(in-package "USER")

;;;; Copyright 1988 The University of Iowa
;;;; Created by Hantao Zhang, 11/10/88.

(defmacro s2n (s) `(parse-integer ,s))
(defmacro s2s (s) `(read-from-string ,s))
(defmacro get-char-type (ch) `(aref $char-type-table (char-code ,ch)))
(defmacro valid-char-code (n) `(and (<= 0 ,n) (<= ,n *char-code-limit*)))
(defmacro is-number-string (s) `(every #'digit-char-p ,s))

(defmacro skip-space (port)
  `(do ()
       ((not (eq $char-type '*space*)))
     (read-one-char ,port)))

(defmacro skip-space-cr (port)
  `(do ()
       ((not (member $char-type '(*space* *eoln*))))
     (read-one-char ,port)))

(defmacro io-char-init () 
  `(when (eq $char-type '*eof*)
     (setq $char-read '*eoln* $char-type '*eoln*)))
(defmacro io-eof (&optional (port piport)) 
  `(progn (skip-space-cr ,port) (eq $char-type '*eof*)))
(defmacro io-eoln (&optional (port piport)) 
  `(progn (skip-space ,port) (member $char-type '(*eoln* *eof*))))

;;---------------------
;; Functions on Buffer
;;---------------------

(defun make-buffer (port &aux buffer)
  ; A token buffer is a list of the form
  ;              (port token-id token-type)
  ; port is a port that it is associated with.
  ; token-id is the text of the token (undefined for the "eof" token) 
  ; token-type is the type of the token, as follows:
  ;           *eoln* -- End of line
  ;           *eof* -- End of File
  ;           ( ) , -- The corresponding punctuation mark
  ;           *if* -- the condition prefix
  ;           *==* -- the equation infix
  ;           function -- An operator
  ;	      constant -- A number
  ;           variable -- A variable
  ;           logical -- either "and", "or", "=", "->", "equ", "all", 
  ;              "not", "exist", "true", or "false".
  ; Usage:
  ;  (make-buffer piport) to read from the terminal
  ;  (make-buffer (infile filename)) to read from the file named filename.
  (io-char-init)
  (skip-space port)
  (setq buffer (list port nil nil))
  (next-token buffer) 
  buffer)

; Macros to access the fields of a token-buffer.
(defmacro token-port (buffer) `(car ,buffer))
(defmacro token-type (buffer) `(cadr ,buffer))
(defmacro token-id (buffer) `(caddr ,buffer))
(defmacro token-eoln (buffer) 
  ; Skip "eoln"s at the beginning of the buffer and return the next token.
  `(do ((peek (token-id ,buffer) (token-id ,buffer)))
       ((neq peek '*eoln*) peek) 
      (next-token ,buffer)))

(defun next-token (buffer &rest expected-type &aux next)
  ; Move to the next token of a token-port.  The value returned
  ; is the current token of the buffer BEFORE next-token was called.
  ; If the expected-type argument is supplied then we check that the 
  ; current token has the given type.  If it doesn't, we issue a type error.

  (when (and expected-type
	     (not (member0 (token-type buffer) expected-type)))
    (if (not (member0 (token-type buffer) expected-type))
	(expected buffer expected-type)))

  (prog1
      (token-id buffer)
    (when (neq (token-id buffer) '*eof*) 
      (skip-space (token-port buffer))
      (setq next (read-sym-real (token-port buffer)))
      (setf (token-type buffer)
	      (cond 
		((member next '(*eof* *eoln* |(| |)| |,| |[|))
		 next)
		;;((equal next '|]|) (setq next '*eof*))
		((equal next ":=") (setq next '*>=*))
		((equal next "if") (setq next '*if*))
		((equal next "==") (setq next '*==*))
		((equal next "!=") (setq next '*!=*))
		((equal next "===") (setq next '*==*))
		((equal next "--->") (setq next '*--->*))
		((equal next "->") (setq next *->*) 'logical)
		((equal next "&")   (setq next *and*) 'logical)
		((equal next "xor") (setq next *xor*) 'logical)
		((not (stringp next)) ;; ignore a bad token
		 nil)
		((is-valid-var next) 
		 (setq next (get-var-id next))
		 'variable)
		(next
		 (setq next (get-new-op-id next))
		 (if (is-bool-op next)
		     'logical
		     'function))
		(t (expected buffer '("a valid symbol")))))
	(setf (token-id buffer) next)
	)))

(defmacro read-sym-string (&optional (port piport))
  ; return a string
  `(read-sym-real ,port t))

(defun read-sym-real (port &optional string &aux (p 0))
  ;;(princ "$char-type: ") (princ $char-type)
  ;;(princ "   $char-read: ") (princ $char-read) (terpri)

  (case $char-type
    (*eof* (if string "" '*eof*))
    (alpha (do ((new 'alpha))
	       ((not (memq new '(alpha num))) (return))
	     (setf (aref $char-buffer p) $char-read)
	     (read-one-char port)
	     (setq new $char-type)
	     (incf p))
	   (subseq $char-buffer 0 p))
    (num (do ((new 'num))
	     ((not (eq new 'num)) (return))
	   (setf (aref $char-buffer p) $char-read)
	   (read-one-char port)
	   (setq new $char-type)
	   (incf p))
	 (subseq $char-buffer 0 p))
    (biop (do ((new 'biop))
	      ((not (eq new 'biop)) (return))
	    (setf (aref $char-buffer p) $char-read)
	    (read-one-char port)
	    (setq new $char-type)
	    (incf p))
	  (subseq $char-buffer 0 p))
    (t (prog1 (if string (string $char-read) $char-type)
	 (read-one-char port)))))

(defun read-string (port &aux res)
  ; skip the initial spaces in a port read a string.
  (io-char-init) 
  (skip-space-cr port)
  (setq res (read-sym-string port))
  (until (memq $char-type '(*space* *eoln* *eof* |(| |)| |[| |]| |,|))
	 (setq res (uconcat res (read-sym-string port))))
  res)

(defun io-skip-line (port)
  (until (member $char-type '(*eoln* *eof*)) (read-one-char port))
  (skip-space-cr port))

(defun print-chars (n port)
  (dotimes (i n)
    (if (characterp $char-read) 
	(write-char $char-read) 
	(return (close port)))
    (read-one-char port)))

(defun help-file (string-list)
  ; Displays string-list and prompts for more after 20 lines.
  ; If the user hits [return] or [space][return]
  ; then the display continues; otherwise, returns.  Returns NIL.
  (sloop for line = 0 then (add1 line)
	as xa in string-list do
    (princ xa) (terpri)
    (if* (eq line 20) then
	(princ "--More--")
	(setq xa (read-one-char piport))
	(cond
	  ((eq xa '*space*) (setq line 0))
	  ((eq xa '*eoln*)  (setq line 19))
	  ((member xa (list #\q #\Q)) (return nil))
	  (t (setq line 0)))
	(terpri))))

(defmacro read-char-aux (file)
  ;; read a char or a symbol from the file and take special case to delimiters.
  `(let ()
     (setq $char-read (read-char ,file nil *eof-list*))
     (if (or (eq $char-read *eof-list*) (eq $char-read #\]))
	 (setq $char-type '*eof*)
       (setq $char-type (get-char-type $char-read)))
     ))

(defun read-one-char (file)
  ;; read a char or a symbol from the file and take special case to delimiters.
  ;; Skip comments leading by ";".
  (read-char-aux file)
  (while (eq $char-type '|;|) (skip-one-line file) (read-char-aux file))
  $char-read)

(defun skip-one-line (port &aux print (tryprint t))
  (until (or (eq $char-type '*eoln*)
	     (eq $char-read *eof-list*))
	 (read-char-aux port)
	 (if print
	     (if (characterp $char-read) (write-char $char-read))
	   (when tryprint
		 (when (eq $char-read #\>)
		       (princ ";;;>") (setq print t))
		 (if (neq $char-read #\;) (setq tryprint nil))))
	 )
  )

(defmacro set-char-type-table (ch val)
  `(setf (aref $char-type-table (char-code ,ch)) ,val))

(defun init-char-type-table ()
   ; 0 - 9: num
   ; A - Z, a - z, ., -: alpha
   ; {+ - # $ % & * + - / :, < > = A \ |}: biop
   ; special control symbols: nil
   ; some symbols translate as symbol/single character sym.
  (do ((i 0 (1+ i))) ((= i 192)) (setf (aref $char-type-table i) nil))
  (do ((i 48 (1+ i))) ((= i 58)) (setf (aref $char-type-table i) 'num))
           
  (do ((i 65 (1+ i))) ((= i 91)) (setf (aref $char-type-table i) 'alpha))
  (do ((i 97 (1+ i))) ((= i 123)) (setf (aref $char-type-table i) 'alpha))
  (set-char-type-table #\. 'alpha) 
  (set-char-type-table #\_ 'alpha) 

  (dolist
   (i (list #\~ #\# #\$ #\% #\& #\* #\+ #\- #\@ #\! #\/ #\: #\< #\> #\= #\|))
   (set-char-type-table i 'biop))

  (set-char-type-table #\Space '*space*)
  (set-char-type-table #\Tab '*space*)

  (set-char-type-table #\Linefeed '*eoln*)
  (set-char-type-table #\Page '*eoln*)
  (set-char-type-table #\Return '*eoln*)

  (set-char-type-table #\( '|"|) 
  (set-char-type-table #\( '|(|) 
  (set-char-type-table #\) '|)|)
  (set-char-type-table #\, '|,|)
  (set-char-type-table #\; '|;|)
  (set-char-type-table #\[ '|[|) 
  (set-char-type-table #\] '|]|)
  (set-char-type-table #\{ '|{|)
  (set-char-type-table #\} '|}|)
)  

;;---------------------
;; Functions on Equations, Type Declarations and Terms Parsing.
;;---------------------

; Use throw to signal a syntax error.
(defmacro io-error (&optional mes)
  `(progn (when ,mes (princ ,mes) (terpri))
	  (throw 'input 'error)))

(defun get-equation (buffer)
  ; Read an equation, according to the production:
  ; <equation> ::= <term> | <equality> | <equality> if <term>
  ;              | <term> if <term>   
  (if (eq $condi 'c) 
      (get-clause buffer) ; >>>>>>>> 1/7/89
      (let ((first (get-term buffer))
	    (source (list 'user (incf $nusereqn)))
	    right)
	(when first
	  (case (token-id buffer)
	    ((*eoln* *eof*) (ass2eqn first source t))
	    (*if*
	     (next-token buffer)
	     (if $condi (setq right *trueterm*))
	     (make-eqn first right (get-term buffer) source 'input))
	    (*==* (get-eqn-rhs first source 'input buffer))
	    (*!=* (setq first (get-eqn-rhs first source 'oneway buffer))
		  (change-lhs-rhs first
				  (list *=* (lhs first) (rhs first))
				  *falseterm*))
	    (*--->* (get-eqn-rhs first source 'oneway buffer))
	    (*===* (setf (car source) 'sos)
		   (get-eqn-rhs first source 'oneway buffer))
	    (t (expected buffer '(end-of-line ==))))))))

(defun get-clause (buffer)
  ; <clause> ::= <literal> | <literal> or <listeral> ... | <equation>
  (let ((first (get-term buffer nil 'literal)) 
	(source (list 'user (incf $nusereqn)))
	right)
    (case (token-id buffer)
      ((*eoln* *eof*) 
       (if (eq (op-of first) *not*)
	   (setq right *falseterm*
		 first (first-arg first))
	   (setq right *trueterm*))
       (make-eqn first right nil source 'oneway))
      (*if*
       (next-token buffer)
       (if (eq (op-of first) *not*)
	   (setq right *falseterm*
		 first (first-arg first))
	   (setq right *trueterm*))
       (make-eqn first right (get-term buffer) source 'oneway))
      (*==* (get-eqn-rhs first source 'input buffer))
      (*--->* (get-eqn-rhs first source 'oneway buffer))
      (*===* 
       (setf (car source) 'sos)
       (get-eqn-rhs first source 'oneway buffer))
      (t (unless (equal (token-id buffer) *or*)
	   (expected buffer '(end-of-line ==)))
	 (next-token buffer)
	 (if (eq (op-of first) *not*)
	     (setq right *falseterm*
		   first (first-arg first))
	     (setq right *trueterm*))
	 (make-eqn first right (condi-from-clause buffer) source 'input))
      )))

(defun condi-from-clause (buffer &aux next)
  ; read a list of literals and negate each of them, then AND them.
  (setq next (negate-literal (get-term buffer nil 'literal)))
  (if (equal (token-id buffer) *or*)
      (progn (next-token buffer)
	     (list *and* next (condi-from-clause buffer)))
      (if (member (token-id buffer) `(*eoln* *eof*))
	  next
	  (expected buffer '(or end-of-line)))))

(defun negate-literal (term)
  (if (or (variablep term) (neq (op-of term) *not*))
      (list *not* term)
      (first-arg term)))

(defun get-eqn-rhs (lhs source oneway buffer)
   ; <rhs> ::= <term> | <term> if <term> 
   ; ( <rhs> stands for right-hand side.)
  (next-token buffer)
  (let ((right (get-term buffer)) condi)
    (case (token-id buffer)
      ((*eoln* *eof*) 
       (make-eqn lhs right nil source oneway))
      (*if*
       (next-token buffer) 
       (setq condi (get-term buffer))
       (make-eqn lhs right condi source oneway))
      (t (expected buffer '(end-of-line if))))))

(defun get-term (buffer &optional low-ops clause)
  ; <term> ::= <item> | <item> <bi-operator> <term> <bi-operator> <term> ...
  ;; (token-eoln buffer) ; skip eoln in buffer.
  (let ((first-part (get-item buffer)) biop)
     (case (token-type buffer) 
        ((|,| |)| *eoln* *eof* *>=* *!=* *==* *--->* *if*) first-part)
	(logical
	  (sloop while t do
		 (setq biop (token-id buffer))
		 (if* (or (member biop low-ops)
			  (and clause (eq biop *or*)))
		      then (return first-part)
		      elseif (not (equal (get-arity biop) 2))
		      then (expected buffer '(")" "a binary function"))
		      else 
		      (next-token buffer)
		      (token-eoln buffer) ; skip eoln in buffer.
		      (setq first-part
			    (list biop
				  first-part
				  (get-term buffer (get-low-ops biop))))
		      (if (neq (token-type buffer) 'logical)
			  (return first-part)))))
	(function
	 (setq biop (next-token buffer))
	 (set-infix biop)
	 (token-eoln buffer) ; skip eoln in buffer.
	 (list biop first-part (get-term buffer low-ops)))
	(t (expected buffer '(")" "binary operator"))))))

(defun get-item (buffer &aux op)
  ; <item> ::= <variable> | <constant> | (<term>) 
  ;            | <unary-function> <term>
  ;            | <function> <term-args>
  ;            | all <varlist> <assertion-item> 
  ;            | exist <varlist> <assertion-item> 
  ;            | not <assertion-item> 
  ;            | true | false 
  (case (token-type buffer) 
    (*eof* nil)
    (|(| (next-token buffer)
	 (prog1 (get-term buffer)
	   (next-token buffer '|)|)))
    (logical 
     (setq op (next-token buffer))
     (cond
       ((member op *exist*all*)
	(fixup-quantified-formula 
	  op
	  (get-varlist buffer) 
	  (get-term buffer (get-low-ops op))))
       ((eq op *not*) (make-term op (ncons (get-item buffer))))
       ((eq op *true*) *trueterm*)
       ((eq op *false*) *falseterm*)))
    (variable (next-token buffer))
    (constant (make-term (next-token buffer) nil))
    (function (get-term-args (next-token buffer) buffer))
    (t (expected buffer '("a function symbol" "a variable")))))

(defun get-varlist (buffer)
  ;; <varlist> ::= ( <variable> <comma-varlist> ) | <variable>
  ;; <comma-varlist> ::= <nothing> | , <variable> <comma-varlist>
  (if* (equal (token-id buffer) '|(|) 
       then
       (next-token buffer)
       (sloop with varlist = (list (next-token buffer 'variable))
	      do (if* (equal (token-id buffer) '|)|) then
		   (next-token buffer)
		   (return (nreverse varlist))
		   else
		   (next-token buffer '|,|)
		   (push (next-token buffer 'variable) varlist)))
       else (list (next-token buffer 'variable))))

(defun get-term-args (func buffer)
  ; <term-args> ::= <nothing> | ( <term> <comma-args> )
  ; <comma-args> ::= <nothing> | , <term> <comma-args>
  (if* (equal (token-id buffer) '|(|) then
       (next-token buffer)
       (setq func (make-term func
			     (sloop while (not (equal (token-id buffer) '|)|)) 
				    collect (get-term buffer)
				    do (if* (equal (token-id buffer) '|,|) 
					    then (next-token buffer)
					    elseif (nequal (token-id buffer) '|)|) 
					    then (expected buffer '(|)| |,|))))))
       (next-token buffer)
       func
       else 
       (make-term func nil)))

(defun get-low-ops (op)
  ; return the bi-operators that are less than "op".
  (cond
    ((eq op *and*) (list *->* *equ* *or* *xor*))
    ((member op *exist*all*) (list *equ* *or* *xor*))
    ((eq op *->*)  (list *equ* *or* *xor*))
    ((eq op *equ*) (list *or* *xor*))
    (t nil)))

;;-----------------------------------
;; Functions on Syntax Error Checking
;;-----------------------------------

(defun eqn-syntax-check (eqn)
  ; Check that predicates and functions were used in the right places and 
  ; that functions were called with the same number of arguments 
  ; everywhere.  If an error happens, we throw. If no error happens, we 
  ; return eqn.
  (when (and eqn
	     (catch 'input
		(progn
		  (if (is-condi-eqn eqn) (expecting-predicates (ctx eqn)))
		  (cond ((is-assertion eqn) (expecting-predicates (lhs eqn)))
			((is-prop-eqn eqn)
			 (expecting-predicates (lhs eqn))
			 (expecting-predicates (rhs eqn)))
			(t (expecting-functions (lhs eqn))
			   (expecting-functions (rhs eqn)))))))
    (write-eqn eqn) (terpri) (io-error))
  eqn)

(defun expecting-functions (term)
  ; Check the top level of term is a function symbol, and that it has the 
  ; right arity, and that all of its arguments satisfy the same criterion.
  (if* (nonvarp term) then
       (check-arity term)
       (if* (or (eq (op-of term) *=*) (eq (op-of term) *eq*))
	    then
	    (if (and (multi-typed)
		     (not (type-cohere 
			    (get-term-type (first-arg term))
			    (get-term-type (second-arg term)))))
		(bad-typed term))
	    (sloop for ar in (args-of term) do 
		   (expecting-functions ar))
	    elseif (member (op-of term) *exist*all*)
	    then (expecting-predicates (second-arg term))
	    elseif (is-bool-op (op-of term)) 
	    then (sloop for xa in (args-of term) do (expecting-predicates xa))
	    elseif (multi-typed)
	    then (sloop for ty in (get-codomain-types (op-of term)) 
			for ar in (args-of term) 
			if (nonvarp ar) 
			do
			(if (type-cohere ty (get-op-type (op-of ar)))
			    (if (eq ty 'bool) 
				(expecting-predicates ar)
				(expecting-functions ar))
			    (bad-typed term)))
	    else
	    (sloop for ar in (args-of term) do 
		   (expecting-functions ar))
	    )))

(defun expecting-predicates (term) 
  ; Check the top level of term is a boolean expression, and that it has 
  ; the right arity, and that all of its arguments satisfy the same criterion.
  (if* (variablep term) 
       then 
       (format t  "WARNING: Variable used as predicate: ~s~%" (var-name term))
       (if (not $condi) (io-error))
      else
      (ensure-predicate (op-of term))
      (expecting-functions term)))

(defun bad-typed (term)
  (write-term term)
  (princ ": bad-typed term in the equation:")
  (terpri) 
  (io-error))

(defun input-type-check (term name)
  (if (well-typed-term term) 
      t 
      (progn 
	(format t "The ~s of the equation is not well-typed.~%" name)
	nil)))

(defun ensure-predicate (pred)
  ; Ensure that the given operator is a predicate.
  (when (not (predicatep pred))
	(format t "WARNING: ~s is now considered as a predicate.~%" 
		(op-name pred))
	(set-predicate pred)))

(defun fixup-quantified-formula (quantifier vars formula)
  ; Given a list of variables, a quantifier, and a formula, return our 
  ; internal representation for that formula quantified with all of the 
  ; variables.  Our internal representation limits us to one variable 
  ; per quantifier, so we will usually produce several quantifiers.
  (if* (null vars) then formula
       elseif (not (memq (car vars) (free-vars formula))) then formula
       else  (make-term quantifier
			(list (car vars) 
			      (fixup-quantified-formula quantifier
							(cdr vars) formula)))))

(defun check-arity (term)
  ;; In a function or predicate expression, ensure that we have the right 
  ;; number of arguments.
  (if (has-arity (op-of term)) 
      (unless (equal (get-arity (op-of term)) (length (args-of term)))
	(princ "In the term ") (write-term term)
	(format t ", the operator ~s used to have ~d arguments~%    but you gave it ~d.~%"
		(op-name (op-of term)) (get-arity (op-of term))
		(length (args-of term)))
	(io-error))
      (set-arity (op-of term) (length (args-of term))))
  term)

(defun expected (buffer expectedlist &optional flag)
  ; Tell the user that he made a boo boo.
  (terpri)
  (if* flag then (princ "Expected one of the following: ")
      else
      (princ "Found '") (princ (token-id buffer))
      (princ "' but expected one of the following: "))
  (sloop for xa in (cdr expectedlist) do (princ xa) (princ ", "))
  (princ (car expectedlist)) (terpri)
  
  (if* (equal (token-port buffer) piport) 
       then (io-skip-line (token-port buffer))
       elseif (nequal (token-eoln buffer) '*eof*)
       then 
       (terpri) (princ "Following text has not been parsed.") (terpri)
       (princ "  ... ... ")
       (print-chars 100 (token-port buffer))
       (princ "  ... ... ") (terpri)
       ;(close (token-port buffer))
       )
  (io-error))

(defun set-up-arity2 (op arity buffer)
  ; check whther "op" has the consistent "arity" as before.
  (if* (get-arity2 op) then
    (if* (nequal (get-arity2 op) arity)
	then (expect-arity op arity buffer))
    elseif (get-arity op) 
    then (if* (equal (length (cdr arity)) (get-arity op))
		then (set-arity2 op arity)
		else (expect-arity12 op arity buffer))
    else (set-arity op (length (cdr arity)))
	 (set-arity2 op arity)
	 (if (eq 'bool (car arity)) (set-predicate op))))

(defun expect-arity12 (op arity buffer &aux old-arity)
  ; Tell the user that he made an error.
  ; The arity of op is not consistent with the old one.
  (format t "The operator has the arity of (length) ~d.~% " (get-arity op))
  (setq old-arity (get-arity2 op))
  (set-arity2 op arity)
  (princ "         but now:")
  (display-one-arity2 op)
  (set-arity2 op old-arity)
  (expected buffer '("consistent arity declaration") t))

(defun expect-arity21 (op arity buffer)
  ; Tell the user that he made an error.
  (princ "The operator has:")
  (display-one-arity2 op)
  (format t "    but now has the arity of length ~d" arity)
  (expected buffer '("consistent arity declaration") t))

(defun expect-arity (op arity buffer &aux old-arity)
  ; op is a symbol.
  ; Tell the user that he made an error.
  (princ "The operator has:")
  (display-one-arity2 op)
  (setq old-arity (get-arity2 op))
  (set-arity2 op arity)
  (princ "         but now:")
  (display-one-arity2 op)
  (set-arity2 op old-arity)
  (expected buffer '("consistent arity declaration") t))


(defun read-arity (buffer &aux op)
  ; <arity-specification> ::= [<op> : <type1>, <type2>, ..., <typen> -> <type>]
  ;			   |  [<var> : <type>]
  ;			   |  [<type1> < <type2>]
  ; where <type1>, ..., <typen> are codomain types and <type> is domain type.
  (next-token buffer)
  (setq op (token-id buffer))
  (unless (stringp op) (expected buffer '("an operator")))
  (setq op (get-new-op-id op))

  (if* (equal (op-name (token-id buffer)) ":")
	then (read-op-declaration op buffer)
	elseif (equal (op-name (token-id buffer)) "<")
	then (read-type-relation op buffer)
	else (expected buffer '(":" "<"))))

(defun read-op-declaration (op buffer &aux types done)
  (while (member0 (token-id buffer) '("->" ":")) (next-token buffer))
  (while (not done)
    (push (s2s (next-token buffer)) types)
    (case (token-id buffer)
      (*eof* (clean-right-bracket buffer) (setq done t))
      (*->* (next-token buffer))
      (|,| (next-token buffer))
      (*eoln* (expected buffer '(])))))
  (dolist (ar types)
    (unless (assoc ar $type-rela) (push (ncons ar) $type-rela)))
  (setq types (cons (car types) (nreverse (cdr types))))
  (set-up-arity2 op types buffer))

(defun read-type-relation (ty1 buffer &aux ty2)
  (setq ty1 (s2s ty1))
  (next-token buffer)
  (unless (and (is-exist-type-name ty1) 
	       (is-exist-type-name (setq ty2 (s2s (token-id buffer)))))
    	 (terpri)
	 (expected buffer '("a valid type name")))

  (next-token buffer)
  (unless (equal (token-id buffer) '*eof*) (expected buffer '(])))
  (clean-right-bracket buffer)
  (add-sugg-type ty1 ty2)
  (format t "Type relation, ~s is included in ~s, is added.~%" ty1 ty2))

(defun clean-right-bracket (buffer)
  ; replace the current token by *eoln*. 
  ; Called when the current token is *eof*.
  (setf (token-id buffer) '*eoln*)
  (setf (token-type buffer) '*eoln*))

(defun err (a &optional b)
  (princ a)
  (when b (princ " ===> ") (princ b))
  (terpri))

(defmacro if-well-typed-term (term &body body)
  (if *no-type-checking*
      `(when (well-typed-term ,term) ,@body)
    `(let () ,@body)
    ))

(defmacro if-well-typed-eqn (eqn &body body)
  (if *no-type-checking*
      `(when (well-typed-eqn ,eqn) ,@body)
    `(let () ,@body)
    ))

(defmacro multi-typed () `(cdr $type-rela))

(defmacro well-typed-term (term)
  ; Return T iff "term" is well-typed.
  ; A term "t" is well-typed if
  ;    1. "t" is a variable;
  ; or 2. "t" is form of f(t1, t2, ..., tn), and
  ;       t1, t2, .., tn are well-typed, and
  ;       f is signature of [type1, type2, ..., typen -> type]
  ;	  and typei is included in the type of ti, for i in [1..n].
  `(or (not (multi-typed))
       (if* (null ,term) then t
	    elseif (variablep ,term) then t 
	    else 
	    (well-typed2 ,term))))

(defun well-typed2 (term)
  (if* (memq (op-of term) '(= eq))
   then (sloop with ty = (get-term-type (first-arg term))
	      for xa in (args-of term) 
	      always (if* (variablep xa) 
			  t
			  (and (type-cohere ty (get-term-type xa)) 
			       (well-typed2 xa))))
   elseif (is-bool-op (op-of term)) 
   then (sloop for arg in (args-of term) always (well-typed-term arg))
   elseif (is-type-predicate (op-of term)) 
   then (sloop for arg in (args-of term) always (well-typed-term arg))
   elseif (get-arity2 (op-of term))
   then
   (sloop for ty in (get-codomain-types (op-of term)) 
	 for ar in (args-of term)
	 always (if* (variablep ar) 
		     t
		     (and (type-cohere ty (get-op-type (op-of ar)))
			  (well-typed2 ar))))
   else (sloop for ar in (args-of term) 
	      always (or (variablep ar) (well-typed2 ar)))))

(defun well-typed3 (term)
  (if* (get-arity2 (op-of term)) then
      (sloop for ty in (get-codomain-types (op-of term)) 
	    for ar in (args-of term)
	    always (if* (variablep ar) 
		       t
		       (type-cohere ty (get-op-type (op-of ar)))))
      else t))


(defun complete-well-typed (term)
  ; Return T iff "term" is well-typed.
  ; A term "t" is well-typed if
  ;    1. "t" is a variable;
  ; or 2. "t" is form of f(t1, t2, ..., tn), and
  ;       t1, t2, .., tn are well-typed, and
  ;       f is signature of [type1, type2, ..., typen -> type]
  ;	  and typei is included in the type of ti, for i in [1..n].
  (if* (null term) then t
      elseif (variablep term) then t 
      elseif (eq (op-of term) *=*)
      then (sloop with ty = (get-term-type (first-arg term))
		 for xa in (args-of term) 
		 always (if (variablep xa) t
			    (and (type-cohere ty (get-term-type xa)) 
				 (complete-well-typed xa))))
      elseif (is-bool-op (op-of term)) 
      then (sloop for arg in (args-of term) always (complete-well-typed arg))
      elseif (get-arity2 (op-of term))
      then
      (sloop for ty in (get-codomain-types (op-of term)) 
	    for ar in (args-of term)
	    always (if (variablep ar) 
		       t
		     (and (type-cohere ty 
				       (get-op-type (op-of ar)))
			  (complete-well-typed ar))))
      else (sloop for ar in (args-of term) 
		 always (or (variablep ar) (complete-well-typed ar)))))

(defun get-term-type (term)
  (if* (variablep term) then 'univ else (get-op-type (op-of term))))

#|
(defun check-badtyped (term type)
  ; "term" and "type" come from "badtyped(term, type)".
  (if* (eq type 'univ) then nil
     elseif (variablep term) 
     then (if* (memq term $induc-vars) 
	      then (ncons *falseterm*)
	      else `((badtyped ,term (,type))))
     elseif (type-cohere (get-op-type (op-of term)) type)
     then (ncons *falseterm*)))

(defun check-typed (term type)
  ; "term" and "type" come from "typed(term, type)".
  (if* (eq type 'univ) then nil
     elseif (variablep term) 
     then (if* (not (memq term $induc-vars)) then `((typed ,term (,type))))
     elseif (type-cohere (get-op-type (op-of term)) type)
     then (sloop for ty in (get-codomain-types (op-of term)) 
		for ar in (args-of term) 
		nconc (check-typed ar ty))
     else (ncons *falseterm*)))
|#

(defmacro get-op-type (i)
  ; The default types are:
  ;    1. variables are type of "univ";
  ;    2. numbers are type of "num";
  ;    3. the predicates are type of "bool".
  ;    3. If no type is given to an operator, then "univ".
  `(if (get-arity2 ,i) (car (get-arity2 ,i)) 
       (if (predicatep ,i) '|bool| '|univ|)))

(defmacro get-codomain-types (i)
  ; If no type is given, then suppose "op" has 
  ;      (univ, univ, ..., univ).
  ;; NOT EFFICIENT !!!!
  `(if (get-arity2 ,i) (cdr (get-arity2 ,i)) 
       (sloop for j from 1 to (get-arity ,i) collect '|univ|)))

(defun ext-type-relation ()
  ; Sets the type relation between two types given by the user.
  ; $type-rela is updated.
  (if* (io-eoln $in-port) then
      (princ "Type type names in including order.") (terpri)
      (princ "  (eg. 'type1 type2 type3' to set type1 C type2 C type2 ) ")
      (terpri) (princ "--> "))
  (let ((ty1 (read-atom 'noend)) tys2)
    (setq tys2 (progn (if* (io-eoln $in-port) then
		        (princ (uconcat ty1 " is included in type name ? ")))
	              (read-args)))
    (if* (sloop for ty2 in (cons ty1 tys2) always 
	     (if* (is-exist-type-name ty2) then t else
	       (princ (uconcat ty2 ": unknown type name, relation not set."))
	       (terpri) nil))
 	then (sloop for ty2 in tys2 do
	       (add-sugg-type ty1 ty2)
	       (princ (uconcat "Type relation, " ty1 " C " ty2 ", is added."))
	       (terpri)
               (setq ty1 ty2)))))

(defun add-sugg-type (ty1 ty2)
  ; Adds the relation ty1 C ty2 and makes sure the global
  ; varaible $type-rela is updated correctly.
  (cond ((null $type-rela) 
         (setq $type-rela (ncons (list ty1 ty2))))
        ((assoc ty1 $type-rela) (add-sugg-type1 ty1 ty2))
	(t (nconc $type-rela (ncons (ncons ty1)))
	   (add-sugg-type1 ty1 ty2))))

(defun add-sugg-type1 (ty1 ty2)
  ; Called by ADD-SUGG-TYPE.
  (sloop for xa in $type-rela do
     (if* (member ty1 xa) then 
	(add-at-end xa ty2)
	(sloop for o2 in (assoc ty2 $type-rela) do (add-at-end xa o2)))))

(defun type-cohere (ty1 ty2)
  ; Checks if TY1 is included in TY2 or vice verca.
  (or (eq ty1 ty2) (is-subtype ty1 ty2) (is-subtype ty2 ty1)))

(defun is-subtype (ty1 ty2)
  (or (eq ty2 'univ) (memq ty1 (assoc ty2 $type-rela))))

(defun get-subtypes (ty1)
  (if* (eq ty1 'univ) 
     then (sloop for xa in $type-rela collect (car xa))
     else (cdr (assoc ty1 $type-rela))))

(defun display-type-arity (ops &optional port)
  (setq ops (sloop for op in ops
		  if (get-arity2 op) collect op))
  (when ops 
    (terpri port)
    (princ "The arities of the operators are:" port) (terpri port)
    (display-arity2 ops port)
    (terpri port)))

(defun display-arity2 (ops &optional port)
   (sloop for op in ops do (display-one-arity2 op port)))

(defun display-one-arity2 (op &optional port &aux types)
  (when (get-arity2 op) 
    (princ (uconcat "      [" (op-name op) " :") port)
    (when (setq types (get-codomain-types op)) 
      (princ " " port) (princ (car types) port)
      (sloop for ty in (cdr types) do (princ ", " port) (princ ty port)))
    (princ " -> " port) (princ (get-op-type op) port)
    (princ " ]" port)
    (terpri port)))

(defun is-exist-type-name (ty2)
 ; return t iff "ty2" is a valid type name.
 ; num, list and univ are pre-defined type names.
 (or (memq ty2 '(num list univ)) (assoc ty2 $type-rela)))

(defun well-typed-eqn (eqn)
  (or (not (multi-typed))
      (and (well-typed-term (lhs eqn))
	   (well-typed-term (rhs eqn)) 
	   (if (ctx eqn)
	       (if (is-premise-set (ctx eqn)) 
		   (sloop for xa in (cdr (ctx eqn)) 
			  always (well-typed-term (car xa)))
		   (well-typed-term (ctx eqn)))
	       t))))

