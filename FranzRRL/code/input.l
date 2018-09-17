;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

;; $log-port: Set up by "log" command. When it is not nil, the port is used 
;;            to registry the correct commands the user fed on the keybord 
;;	      to make log files.
;; $in-port:  Set up by "auto" or "test" commands. When it is not nil, the 
;;            port is used to provide the commands pre-registried by "log" 
;;	      command.
;;  At any time, at least one of the above variables is nil.

(defun read-input (terminal)
   ; Read equations from terminal.
   (let ((l1 (if terminal then (readteqns) else (readfeqns))))
	(if (not $ckb_flag)
	    ; >>>>>>>>> 1/7/89
	    (setq $ckb_flag (loop for eqn in l1 thereis (is-condi-eqn eqn))))
	(when (and $ckb_flag (null $induc)) 
	  (terpri) (princ "Using Conditional Rewriting Method ...") (terpri)
	  (setq $induc 'c $trace-proof t $prove-method 'c))
	(if (and (not $in-fopc)
		 (loop for eqn in l1 thereis (assertionp eqn))) then
	    (setq $in-fopc t			
		  $trace-proof t)
	    ; initialize flags for first order predicate calculus 
	    ; using the boolean-ring method.
	    (if (not (or $ckb_flag $induc $narrow)) then
		(setq $crit-with-str 'a  
		      $ordering 's
		      $del_rule_str 1
		      $newrule-max 10000)))

	(sys-flag-init)
	(if (and terminal $log-port) then 
	    ; Make log file. Write equations in it.
	    (display-arity2 $newops) ;; >>>>>> 2/28/89
	    (write-eqns l1 $log-port) 
	    (princ "]" $log-port) (terpri $log-port))
	(mapcar 'first-process-eqn l1)))

(defun open-read-file (&optional suffix)
  ; Read in a file name and try to open it to read. Look for the file 
  ; with the default suffix and in the example-directory, too.
  (let (filename port)
   (if (is-empty-line $in-port) then (princ "Type filename: "))
   (setq filename (read-atom 'end))
   (cond  ((setq port
	    (or (car (errset (infile filename) nil))
		(car (errset (infile (uconcat filename "." suffix)) nil))
		(car (errset (infile (uconcat $example-dir filename)) nil))
		(car (errset (infile (uconcat $example-dir
					    filename "." suffix)) nil)))))
	  (t (princ (uconcat "   Error : Couldn't open file: " filename))
	     (terpri)))
      port))

(defun show-grammar ()
  ; Put a description of the new grammar on the screen.
  (loop for xa in '(
   "                      RRL'S    INPUT    SYNTAX "
   " "
   " <arity> ::= [<function> : <type>, <type>, ..., <type> -> <type>]"
   "              |  [<type> < <type>]"
   " <type> ::= Any sequence of alphanumeric characters"
   " <equation> ::= <assertion> == <rightside> |  <assertion> := <rightside>"
   "                | <assertion> ---> <rightside> | <formula>"
   " <rightside> ::= <assertion> | <assertion> if <assertion>"
   " <formula> ::= all <varlist> <formula> | exist <varlist> <formula>"
   "              | (<formula> <connective> <formula>) | not(<formula>) "
   "              | <assertion>"
   " <assertion> ::= (<assertion> <connective> <assertion>) | not(<assertion>)"
   "              | true | false | <atom>"
   " <connective> ::= and | or | xor | -> | equ "
   " <atom> ::= <predicate> <term-args>"
   " <predicate> ::= <function> | = | eq | cond"
   " <term> ::= <item> | <item> <infix-operator> <term>"
   " <item> ::= <variable> | <constant> | <function> <term-args> |(<term>)"
   " <term-args> ::= <nothing> | ( <term> <comma-args> )"
   " <comma-args> ::= <nothing> | , <term> <comma-args>"
   " <varlist> ::= ( <variable> <comma-varlist> ) | <variable>"
   " <comma-varlist> ::= <nothing> | , <variable> <comma-varlist>"
   " <infix-operator> ::= <function>"
   " <constant> ::= A number | <function>"
   " <function> ::= A letter in [a .. t] or in [A .. Z] followed by a sequence"
   "                of alphanumeric  characters or a word of"
   "                {+ - & ^ $ # @ ! | : . =}, except --->, ==, :=, if"
   " <variable> ::= A letter in [u .. z] followed by a sequence of "
   "                alphanumeric characters"
   " <nothing> ::= "
   " "
   " No distinctions are made between lowcase and upcase characters."
   " Formulas are any first-order logic formulas. "
   " Assertions are quantifier-free formulas. "
   " Terms are built from variables and operators."
   " Numbers can only be used as constants."
   " All functions must be used with the same number of arguments."
   " All free variables are considered as universally quantified variables."
   " "
   " Pre-defined precedence: "
   "  {<function>} > {not} > {and} > {->} > {all, exists} > {equ} > {or, xor}"
   " "
   " Note that all infix binary operators associate to the left if no "
   " parentheses or no precedence are given."
   " "
   ) do (princ xa) (terpri)))

(defun readfeqns (&aux port)
  ;; Read in a file name from terminal and then open it to read the equations
  ;; in and return them. 
  (if (setq port (open-read-file "eqn")) then
     (prog1 (read-eqns port) (close port))))

(defun readteqns ()
  ;; Read the equations from $in-port if it is openned by "auto" command.
  ;; Otherwise read equations from the keybord. 
  (princ "Type your equations, enter a ']' when done.") (terpri) 
  (read-eqns $in-port))

(defun read-eqns (&optional in-port)
  ; Returns the list of equations read in from the given port.
  ; The list of equations can be terminated by either an end-of-file,
  ; or "]" symbol.
  (let (eqns l1 l2 (buffer (make-buffer in-port)))
    (setq $newops nil)
    (loop while (nequal (token-eoln buffer) 'eof) do
       (setq l1 (*catch 'error
		    (if (eq (token-text buffer) '|[|) 
			  then (read-arity buffer) nil
			  else (input-check (get-equation buffer)))))
       (cond ((eq l1 'error) (return))
	     (l1 (push l1 eqns))))
    (if eqns then
	(if $newops then
	  (if (loop for op in $newops thereis (get-arity2 op)) then
	    (terpri) (princ "New operators have the arities:") (terpri)
	    (display-arity2 $newops))
          (if (setq l2 (get-constants $newops)) then
		;; Display constant operators to make the user aware 
		;; of variable name problem.
		(terpri) (princ "New constant set is: ")
		(princ (display-ops l2)) (terpri)))
	(if (eq l1 'error) 
	    (princ "Part of equations are succesfully read:")
	  (princ "Equations read in are:"))
	(terpri) (list-equations (setq eqns (nreverse eqns))))
    eqns))

(defun remove-last-letter (p) (implode (butlast (explodec p))))

(defun read-arity (buffer &aux op)
  ; <arity-specification> ::= [<op> : <type1>, <type2>, ..., <typen> -> <type>]
  ;			   |  [<var> : <type>]
  ;			   |  [<type1> < <type2>]
  ; where <type1>, ..., <typen> are codomain types and <type> is domain type.
  (next-token buffer)
  (setq op (token-text buffer))
  (if (or (is-valid-var op) (is-valid-op op))
      then (next-token buffer)
      else (expected buffer '("an operator")))

  (if (and (neq op '|:|) (eq (last-letter op) '|:|))
	then (setq op (remove-last-letter op))
	     (read-op-declaration op buffer)
        elseif (eq (token-text buffer) '|:|)
	then (read-op-declaration op buffer)
	elseif (eq (token-text buffer) '|<|)
	then (read-type-relation op buffer)
	elseif (and (neq op '|<|) (eq (last-letter op) '|<|))
	then (setq op (remove-last-letter op))
	     (read-type-relation op buffer)
	else (expected buffer '(":" "<"))))

(defun read-op-declaration (op buffer &aux arity)
  (loop for xa = (token-text buffer) 
        if (memq xa '(-> |:|)) do (next-token buffer)
	else return nil)
  (loop while t do
	(push (next-token buffer) arity)
	(caseq (token-text buffer)
	    (eof (clean-right-bracket buffer) (return))
	    (|->| (next-token buffer))
	    (|,| (next-token buffer))
	    (eoln (expected buffer '("]")))))
  (loop for ar in arity
	if (not (assoc ar $type-rela)) do (push (ncons ar) $type-rela))
  (setq arity (cons (car arity) (nreverse (cdr arity))))
  (set-up-arity2 op arity buffer))

(defun read-type-relation (ty1 buffer &aux ty2)
  (next-token buffer)
   (if (and (is-exist-type-name ty1) 
	    (is-exist-type-name (setq ty2 (token-text buffer))))
	then (next-token buffer)
	     (if (eq (token-text buffer) 'eof) 
		then (clean-right-bracket buffer)
		     (add-sugg-type ty1 ty2)
		     (princ (uconcat "Type relation, " ty1 
				     " C " ty2 ", is added."))
		     (terpri)
		else (expected buffer '("]")))
	else (expected buffer '("a valid type name"))))

(defun clean-right-bracket (buffer)
   ; replace the current token by "eoln". Called when the current token is "eof".
   (setf (token-text buffer) 'eoln) (setf (token-type buffer) 'eoln))

(defun get-equation (buffer)
  ; Read an equation, according to the production:
  ; <equation> ::= <term> | <equality> | <equality> if <term>
  ;                 | <term> if <term>   
  (if (eq $induc 'c) 
      (get-clause buffer) ; >>>>>>>> 1/7/89
  (let ((first (get-term buffer))
	(source (list 'user (inc $nusereqn)))
         right oneway)
      (caseq (token-text buffer)
           ((eoln eof) 
	    (ass2eqn first source t))
	   (if (next-token buffer)
	       (if $induc then 
		 ;; >>>>>>>>> 1/14/89
		 (if (eq (op-of first) 'not)
		     (setq right '(false)
			   first (first-arg first))
		   (setq right '(true))))
	     (make-eqn first right (get-term buffer) source t))
	   ((== ---> |:=|)
	    (caseq (next-token buffer)
		(---> (setq oneway t))
		(|:=| (setq source (list 'def $nusereqn)))
		(t t))
	    (setq right (get-rhs buffer))
	    (make-eqn first (first right) (cdr right) source oneway))
	   (t (expected buffer '(eof eoln ==)))))))

(defun get-clause (buffer)
  ; <clause> ::= <literal> | <literal> or <listeral> ...
  (let ((first (get-term buffer nil 'literal)) 
	(source (list 'user (inc $nusereqn)))
	oneway right)
      (caseq (token-text buffer)
	   (or (next-token buffer)
	       (if (eq (op-of first) 'not)
		   (setq right '(false)
			 first (first-arg first))
		 (setq right '(true)))
	    (make-eqn first right (condi-from-clause buffer) source t))
           ((eoln eof) 
	    (if (eq (op-of first) 'not)
		(setq right '(false)
		      first (first-arg first))
	      (setq right '(true)))
	    (make-eqn first right nil source t))
	   (if (next-token buffer)
	       (if (eq (op-of first) 'not)
		   (setq right '(false)
			 first (first-arg first))
		 (setq right '(true)))
	     (make-eqn first right (get-term buffer) source t))
	   ((== ---> |:=|)
	    (if (neq '== (next-token buffer)) (setq oneway t))
	    (setq right (get-rhs buffer))
	    (make-eqn first (first right) (cdr right) source oneway))
	   (t (expected buffer '(eof eoln ==))))))

(defun condi-from-clause (buffer &aux next)
  ; read a list of literals and negate each of them, then AND them.
  (setq next (negate-literal (get-term buffer nil 'literal)))
  (caseq (token-text buffer)
	 (or (next-token buffer)
	     (list 'and next (condi-from-clause buffer)))
	 ((eoln eof) next)
	 (t (expected buffer '(or eof eoln)))))

(defun negate-literal (term)
  (if (or (variablep term) (neq (op-of term) 'not))
      (list 'not term)
    (first-arg term)))

(defun get-rhs (buffer)
   ; <rhs> ::= <term> | <term> if <term> 
   ; ( <rhs> stands for right-hand side.)
   (let ((right (get-term buffer)) condi)
      (caseq (token-text buffer)
          ((eoln eof) (ncons right))
          (if (next-token buffer) 
		(setq condi (get-term buffer))
		(cons right condi))
          (t (expected buffer '(eof eoln if))))))

(defun get-term (buffer &optional low-ops literal)
  ; <term> ::= <item> | <item> <bi-operator> <term> <bi-operator> <term> ...
  (token-eoln buffer) ; skip eoln in buffer.
  (let ((first-part (get-item buffer)) biop)
     (caseq (token-type buffer) 
	(keyword
	  (loop while t do
	    (setq biop (token-text buffer))
	    (if (or (memq biop low-ops) (and literal (eq biop 'or)))
		;; >>>>>> 1/7/89
	      then (return first-part)
	      elseif (not (memq biop '(and & or xor -> equ))) 
	      then (expected buffer '(|)| eof eoln and & or -> equ))
	      else (next-token buffer)
	           (setq first-part (list biop first-part
					  (get-term buffer 
						    (get-low-ops biop) 
						    literal)))
		   (if (neq (token-type buffer) 'keyword)
		       then (return first-part)))))
        ((|)| eoln eof |:=| == |,| ---> if) first-part)
	(function (setq biop (next-token buffer))
		  (set-infix biop)
		  (list biop first-part (get-term buffer low-ops literal)))
	(t (expected buffer '(|)| eof eoln bi-operator))))))

(defun get-low-ops (op)
  ; return the bi-operators that are less than "op".
  (caseq op
    ((& and) '(-> equ or xor))
    (|->| '(equ or xor))
    (equ '(or xor))
    (t nil)))

(defun get-item (buffer &aux op)
  ; <item> ::= <variable> | <constant> | (<term>) 
  ;            | <unary-function> <term>
  ;            | <function> <term-args>
  ;            | all <varlist> <assertion-item> 
  ;            | exist <varlist> <assertion-item> 
  ;            | not <assertion-item> "
  ;            | true | false "
  (caseq (token-type buffer) 
     (|(| (next-token buffer)
          (prog1 (get-term buffer)
	         (next-token buffer '|)|)))
     (keyword 
	(caseq (setq op (next-token buffer))
	   ((all exist) (fixup-quantified-formula 
			  op
			  (get-varlist buffer) 
			  (get-term buffer '(equ or xor))))
           (not	(make-term 'not (ncons (get-item buffer))))
	   (true '(true))
	   (false '(false))))
     (variable (next-token buffer))
     (constant (make-term (next-token buffer) nil))
     (function (get-term-args (next-token buffer) buffer))
     (t (expected buffer '("a function symbol" "a variable")))))

(defun get-varlist (buffer)
  ; <varlist> ::= ( <variable> <comma-varlist> ) | <variable>
  ; <comma-varlist> ::= <nothing> | , <variable> <comma-varlist>
  (if (equal (token-text buffer) '|(|) then
      (next-token buffer)
      (loop with varlist = (list (next-token buffer 'variable))
	    do (if (equal (token-text buffer) '|)|) then
		   (next-token buffer '|)|)
		   (return (nreverse varlist))
		   else
		   (next-token buffer '|,| '|)|)
		   (push (next-token buffer 'variable) varlist)))
      else (list (next-token buffer 'variable))))

(defun get-term-args (func buffer)
  ; <term-args> ::= <nothing> | ( <term> <comma-args> )
  ;                 <term>
  ; <comma-args> ::= <nothing> | , <term> <comma-args>
  ; Return a term.
  (if (eq (token-text buffer) '|(|) then
      (next-token buffer)
      (setq func (make-term func
			    (loop while (not (equal (token-text buffer) '|)|)) 
				  collect (get-term buffer)
				  do (if (equal (token-text buffer) '|,|) 
					 then (next-token buffer)
					 elseif (nequal (token-text buffer) '|)|) 
					 then (expected buffer '(|)| |,|))))))
      (next-token buffer)
      func
      elseif (and (infix-letter (getcharn func 1))
		  (memq (token-type buffer) '(variable function)))
      then (list func (get-term buffer))
      else (make-term func nil)))

(defun read-t-term ()
  (if (is-empty-line $in-port) then (terpri)
          (princ "Input a term in the form T  or T if C :") (terpri))
   (let (term (buffer (make-buffer $in-port)))
     (if (not (eq (token-eoln buffer) 'eof)) then
	  (setq term (*catch 'error (get-rhs buffer))))
     (if (and term (nequal term 'error)) then
       (setq term (first term))
       (terpri) (princ "The term read in is:") (terpri) 
      (princ "  ") (write-term term) (terpri) 
      (if $log-port then (write-term term $log-port) (terpri $log-port))
      (if $in-port then (write-term term) (terpri))
      term)))

;;---------------------
;; Functions on Buffer
;;---------------------

(defun make-buffer (port)
  ; A token buffer is a list of the form
  ;              (port token-text token-type)
  ; port is a port that it is associated with.
  ; token-text is the text of the token (undefined for the "eof" token) 
  ; token-type is the type of the token, as follows:
  ;           eoln -- End of line
  ;           eof -- End of File
  ;           ( ) , -- The corresponding punctuation mark
  ;           if -- the condition prefix
  ;           == -- the equation infix
  ;           function -- An operator
  ;	      constant -- A number
  ;           variable -- A variable
  ;           keyword -- either "and", "or", "=", "->", "equ", "all", 
  ;              "not", "exist", "true", or "false".
  ; Do something similar to the infile function for token-ports.
  ; Usage:
  ;  (make-buffer piport) to read from the terminal
  ;  (make-buffer (infile filename)) to read from the file named filename.
  (let ((buffer (list port nil nil))) (next-token buffer)  buffer))

(defun next-token (buffer &rest expected-type)
  ; Move to the next token of a token-port.  The value returned
  ; is the current token of the buffer BEFORE next-token was called.
  ; If the expected-type argument is supplied then we check that the 
  ; current token has the given type.  If it doesn't, we do a syntax error.
  (if (and expected-type (not (memq (token-type buffer) expected-type))) 
	then (if (eq (token-text buffer) 'eoln) then (token-eoln buffer))
	     (if (not (memq (token-type buffer) expected-type))
		 then (expected buffer expected-type)))
  (prog1
     (token-text buffer)
     (if (neq (token-text buffer) 'eof) then
       (let (next)	 
	 (setq next (get-atom (token-port buffer)))
	 (setf (token-type buffer)
	       (caseq next
		  (|:=| next)
 		  ((eof eoln if == ---> |(| |)| |,|) next)
		  ((and or -> equ all exist not true false xor) 'keyword)
		  (& (setq next 'and) 'keyword)
		  (t (cond ((numberp next) 'constant)
			   ((is-valid-var next) 'variable)
			   ((is-valid-op next) 'function)
			   (t (setf (token-text buffer) next)
			      (expected buffer '("a valid symbol")))))))
	 #+lispm
	 (if (equal (token-type buffer) 'keyword) then
 	 	(setq next (intern (string-upcase next))))
         (setf (token-text buffer) next)))))

(defun token-eoln (buffer)
  ; Skip "eoln"s at the beginning of the buffer and return the next token.
  (do ((peek (token-text buffer) (token-text buffer)))
      ((neq peek 'eoln) peek) 
      (next-token buffer)))

(defun get-atom (&optional port)
  ; Read an atom from the given port and give it a uniform name.
  (caseq (tyipeek-space port)
    (#/; (clean-line port) 'eoln)
    (#/] (my-tyi port) 'eof) 
    (-1 'eof)
    ((
#+lispm 148 
#-lispm #\newline 
#\return) (my-tyi port) 'eoln) 
	  ; 148 is #<end>. #\newline and #\return have different values in franz lisp.
	  (t (get-atom2 port))))

(defun get-atom2 (port)
  ; Return one of the following:
  ;   1.  (, ), [, ], eof, eoln;
  ;   2.  an integer or a float number;
  ;   3.  An id beginning by a letter and followed by a mixture of letters, numbers or "_".
  ;   4.  A string on { :, <, > ? //, =, +, -, \, | }.
  (let ((one (my-tyipeek port)))
   (cond ((numeral one) (get-atom3 port 'numeral))
	 ((letterp one) (get-atom3 port 'num-letter))
	 ((infix-letter one) (get-atom3 port 'infix-letter))
	 ((eq one #/[) (ascii (my-tyi port)))
	 (t (car (errset (ratom port) nil))))))

(defun get-atom3 (port condi &aux l1)
  ; Return a string from "port" such that "condi" is always true.
  (setq l1 (loop while (funcall condi (my-tyipeek port))
		 collect (my-tyi port)))
  (if (numeral (car l1)) 
	then (loop with res = (add (car l1) -48)
		   for next in (cdr l1) 
		   do (setq res (add (times res 10) next -48))
		   finally (return res))
        else (implode l1)))


(defun numeral (p) (and (>= p #/0) (<= p #/9)))
(defun num-letter (p) (or (letterp p) (numeral p)))
(defun infix-letter (p)
  (memq p
	'(#/. #/! #/@ #/# #/$ #/% #/^ #/& #/* #/- #/: #/_ #/= #/+ #/\ #/> #/<)))
; ---------- use positive check. HZ 12/88

(defun is-empty-line (&optional in-port)
  ; Returns T if we are at the end of a line in IN-PORT.
  ;        32 = ' '     10 = CR       -1 = EOF
  (do ((peek (my-tyipeek in-port) (my-tyipeek in-port)))
      ((not (memq peek '(#\tab #\space))) 
       (or (memq peek '(#\newline #\return -1 148))))
      (my-tyi in-port)))

(defun tyipeek-space (in-port)
  ; Peeks at the next character that is not a space from the
  ; port IN-PORT and returns that character.
  (do ((peek (my-tyipeek in-port) (my-tyipeek in-port)))
      ((not (memq peek '(#\space #\tab))) peek) ;
      (my-tyi in-port)))

(defun tyipeek-spa-cr (in-port)
  ; Peeks at the next character that is not a space from the
  ; port IN-PORT and returns that character.
  (do ((peek (my-tyipeek in-port) (my-tyipeek in-port)))
      ((not (memq peek '(#\tab #\space #\newline #\return 148))) peek)
      (my-tyi in-port)))

; Following functions are less general because they use the global variables
; $in-port and $log-port. For general use, we can delete the lines containing
; those global variables.

;	read-atom:	Read an atom from a file or terminal.
;       read-args:  	Read a list (nonempty) of atoms from the terminal.
;	ask-a-choice:   Ask the user to give a choice.
;       ok-to-continue: Ask the user whether he wants to continue.
;       choose-str:	if a string is a subsequence of one element in a list
;			then returns that element. We assume that the list
;			is already in lexicograhcal order (from small to 
;			great).

(defun read-atom (flag &optional in-port &aux atom)
  ; Returns next atom from IN-PORT or $IN-PORT or TERMINAL.
  (if in-port then (car (errset (ratom in-port) nil)) else
     (if (and $in-port (eq (tyipeek-spa-cr $in-port) -1)) then 
	 (close $in-port) (setq $in-port nil)
	 (if $test then 
	     (close $log-port)
	     (setq $log-port nil
		   $in-port (pop $save-in-port)
		   $test nil)))
     (setq atom (car (errset (ratom $in-port) nil)))
     (if (eq atom '|;|) then
	 (loop while (not (member (my-tyi in-port)
				  `(,sharp-backslash-end nil #\return #\newline))))
	 (read-atom flag in-port)
	 else
	 (caseq flag
	   (none nil)
	   (end (save-word-end atom))
	   (noend (save-words (list atom))))
	 atom)))

(defun save-word-end (atom)
  (when $log-port 
    (princ atom $log-port)
    (terpri $log-port))
  (when $in-port 
    (princ atom)
    (terpri)))

(defun save-words (atoms)
  (when $log-port
    (loop for atom in atoms do 
      (princ atom $log-port) (princ " " $log-port)))
  (when $in-port
    (loop for atom in atoms do 
      (princ atom) (princ " "))))

(defun read-args (&optional in-port)
  ; Read a list (nonempty) of atoms from the terminal.
  (let ((l1 (cons (read-atom 'none in-port)
		  (loop while (not (is-empty-line in-port)) 
					collect (read-atom 'none in-port)))))
    (if $log-port then 
	(loop for xa in l1 do (princ xa $log-port) (princ " " $log-port))
	(terpri $log-port))
    (if $in-port then (loop for xa in l1 do (princ xa) (princ " ")) (terpri))
    l1))

(defun ask-a-choice (choices message)
  ; Ask the user to choose one from "choices".
  (if (is-empty-line $in-port) then (princ message))
  (do
    ((ans (read-atom 'none) (read-atom 'none)))
    ((memq ans choices) 
     (save-word-end ans)
     ans)
    (invalid-input-warning ans)
    (princ message)
    (clean-line $in-port)))

(defun clean-line (&optional port)
  (loop while (not (member (my-tyi port)
			   `(,sharp-backslash-end nil #\newline
			     #+lispm 148 
			     #-lispm #\return 
			     )))))

(defun ask-a-number (default)
  ; ask the user to give a natural number. If the number is smaller than 1, 
  ; the default value is returned.
  (do
    ((ans (read-atom 'none) (read-atom 'none)))
    ((numberp ans)
     (if (< ans 0) then (setq ans default))
     (save-word-end ans)
     ans)
    (invalid-input-warning ans)
    (princ "A number, please ! ")
    (clean-line $in-port)))

(defun ok-to-continue (&optional message &aux answer)
  ; Return T if the user gives "y or yes".
  (if message
      (member (ask-choice answer '(y n yes no) message)
	      '(y yes))
      (member (ask-choice answer '(y n yes no) "Is it ok to continue ? ")
	      '(y yes))))

(defun choose-str (key choices)
  ; if KEY is a subsequence of one element in CHOICES and they
  ; have the same starting character, returns that element. 
  ; If there are more than one element satisfying the above
  ; conditions, then return the first one.
  (if (symbolp key) then
      (let ((chn (getcharn key 1)))
	(loop for choice in choices do
	  (if (and (eq chn (getcharn choice 1))
		   (or (is-subsequence key choice)
		       (is-subsequence choice key))) then
		 (if $log-port then
		     (if (or (eq choice 'auto) (eq choice 'log))
			 then (princ "Warning: Log file is open. ") 
			 elseif (not (member choice '(help dump unlog)))
			 then (princ choice $log-port) (terpri $log-port)))
		 (if $in-port then (princ choice) (terpri))
		 (return choice))
	      finally (progn 
			(if $in-port then (princ key) (terpri))
			(return key))))
      elseif (listp key) 
      then (if $in-port then (princ key) (terpri) (reset))
      else key))

(defun read-this-eqn ()
  ;; used in prove.l to read in an equation to prove.
  (let (eqn buffer)
    (if (is-empty-line $in-port) then
	(princ "Type your equation in the format:  L == R (if C) ")
	(terpri) (princ "Enter a ']' to exit when no equation is given.")
	(terpri))
    (setq buffer (make-buffer $in-port)
 	  $newops nil)
    (if (not (eq (token-eoln buffer) 'eof)) then
	  (setq eqn (*catch 'error (input-check (get-equation buffer)))))
    (if (or (null eqn) (eq 'error eqn)) 
     then (if $log-port then (princ "]" $log-port) (terpri $log-port)) nil
     else (if (null (rhs eqn)) then (setq eqn (change-rhs eqn '(true))))
          (if $log-port then (write-f-eqn eqn $log-port))
	  (if $in-port then (write-eqn eqn)) (terpri)
	  (flatten-eqn eqn))))

(defun lowcase (n)
  ; If "n" presents a character between 'A-Z', then change it to 'a-z'.
  ; A = 65, Z = 90, a = 97,
  (if (and n (<= #/A n) (<= n #/Z)) then (+ n 32) else n)) 

(defun print-choice-message (&rest messages)
  (if (is-empty-line $in-port) then
    (if messages then 
      (princ (car messages))
      (loop for xa in (cdr messages) do (terpri) (princ xa)))))


(defun invalid-input-warning (some)
  (princ "Invalid input: `") (princ some) 
  (if $in-port 
      then
      (princ "'. Modify your cmd file.") (terpri)
      (setq $in-port nil) (reset)
      else (princ "'. Try again.") (terpri)))
