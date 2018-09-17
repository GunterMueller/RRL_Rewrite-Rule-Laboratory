(in-package "USER")

;; ================================================
;; Output Functions
;; ================================================

(defmacro trace-message (level mes &body body)
  (if *no-trace-message*
    (case level
	  (0 `(let () (terpri) (princ ,mes) ,@body))
	  (1 `(when (> $trace-flag 0) 
		    (terpri) (princ ,mes) ,@body))
	  (2 `(when (> $trace-flag 1) 
		    (terpri) (princ ,mes) ,@body))
	  )
    (case level
	  (0 `(let () (terpri $out-port) (princ ,mes $out-port) ,@body))
	  (1 `(when (> $trace-flag 0) 
		    (terpri $out-port) (princ ,mes $out-port) ,@body))
	  (2 `(when (> $trace-flag 1) 
		    (terpri $out-port) (princ ,mes $out-port) ,@body))
	  (3 `(when (> $trace-flag 2) 
		    (terpri) (princ ,mes) ,@body))
	  (4 `(when (> $trace-flag 3) 
		    (terpri) (princ ,mes) ,@body))
	  )))

(defun display (&optional (disp-rules t) (port $out-port))
  ; Prints a list of the equations and rules.  If DISP-RULES is nil
  ; then only the equations are displayed.
  (display-type-arity (every-ops) port)
  (when $ac
    (terpri port)
    (princ "Associative & commutative operator set = " port)
    (princ (display-ops $ac) port) (terpri port))
  (when $commutative 
    (terpri port)
    (princ "Commutative operator set = " port)
    (princ (display-ops $commutative) port)
    (terpri port))
  (if* (or $eqn-set $post-set $post-ass-set) then
    (princ "Equations:" port) (terpri port)
    (list-equations $eqn-set port)
    (list-equations $post-set port (length $eqn-set))
    (if $post-ass-set 
	(list-assertions $post-ass-set (length (append $eqn-set $post-set)) port))
    else
    (princ "No equations in current system." port) (terpri port))
  (terpri port)
  (when disp-rules 
    (if* $rule-set
	 then (princ "Rules:" port) (terpri port) (list-rules $rule-set port)
	 else (princ "No rules in current system." port) (terpri port))))

(defun display-stat (&optional (port $out-port))
  (when $prove-eqn
	(terpri port)
	(princ "You are proving the equation:" port) (terpri port)
	(princ "    " port) (write-eqn $prove-eqn port)
	)
  (terpri port)
  (display-kb-stat port)
  (if* $constructors 
       then (princ "Constructors : " port) (princ (display-ops $constructors) port) 
       else (princ "No constructors." port))			
  (terpri port) (terpri port) 
  (princ "Termination Ordering : " port)
  (if (eq $ordering 'm) 
      (princ "Manual" port) 
    (if (eq $ordering 's)
	(princ "Size + Lexicographic Ordering." port)
      (if $lrpo
	  (princ "Lexicographic Recursive Path Ordering (LRPO)" port) 
	(princ
	 "Manual and Lexicographic Recursive Path Ordering (LRPO)" port))))
  (terpri port)
  (display-op-stats port)

  (princ "Normalization Strategy : " port)
  (princ (case $norm-str
	       (e "Efficient Innermost")
	       (i "Innermost")
	       (m "Mixed")
	       (o "Outermost")) port) 
  (terpri port)
  (princ "Critical Pair Strategy : " port)
  (princ (case $pick-rule-str
	       (m "Manually chosen rule with ")
	       (e "Earliest generated smallest rule with ")
	       (l "Latest generated smallest rule with ")
	       (o "Oldest rule with ")
	       (f "First unmarked rule with ")) port)
  (princ (case $crit-with-str
	       (m "all marked rules.")
	       (o "all older rules.")
	       (a "all other rules.")
	       ((h1 h2) "manually chosen rule.")) port) 
  (terpri port)
  (terpri port)
  )

(defun display-kb-stat (&optional (port $out-port))
  (let ((x1 (time-in-sec $proc-time)) x2 $unif-time)
    (format port "Number of rules generated             = ~d~%" $nrules)
    (format port "Number of rules retained              = ~d~%"
	    (length $rule-set))
    (format port "Number of critical pairs              = ~d"
	    (if $block-cps (+ $block-cps $ncritpr) $ncritpr))
    (cond
     ($prime-cps (format port " (of which ~d are composite.)~%" $prime-cps))
     ((and $left-cps $block-cps)
      (format port " (~d left-composite; ~d unblocked.)~%" 
	      $left-cps $block-cps))
     ($left-cps (format port " (of which ~d are left-composite.)~%" $left-cps))
     ($block-cps (format port " (of which ~d are unblocked.)~%" $block-cps))
     (t (terpri port)))
     
     (format port "Time used (incl. garbage collection)  = ~,3f sec~%" x1) 
     (when (> $norm-time 0.001) 
     ;; Because (add-time) macro is very expensive, we eliminate
     ;; its calls to $unif-time and $block-time. 10/11/90.
    
     (setq $unif-time (abs (- $proc-time (+ $norm-time $ord-time $add-time))))
     (format port " Time spent in normalization          = ~,3f sec " 
	     (setq x2 (time-in-sec $norm-time)))
     (format port " (~,2f %)~%"  (times 100 (/ x2 x1)))
     (format port " Time spent in unification            = ~,3f sec " 
	     (setq x2 (time-in-sec $unif-time)))
     (format port " (~,2f %)~%"  (times 100 (/ x2 x1)))
     (format port " Time spent in ordering               = ~,3f sec "
	     (setq x2 (time-in-sec $ord-time)))
     (format port " (~,2f %)~%"  (times 100 (/ x2 x1)))
     (format port " Time spent in simplifying the rules  = ~,3f sec " 
	     (setq x2 (time-in-sec $add-time)))
     (format port " (~,2f %)~%"  (times 100 (/ x2 x1)))
     (when (or $ac $commutative $fopc)
       (format port " Time spent in flattening terms       = ~,3f sec " 
	       (setq x2 (time-in-sec $brt-time)))
       (format port " (~,2f %)~%"  (times 100 (/ x2 x1))))
     )
     (when (eq poport port) (princ "Done at: ") (date))
     (terpri port)
     ))
   
(defun display-op-stats (&optional port)
  ; Displays to the user the current equivalence, precedence and
  ; status relation among operators in the system.  Returns NIL.
  (terpri port)
  (if* $eqop-list
      then (princ "Equivalence relation among operators now is:" port) (terpri port)
	   (sloop for xa in $eqop-list do 
	      (princ "Equivalent set: " port)
	      (princ (display-ops xa) port) (terpri port))
      else (princ "There are no equivalent operators." port) (terpri port))
  (terpri port)
  (if* $precedence
      then (princ "Precedence relation now is: " port) (terpri port) 
	   (sloop for xa in $precedence do
		 (princ (uconcat "   " (op-name (car xa)) " > ") port)
		 (sloop for xb in (cdr xa) do (princ (uconcat (op-name xb) " ") port))
		 (terpri port))
      else (princ "There is no ordering yet in the precedence relation." port)
	   (terpri port))

  (when $l-st-list
    (terpri port) (princ "Operators with left-to-right status are:  " port) 
    (dolist (op $l-st-list) (princ (op-name op) port) (princ ", " port))
    (terpri port))
  (when $r-st-list
    (terpri port) (princ "Operators with right-to-left status are:  " port) 
    (dolist (op $r-st-list) (princ (op-name op) port) (princ ", " port))
    (terpri port))

  (if* $ac then (terpri port)
    (princ "Associative & commutative operator set = " port)
    (princ (display-ops $ac) port)
    (terpri port))
  (if* $commutative then (terpri port)
    (princ "Commutative operator set = " port)
    (princ (display-ops $commutative) port)
    (terpri port))
  (display-type-arity (every-ops) port))

(defun display-ops (ops &aux res)
  (if ops 
   (progn
     (setq res (uconcat "{" (op-name (car ops))))
     (dolist (op (cdr ops)) (setq res (uconcat res ", " (op-name op))))
     (uconcat res "}"))
   "{}"))     

(defun writef-sys (&aux port)
  (setq $write-to-file t)
  (user-menu
    (equations "   Save only equations"
      (when (setq port (open-write-file "eqn" t))
	(write-eqns (append $eqn-set $post-set) port)
	(if* $post-ass-set then (write-assertions $post-ass-set port))
	(close port)
	(princ "Equations written in the file.") (terpri)))
    (rules "       Save only rules. "
      (when (setq port (open-write-file "eqn" t)) 
	(write-rules $rule-set port) (close port)
	(princ "Rules written in the file.") (terpri)))
    (all "         Save both equations and rules. "
      (when (setq port (open-write-file "eqn" t)) 
	(write-eqns (append $eqn-set $post-set) port) (terpri port) 
	(write-rules $rule-set port) 
	(close port)
	(princ "System written in the file.") (terpri)))
    (kb-status "   Save KB statistics in a file with the suffix `.out'. "
      (when (setq port (open-write-file "out" t)) 
	(display t port)
	(terpri port)
	(display-kb-stat port)
	(terpri port) 
	(close port))))
  (setq $write-to-file t))

(defun open-write-file (&optional suffix no-detroy)
  ; Read in a file name and try to open it to write. 
  ; If the filename has no default suffix, then append SUFFIX
  ; to it. If the file exists, then open the file to append.
  (let (filename port)
    (if* (io-eoln $in-port) then (princ "Type filename: "))
    (setq filename (read-atom 'end))
    (unless (is-subsequence suffix filename)
      (setq filename (uconcat filename "." suffix)))
    (when (or (not no-detroy) 
	      (not (probef filename))
	      (ok-to-continue "Overwrite the old file ? "))
      (cond
	((setq port (outfile filename))
	 (format t "    ~s is open to write.~%" filename))
	(t (princ (uconcat "Error: Couldn't open file: " filename))))
      (terpri))
    port))

(defun list-rules (rset &optional (port $out-port))
  (dolist (xa rset) (write-rule xa port)))

(defun list-undeleted-rules (rset &optional (port $out-port))
  (dolist (xa rset)
	  (if (not (is-deleted-rule xa))
	      (write-rule xa port))))

(defun write-rules (rset &optional (port $out-port))
  (sloop for xa in rset do (write-f-rule xa port)))

(defun list-equations (eqns &optional (port $out-port) (i 0))
  (dolist (eqn eqns)
    (incf i)
    (if (< i 10) (princ " " port))
    (princ i port) (princ ". " port)
    (write-eqn eqn port)))

(defun write-eqns (eqns &optional (port $out-port))
  ;  Writes out equations EQNS to port PORT.
  (dolist (eqn eqns) (write-f-eqn eqn port)))

(defun write-f-rule (rule &optional (port $out-port))
  ;  Writes out RULE to PORT.
  (write-term-simple (lhs rule) port)
  (princ " ---> " port)
  (write-f-rhs (rhs rule) (ctx rule) port)
  (terpri port))

(defun write-rule (rule &optional (port $out-port))
  ; writes out RULE to PORT, precedes it with its rule number.
  (if (< (ruleno rule) 10) (princ "  " port) (princ " " port))
  (write-p-rule rule port)
  (if (and (order-condition rule) (cdr (order-condition rule)))
      (write-order-condition rule port))
  (setq rule (rule-source rule)) 
  (format port "  [~s, ~s]~%" (car rule) (cadr rule)))

(defun write-p-rule (rule port)
  (format port "[~d] " (ruleno rule)) 
  (write-term (lhs rule) port)
  (princ " ---> " port)
  (write-rhs (rhs rule) (ctx rule) port)
  )

(defun write-order-condition (rule port)
  (princ " { if " port) 
  (write-term-simple (cadr (order-condition rule)) port)
  (princ " > " port)
  (write-term-simple (caddr (order-condition rule)) port)
  (princ " }" port)
  )

(defun write-f-eqn (eqn &optional (port $out-port))
  ;  Writes out equation EQN to port PORT.
  (write-term-simple (lhs eqn) port)
  (when (or (is-condi-eqn eqn) (not (is-assertion eqn)))
    (princ " == " port)
    (write-f-rhs (rhs eqn) (ctx eqn) port))
  (terpri port))

(defun write-eqn (eqn &optional (port $out-port))
  ;  Writes out equation EQN to port PORT.
  (write-term (lhs eqn) port)
  (when (or (is-condi-eqn eqn) (not (is-assertion eqn))) 
    (princ " == " port)
    (write-rhs (rhs eqn) (ctx eqn) port))
  (setq eqn (eqn-source eqn)) 
  (format port "  [~s, ~s]~%" (car eqn) (cadr eqn)))

(defun write-rhs (rhs ctx &optional (port $out-port))
  (if (truep rhs) (princ "true" port) (write-disjunctions rhs 2 port))
  (when ctx 
    (princ "  if  " port)
    (if (is-premise-set ctx) 
	 (write-premises (cdr ctx) port)
	 (write-disjunctions ctx 3 port))))

(defun write-f-rhs (rhs ctx &optional (port $out-port))
  (if (truep rhs) (princ "true" port) (write-term-simple rhs port))
  (when ctx
	(princ " if " port) 
	(if (is-premise-set ctx) 
	    (write-f-premises (cdr ctx) port)
	  (write-term-simple ctx port))))

(defun list-assertions (asss num &optional (port $out-port))
  (sloop for xa in asss for i from (add1 num) do 
	 (if (< i 10) (princ " " port))
	 (princ i port) (princ ". " port)
	 (write-assertion (cadr xa) (cddr xa) port)))

(defun write-assertions (asss &optional (port $out-port))
  (sloop for xa in asss do (write-term-simple (cddr xa) port) (terpri)))

(defun write-assertion (source ass &optional (port $out-port))
  (write-term ass port)
  (format port "  [~s, ~s]~%" (car source) (cadr source)))

(defun write-term (term &optional (port $out-port))
  (write-term-bool term port))

(defun write-term-bool (ct &optional (port $out-port))
  (if* (variablep ct) then (write-variable ct port) else
  (cond ((eq (op-of ct) *xor*)
	 (princ "(" port) 
	 (write-term-bool (first-arg ct) port)
         (sloop for xa in (cdr (args-of ct)) do
		(princ " + " port) (write-term-bool xa port))
	 (princ ")" port))
	((eq (op-of ct) *and*)
	 (write-term-simple (first-arg ct) port)
         (sloop for xa in (cdr (args-of ct)) do
		(princ " & " port) (write-term-simple xa port)))
	(t (write-term-simple ct port)))))

(defun write-term-simple (term &optional (port $out-port) &aux op)
  ; Recursive function used by write-term.
  (if* (variablep term) then (write-variable term port)
       elseif (is-infix-op (setq op (op-of term)))
       then
       (princ "(" port)
       (if* (and $polynomial (eq op *+*)) then
	    (setq term (mult-form (args-of term)))
	    (if* (> (cdar term) 1) (princ (cdar term) port))
	    (write-term-simple (caar term) port)
	    (sloop for xa in (cdr term) do
		   (princ " + " port)
		   (if (> (cdr xa) 1) (princ (cdr xa) port))
		   (write-term-simple (car xa) port))
	    else
	    (write-term-simple (first-arg term) port)
	    (sloop for xa in (cdr (args-of term)) do
		   (princ (uconcat " " (op-name op) " ") port)
		   (write-term-simple xa port))
	    )
	    (princ ")" port)
       else 
       (princ (op-name op) port)
       (cond
       ((member op *exist*all*) 
	(princ " " port)
	(write-variable (first-arg term) port)
	(princ " (" port)
	(write-term-simple (second-arg term) port)
	(princ ")" port))
       (t (if* (args-of term) then
	       (princ "(" port)
	       (write-term-simple (first-arg term) port)
	       (if* (and $write-to-file (ac-op-p op) (cdddr term))
		    then
		    (princ ", " port) 
		    (write-term-simple (make-term op (cddr term)) port)
		    else
		    (sloop for xa in (cdr (args-of term)) do
			   (princ ", " port) (write-term-simple xa port)))
	       (princ ")" port))))))

(defun write-disjunctions (ct spn port)
  (if* (variablep ct) then (write-variable ct port)
    elseif (and (eq (op-of ct) *xor*) (cdddr ct)) 
    then (terpri port) (princ "       " port)
	 (sloop for xx from 1 until (eq xx spn) do (princ "        " port))
	 (princ "(" port)
         (write-term-bool (car (args-of ct)) port)
         (sloop for xa in (cdr (args-of ct)) do
            (princ " + " port) (terpri port)
 	    (sloop for xx from 0 until (eq xx spn) do (princ "        " port))
	    (write-term-bool xa port))
	 (princ ")" port)
    else (write-term-bool ct port)))

(defun write-premises (pres &optional (port $out-port))
  (if* (cdr pres) then
    (terpri port) (princ "        " port)
    (princ "{ " port)
    (write-one-pre (car pres) port)
    (sloop for xa in (cdr pres) do
      (princ "," port) 
      (terpri port)
      (princ "          " port)
      (write-one-pre xa port))
    else
    (princ " { " port) 
    (write-one-pre (car pres) port))
    (princ " } " port))

(defun write-f-premises (pres port)
  (if* (cdr pres) then
    (terpri port) (princ "          (" port)
    (write-one-pre (car pres) port)
    (sloop for xa in (cdr pres) do
      (princ ") and " port) 
      (terpri port)
      (princ "          (" port)
      (write-one-pre xa port))
    (princ ")" port)
    else
    (write-one-pre (car pres) port)))

(defun write-one-pre (pre &optional (port $out-port))
  (if* (equal (cadr pre) *falseterm*)
      then 
      (princ "not(" port) (write-term-bool (car pre) port)
      (princ ")" port)
      else
      (write-term-bool (car pre) port)
      (if* (cadr pre) then 
	(if (variablep (car pre)) 
	    (princ " = " port)
	    (princ " equ " port)) 
	(write-term-bool (cadr pre) port))))

(defun print-elements (list separator &optional (port $out-port))
  (when list 
    (princ "(" port)
    (princ (car list) port)
    (sloop for xa in (cdr list) do 
	   (princ separator port)
	   (princ xa port))
    (princ ") " port)))

(defun print-head (choices)
  ;; choices is a list of symbols.
  (when (io-eoln $in-port) 
     (let ((num 0))
       (princ "Type ")
       (dolist (xa (cdr choices))
	 (when (> (setq num (+ num 2 (length (string xa)))) 74)
	   (terpri) (princ "     ") 
	   (setq num (+ 2 (length (string xa)))))
	 (princ xa) (princ ", "))
       (when (> (+ num (length (string (car choices)))) 70)
	 (terpri) (princ "     "))
       (princ (car choices)) (princ " --> "))))

#|
(defun write-detail-rule (rul port &aux source)
  (setq source (rule-source rul))
  (princ "     " port)
  (caseq (first source)
    ((user def sos) (format port "Input #~s," (second source)))
    (detach (format port "Superposing Rule [~s] with the detachment rule," 
		    (second source)))
    (idem (format port "Superposing Rule [~s] into itself," (second source)))
    (insta (format port "Instantiating Rule [~s]," (second source)))
    (distr (format port "Superposing x * (y + z) ---> (x * y) + (x * z) into Rule [~s],"
		   (second source)))
    (deleted (format port "Deleting Rule [~s] by Rule [~s]," (second source) (third source)))
    (divided (format port "[~s] was divided by disgreement of arguements," 
		     (second source)))
    (t (format port "Superposing ")
       (format port (rule-name (first source) 
			       (memq (third source) '(ext1 ext2))))
       (format port " into ")
       (format port (if (eq (first source) (second source))
			"itself"
		      (rule-name (second source) (eq (third source) 'ext2))))
       (format port ","))
    )

  (setq source (eqn-used-rules rul))
  (when source 
	(if* (cdr source) 
	     then
	     (princ " reduced by Rules" port)
	     (sloop for xa in source do (format port " [~s]," xa))
	     else
	     (format port " reduced by Rule [~s]," (car source)))
	)

  (princ " produces:" port) (terpri port) 
  (write-p-rule rul port)
  (terpri port))
|#

(defun write-detail-rule (rul port &aux source)
  (write-p-rule rul port)
  (setq source (rule-source rul))
  (princ "     { " port)
  (case (first source)
    ((user def sos) (format port "from Input #~s" (second source)))
    (deleted (format port "by deleting Rule [~s] by Rule [~s]" (second source) (third source)))
;    (detach (format port "by superposing Rule [~s] with the detachment rule" 
;		    (second source)))
    (idem (format port "by superposing Rule [~s] into itself" (second source)))
    (insta (format port "by instantiating Rule [~s]" (second source)))
    (distr (format port "by superposing x * (y + z) ---> (x * y) + (x * z) into Rule [~s]"
		   (second source)))
    (divided (format port "by dividing [~s]" (second source)))
    (t (format port "by superposing ")
       (format port (rule-name (first source) 
			       (memq (third source) '(ext1 ext2))))
       (format port " into ")
       (when (eqn-info rul) (write-term (eqn-info rul) port) (princ " of " port))
       (format port (rule-name (second source) (eq (third source) 'ext2)))
    ))

  (setq source (eqn-used-rules rul))
  (if* (null source)
       then (format port ". }")
       elseif (cdr source) 
       then
       (princ "," port) (terpri port)
       (princ "      and then reduced by Rules" port)
       (sloop for xa in (butlast source) do
	      (format port " [~s]," xa))
       (format port " and [~s]. }" (car (last source)))
       else
       (princ "," port) (terpri port)
       (format port "      and then reduced by Rule [~s]. }" (car source))
       )
  (terpri port))

(defun rule-name (num &optional ext) 
  (if ext 
      (uconcat "Extension of Rule [" (princ-to-string num) "]") 
      (uconcat "Rule [" (princ-to-string num) "]")))

(defmacro write-var-term (obj port)
  `(if (car ,obj)
       (progn
	 (write-variable (car ,obj) ,port)
	 (princ "|" ,port)
	 (write-term-simple (cdr ,obj) ,port))
       (princ "x|x" port)))

(defun write-sigma (sigma &optional (port $out-port))
  (unless (empty-sub sigma)
	  (write-var-term (car sigma) port)
	  (dolist (xa (cdr sigma)) (princ ", " port)
		  (write-var-term xa port))))

(defun trace-reduce-lhs (xa &optional because)
  (format t "  Delete Rule [~d]" (ruleno xa))
  (if because (princ because)) (princ ".") (terpri)
  (when (eq $trace-flag 3) (princ "   ") (write-rule xa)))

(defun trace-reduce-rhs (xa term)
  (format t "  The right side of [~d] is reduced to " (ruleno xa))
  (write-term term) (princ ".") (terpri))

(defun seearray (ar h &optional (l 0))
  (sloop for i from l to h do (princ " ") (princ (aref ar i))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Following functions are moved from consistency.lisp.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro collect-unused-rules (rule-set)
  `(dolist (ru ,rule-set)
	   (if (and (eq (first (rule-source ru)) 'user)
		    (not (member ru $theory-rules))
		    (not (memq (ruleno ru) rule-nums)))
	       (push ru unused))))

(defun trace-rule (rule &optional (port $out-port) unused)
  (let (rule-nums)
    ; Trace the sources of this rule.
    (setq $theory-rules (reverse $theory-rules))
    (setq rule-nums (get-all-rule-nums
		     (rule-nums-from-source rule)))

    (sloop for num in rule-nums do
	   (if (eq num 0)
	       (sloop for xa in $theory-rules
		      if (eq (ruleno xa) 0)
		      do (write-detail-rule xa port))
	     (if (setq num (pick-out-rule num)) 
		 (write-detail-rule num port))))

    (write-detail-rule rule port)
    (push (ruleno rule) rule-nums)

    (when (not unused)
	  (collect-unused-rules $rule-set)
	  (collect-unused-rules $del-rules)
	  (when unused 
		(terpri port) 
		(if* (cdr unused)
		     (format port "There are ~d rules" (length unused))
		     (princ "Only one rule is" port))
		(princ " made from the input, but not used in the proof:" port) 
		(terpri port)
		(dolist (ru (sort unused 'ruleno-lessp)) (write-rule ru port))
		))

    (format port "~%The number of the rules in the above sequence is ~d.~%" 
	    (length rule-nums))
    (when (> $reduce-system 2)
      (terpri)
      (dolist (xa '(
"WARNING: Deleted rules might be different from their first appearence," 
"         because original terms were destroyed during simplification."
"         Check the whole transcript for the right forms."))
	      (princ xa port) (terpri port)))
    (unless (eq port $out-port) (display-kb-stat port))
    ))

(defun trace-rule-num (num &aux rule) 
  (if (setq rule (pick-out-rule num))
      (trace-rule rule)
    (format "~%Rule [~d] does not exist!!!~%" num)))

(defun ruleno-lessp (r1 r2) (< (ruleno r1) (ruleno r2)))

(defun get-all-rule-nums (nums &aux rule result)
  ; Return all rule numbers which has some relation with the rules in "nums".
  (sloop while nums for num = (pop nums) 
	 if (and (numberp num) (not (memq num result)))
	 do
	 (push num result)
	 (if (setq rule (pick-out-rule num))
	     (setq nums (append nums (rule-nums-from-source rule)))))
  (sloop for xa in $theory-rules do (query-insert (ruleno xa) result))
  (sort result #'<))

(defun rule-nums-from-source (eqn &aux (source (eqn-source eqn)))
  ; "source" contains the info about the source of a rule and the rules
  ; which has reduced that rule. 
  ; Return a list of rule nums which is in "source".
  (append
   (if* source then
	(case (first source)
	      ((sos user def) nil)
	      ((deleted divided idem) (cdr source))
	      (t source)))
   (eqn-used-rules eqn)))

(defun pick-out-rule (num)
  ; Return a rule of which the number is "num".
  (or (sloop for rule in $rule-set 
	     if (eq (ruleno rule) num) return rule
	     else if (> (ruleno rule) num) return nil)
      (sloop for rule in $theory-rules
	     if (eq (ruleno rule) num) return rule
	     else if (> (ruleno rule) num) return nil)
      (sloop for rule in $del-rules if (eq (ruleno rule) num) return rule)
      ))

(defun report-proof (port)
  (princ "A proof of equation [" port) 
  (princ (car (eqn-source $used-rule-nums)) port)
  (princ ", " port) 
  (princ (cadr (eqn-source $used-rule-nums)) port)
  (princ "] has been found." port) (terpri port)
  )
