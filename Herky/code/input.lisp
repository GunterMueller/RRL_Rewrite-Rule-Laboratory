(in-package "USER")

;;;> ** (c) Copyright 1988 The University of Iowa.  All rights reserved.

;; $log-port: Set up by "log" command. When it is not nil, the port is used 
;;            to registry the correct commands the user fed on the keybord 
;;	      to make log files.
;; $in-port:  Set up by "auto" or "test" commands. When it is not nil, the 
;;            port is used to provide the commands pre-registried by "log" 
;;	      command.
;;  At any time, at least one of the above variables is nil.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; operations on $log-port

#|
(defmacro try-to-open-log-port (cmd avoid-list)
  `(when (and (null $log-port) (eq $in-port piport)
	      (not (memq ,cmd ,avoid-list)))
			
	;; Save everything typed by the user. 10/1/90.
	(setq $log-port (or (outfile "herky.cmd") 
			    (outfile "~/herky.cmd") 
			    (outfile "/tmp/herky.cmd")))
	(if $log-port (save-cmd-end ,cmd 'princ))
	))
|#

(defmacro open-new-log-port ()
  `(when (and (null $log-port) (eq $in-port piport))
	;; Save everything typed by the user. 5/1/91
	 (setq $log-flag nil)
	 (setq $log-port (or (outfile "herky.cmd") 
			     (outfile "~/herky.cmd") 
			     (outfile "/tmp/herky.cmd")))
	 ))

(defun save-cmd (cmd &optional (write #'princ))
  (setq cmd (string-downcase (princ-to-string cmd)))
  (when (and $log-port 
	     (not (member0 cmd *avoid-cmds*)))
	(setq $log-flag t)
	(funcall write cmd $log-port) (princ " " $log-port))
  (unless (eq $in-port piport) (funcall write cmd) (princ " ")))

(defun save-cmd-end (cmd &optional (write #'princ))
  (setq cmd (string-downcase (princ-to-string cmd)))
  (when (and $log-port 
	     (not (member0 cmd *avoid-cmds*)))
	(setq $log-flag t)
	(funcall write cmd $log-port) (terpri $log-port))
  (unless (eq $in-port piport) (funcall write cmd)
	  (terpri)))

(defun save-cmds (cmds &optional (write #'princ))
  (sloop for cmd in cmds do 
	 (setq cmd (string-downcase (princ-to-string cmd)))
	 (when $log-port (funcall write cmd $log-port) (princ " " $log-port))
	 (unless (eq $in-port piport) (funcall write cmd) (princ " "))
	 )
  (if (neq $in-port piport) (terpri))
  (if $log-port (terpri $log-port))
  )

(defun terpri-cmd ()
  (when $log-port (terpri $log-port))
  (unless (eq $in-port piport) (terpri))
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun read-input (&optional terminal)
   ; Read equations from terminal.
   (let ((eqns (if terminal (readteqns) (readfeqns))))

     ;; Is there any predicate assertions?
     (when (and (not $automatic) (not $fopc))
       (dolist (eqn eqns)
	 (if* (assertionp eqn) then
	      (setq $fopc t			
		    $trace-proof t
		    )
	      (return)
	      elseif (falsep (rhs eqn))
	      then 
	      (setq $trace-proof t
		    )
	      ))

       ;; initialize flags for first order predicate calculus 
       ;; using the boolean-ring method.
       (when (and $fopc (not $condi))
	     (terpri)
	     (princ "Warning: the ordering is set to size+lrpo.")
	     (terpri)
	     (setq $crit-with-str 'a  
		   $ordering 's
		   $del-rule-str 1
		   $newrule-max 10000)))
     
     (when $fopc (dolist (xa eqns) (set-input-ass xa)))

     (sys-flag-init)
     (when (and terminal $log-port) 
	   ;; Make log file. Write equations in it.
	   (write-eqns eqns $log-port) 
	   (princ "]" $log-port) (terpri $log-port))
     (if (or $fopc $ac)
	 (mapcar 'process-input-eqn eqns)
	 eqns)))

(defun open-read-file (&optional suffix)
  ; Read in a file name and try to open it to read. Look for the file 
  ; with the default suffix and in the example-directory, too.
  (let (filename port)
    (if (io-eoln $in-port) (princ "Type filename: "))
    (setq filename (read-atom 'end))
    (when filename
      (if (setq port
		    (or (infile (uconcat filename "." suffix))
			(infile filename)
			(infile (uconcat $example-directory filename "." suffix))
			(infile (uconcat $example-directory filename))))
	  (format t "    ~s is open to read.~%" 
		  (uconcat filename "." suffix))
	(format t " Error : Couldn't open file: ~s ~%" 
		(uconcat filename "." suffix)))
      port)))

(defun readfeqns (&aux port)
  ;; Read in a file name from terminal and then open it to read the equations
  ;; in and return them. 
  (when (setq port (open-read-file "eqn")) 
    (prog1 (read-eqns port) (close port))))

(defun readteqns ()
  ;; Read the equations from $in-port if it is openned by "auto" command.
  ;; Otherwise read equations from the keybord. 
  (princ "Type your equations, enter a ']' when done." $out-port)
  (terpri $out-port) 
  (read-eqns $in-port))

(defun read-eqns (&optional (in-port piport) buffer)
  ; Returns the list of equations read in from the given port.
  ; The list of equations can be terminated by either an end-of-file,
  ; or "]" symbol.
  (let (eqns eqn (lastop 0))
    (setq $newops nil)
    (setq buffer (make-buffer in-port))
    (until (io-eof in-port)
      (init-var-tab)
      (token-eoln buffer) ; skip eoln in buffer.
      (setq eqn (catch 'input
		 (if (equal (token-id buffer) '|[|) 
		     (read-arity buffer)
		   (eqn-syntax-check (get-equation buffer)))))
      (cond ((eq eqn 'error) (return))
	    (eqn (if $automatic (setq eqn (automatic-check eqn lastop)))
		 (if eqn (push eqn eqns))
		 (setq lastop (car $newops)))
	    ))

    (io-char-init)

    (when eqns 

      (if $automatic (automatic-adjust))

      (when $newops 
	    ;; (terpri) (princ "New operators have the arities:") (terpri)
	    ;; (display-arity2 $newops)
	(when (setq eqn (get-constants $newops)) 
	  ;; Display constant operators to make the user aware 
	  ;; of variable name problem.
	  (terpri $out-port)
	  (princ "New constant set is: " $out-port)
	  (princ (display-ops eqn) $out-port) 
	  (terpri $out-port)))
      (terpri $out-port)
      (if (eq eqn 'error) 
	  (princ "Part of equations are succesfully read:" $out-port)
	(princ "Equations read in are:" $out-port))
      (terpri $out-port) 
      (list-equations (setq eqns (nreverse eqns))))

    (setq $newops nil)
    eqns))

(defun automatic-check (eqn lastop &aux new)
  (if* (and (falsep (rhs eqn)) 
	    (eq (op-of (lhs eqn)) *=*))
       then
       (setq $trace-proof t)

       (when (is-ground (lhs eqn))
	     (setq new (make-eqn (first-arg (lhs eqn)) (second-arg (lhs eqn)) nil
				 (eqn-source eqn)))
	     (when (setq new (check-norm-eqn (process-input-eqn new)))
		   (trace-message 1 "Convert negated Goal: " (write-eqn eqn) 
				  (princ "           into Goal: " $out-port) 
				  (write-eqn new))
		   (setq eqn nil)
		   (push new $prove-eqns)))

       (dolist (op $newops)
	       (if (eq op lastop) (return))
	       (push op $skolem-ops))
       else
       (when (setq new (recognize-theory-eqn eqn)) 
	     (push (cons new eqn) $theory-eqns))
	     
       (dolist (op $newops)
	       (if (eq op lastop) (return))
	       (if (not (is-constant-op op))
		   (setq $skolem-ops (delete op $skolem-ops))))
       )		  
  eqn)

(defun automatic-adjust ()
  (sloop for op in $associative do
	 (when (member op $commutative)
	       (query-insert op $ac)
	       (init-ac-arrays)
	       (setq $commutative (delete op $commutative))))
  )

(defun read-this-eqn ()
  ;; used in prove.l to read in an equation to prove.
  (let (eqn buffer)
    (when (io-eoln $in-port) 
      (princ "Type your equation in the format:  L == R {if C} " $out-port)
      (terpri $out-port) 
      (princ "Enter a ']' to exit when no equation is given." $out-port)
      (terpri $out-port))
    (setq buffer (make-buffer $in-port)
 	  $newops nil)
    (init-var-tab) (token-eoln buffer) ; skip eoln in buffer.
    (unless (io-eof $in-port)
      (setq eqn (catch 'input (eqn-syntax-check (get-equation buffer)))))
    (if* (or (null eqn) (eq 'error eqn)) 
     then (when $log-port (princ "]" $log-port) (terpri $log-port)) nil
     else
     (when (null (rhs eqn)) (change-rhs eqn *trueterm*))
     (if $log-port (write-f-eqn eqn $log-port))
     (unless (eq $in-port piport) (write-eqn eqn)) (terpri)
     (process-input-eqn eqn))))

(defun read-t-term ()
  (if* (io-eoln $in-port) then (terpri)
          (princ "Input a term in the form T  or T if C :") (terpri))
   (let (term (buffer (make-buffer $in-port)))
     (if* (not (equal (token-eoln buffer) "eof")) then
	  (setq term (catch 'input (get-term buffer))))
     (if* (and term (nequal term 'error)) then
       (setq term (first term))
       (terpri) (princ "The term read in is:") (terpri) 
      (princ "  ") (write-term term) (terpri) 
      (save-cmd-end term 'write-term)
      term)))

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

(defun read-atom (flag &aux atom)
  ;; Returns next atom from $IN-PORT or PIPORT.
  (when (and (not (equal $in-port piport)) (io-eof $in-port))
	(close-out-file)
	(close $in-port) 
	(setq $in-port piport)
	(if $test-in-process (setq atom t))
	)

  (unless atom ;; if not in test-process.
	  (setq atom (read-string $in-port))
	  (case flag
		(none nil)
		(end (save-cmd-end atom 'princ))
		(noend (save-cmd atom 'princ)))
	  atom))

(defun read-args ()
  ; Read a list (nonempty) of atoms from the terminal.
  (let (l1)
    (setq l1 (list (read-atom 'none)))
    (while (not (io-eoln $in-port)) 
      (push (read-atom 'none) l1))
    (save-cmds (setq l1 (nreverse l1)))
    l1))

(defun read-nums ()
  ; Read a list (nonempty) of atoms from the terminal.
  (sloop for xa in (read-args) 
	 if (is-number-string xa)
	 collect (s2n xa)))

(defun choose-str (key choices &aux chn)
  ; if KEY is a subsequence of one element in CHOICES and they
  ; have the same starting character, returns that element. 
  ; If there are more than one element satisfying the above
  ; conditions, then return the first one.
  (if* (stringp key) then
       (setq key (string-upcase key)
	     chn (getcharn key 1))
       (sloop for ch in choices
	      for choice = (string ch) do
	      (when (and (equal chn (getcharn choice 1))
			 (or (is-subsequence key choice)
			     (is-subsequence choice key))) 
		    (save-cmd-end choice)
		    (return ch))
	      finally (progn 
			(unless (eq $in-port piport) (princ key) (terpri))
			(return key)))
       elseif (listp key) 
       then (unless (eq $in-port piport) (princ key) (terpri) (reset))
       else key))

(defmacro ask-number (current &rest messages)
  ; ask the user to give a natural number. 
  `(let ()
     (print-choice-message ,@messages)
     (when (and (io-eoln $in-port) ,current) 
       (format t "~%(current value: ~s) " ,current))
     (setq ,current (ask-a-number))))

(defmacro print-choice-message (messages)
  (if (stringp messages)
      `(when (and (io-eoln $in-port) ,messages)
	 (princ ,messages))
      `(when (and (io-eoln $in-port) ,messages)
	   (princ (car ,messages))
	   (dolist (xa (cdr ,messages)) (terpri) (princ xa)))))

(defmacro ask-choice (current choices messages)
  ; >>>>>>> 1/16/89
  ; Ask the user to choose one from "choices". The current value is displaied.
  `(progn
     (print-choice-message ,messages)
     (when (and (io-eoln $in-port) ,current) 
       (format t "~%(current value: ~s) " ,current))
     (setq ,current (ask-a-choice ,choices))))

(defmacro ok-to-continue (&optional (message "Is ok to continue?"))
  `(progn
     (when (io-eoln $in-port) (princ ,message))
     (equal (ask-a-choice '(y n)) 'y)))

(defun ask-a-choice (choices)
  ; Ask the user to choose one from "choices".
  (if (io-eoln $in-port) (print-elements choices ", "))
  (do
   ((ans (read-atom 'none) (read-atom 'none)))
   ((and ans (member (setq ans (read-from-string ans)) choices))
    (save-cmd-end ans 'princ)
    ans)
   (format t "Invalid input: ~s~%" ans)
   (print-elements choices ", ")
   (io-skip-line $in-port)))

(defun ask-a-number (&aux ans)
  ; ask the user to give a natural number. If the number is smaller than 0, 
  ; the default value is returned.
  (while t
    (setq ans (read-atom 'none))
    (when (and ans (is-number-string ans)) 
	  (save-cmd-end ans 'princ)
	  (return (s2n ans)))
    (princ "Invalid input: `") (princ ans) (princ "'") (terpri)
    (princ "A number, please ! ")
    (io-skip-line $in-port)))

(defun recognize-theory-eqn (eqn)
  ;; Return 1 if eqn is a commutative law, i.e., x + y = y + x
  ;;        2 if eqn is an associative law, i.e., (x + y) + z = x + (y + z)
  ;;        3 if eqn is a right unit law, i.e., x + c = x
  ;;        4 if eqn is a left unit law, i.e., c + x = x
  ;;        5 if eqn is a right inverse law, i.e., x + i(x) = c
  ;;        6 if eqn is a left inverse law, i.e., i(x) + x = c
  ;;        7 if eqn is a right distributive law, i.e., z * (x + y) = (z * x) + (z * y)
  ;;        8 if eqn is a left distributive law, i.e., (x + y) * z = (x * z) + (y * z)
  (if (and (nonvarp (lhs eqn)) (eq (get-arity (op-of (lhs eqn))) 2))
      (let ((term (lhs eqn)) (rhs (rhs eqn)) op1 op2 t1 t2 s1 s2 switch)
	(setq op1 (op-of term)
	      t1 (first-arg term)
	      t2 (second-arg term))
	(if (nonvarp t1) (psetq t1 t2 t2 t1 switch t))

	(if (variablep t1) 
	    (cond ((variablep t2)
		   (when (and (not (eq t1 t2))
			      (nonvarp rhs)
			      (eq (op-of rhs) op1)
			      (eq (first-arg rhs) t2)
			      (eq (second-arg rhs) t1))
			 1)) ; commutative
		  (t (setq op2 (op-of t2))
		     (case (get-arity op2)
			   (0 (when (eq rhs t1) 
				    (push (list op1 op2 switch) $unit-ops) 
				    (if switch 4 3))) ; x + c = x
			   (1 (when (and (eq t1 (first-arg t2))
					 (is-constant-term rhs))
				    (push (list op2 op1 (op-of rhs) switch) $inverse-ops)
				    (if switch 6 5))) ; x + i(x) = c
			   (2 (when (and (variablep (first-arg t2))
					 (variablep (second-arg t2))
					 (nonvarp rhs)
					 (eq op2 (op-of rhs)))

				  (setq s2 (second-arg rhs) s1 (first-arg rhs))

				  (cond ((eq op1 op2)
					 (if switch (psetq s1 s2 s2 s1))

					 (when (and (nonvarp s1)
						    (eq op1 (op-of s1))
						    (member t1 (args-of s1))
						    (have-common (args-of t2) (args-of s1))
						    (member s2 (args-of t2))
						    (is-linear term))
					       2)) ; associative
					(t ; op1 \= op2
					 (when (and (nonvarp s1)
						    (eq op1 (op-of s1))
						    (member t1 (args-of s1))
						    (member (first-arg t2) (args-of s1))
						    (nonvarp s2)
						    (eq op1 (op-of s2))
						    (member t1 (args-of s2))
						    (member (second-arg t2) (args-of s2))
						    (is-linear term))
					       (push (list op1 op2 switch) $distributive)
					       (if switch 8 7))))
				  ))
			   ))
		  )))))

(defun digest-theory-eqns ()
  ;;  Type: 1 if eqn is a commutative law, i.e., x + y = y + x
  ;;        2 if eqn is an associative law, i.e., (x + y) + z = x + (y + z)
  ;;        3 if eqn is a right unit law, i.e., x + c = x
  ;;        4 if eqn is a left unit law, i.e., x + c = x
  ;;        5 if eqn is a right inverse law, i.e., x + i(x) = c
  ;;        6 if eqn is a left inverse law, i.e., x + i(x) = c
  ;;        7 if eqn is a right distributive law, i.e., z * (x + y) = (z * x) + (z * y)
  ;;        8 if eqn is a left distributive law, i.e., z * (x + y) = (z * x) + (z * y)
  (setq $theory-eqns (nreverse $theory-eqns))

  (digest-ac-eqns)

  (digest-abelian-group-eqns)
	 
  (setq $theory-eqns nil)
  )

(defun digest-ac-eqns (&aux op)
  (sloop for xa in $theory-eqns
	 for eqn = (cdr xa) 
	 if (nonvarp (lhs eqn)) do
	 (setq op (op-of (lhs eqn)))
	 (case (car xa)
	       (1 (if* (or (member op $ac) (member op $commutative))
		       then nil
		       elseif (member op $associative)
		       then 
		       (setq $associative (delete op $associative))
		       (sloop for xb in $theory-eqns 
			      if (and (eq (car xb) 2)
				      (nonvarp (lhs (cdr xb)))
				      (eq (op-of (lhs (cdr xb))) op))
			      do (make-theory-rule (cdr xb)) (return))
		       (ext-ac op)
		       (make-theory-rule eqn)
		       else
		       (ext-commutative op)
		       (make-theory-rule eqn)))
	       (2 (if* (or (member op $associative) (member op $ac))
		       then nil
		       elseif (member op $commutative)
		       then
		       (setq $commutative (delete op $commutative))
		       (ext-ac op)
		       (make-theory-rule eqn)
		       else
		       (push op $associative)))
	       (t nil)
	       )))
  
(defun digest-abelian-group-eqns ()
  (sloop for t4 in $inverse-ops 
	 if (and (member (cadr t4) $ac)
		 (member0 (cdr t4) $unit-ops))
	 do
	 (setq $polynomial t
	       *0* (caddr t4)
	       *0term* (make-term *0* nil)
	       *+* (cadr t4)
	       *-* (car t4)
	       )
	 (sloop for xa in $theory-eqns for eqn = (cdr xa)
		if (and (member (car xa) '(3 4 5 6))
			(eq (op-of (lhs eqn)) *+*))
		do (make-theory-rule eqn))
		
	 (digest-distributive-eqns)
	 (return)
  ))

(defun digest-distributive-eqns ()
  (sloop with first
	 for t3 in $distributive 
	 if (eq (cadr t3) *+*) 
	 do (if first 
		(when (and (eq (car first) (car t3))
			   (nequal (caddr first) (caddr t3)))
		      (setq $*$ (car t3))
		      (set-op-status $*$ 'lr)
		      (sloop for xa in $theory-eqns for eqn = (cdr xa)
			     if (and (member (car xa) '(7 8))
				     (eq (op-of (lhs eqn)) $*$)
				     (eq (op-of (rhs eqn)) *+*))
			     do (make-theory-rule eqn))
		      (set-check-homogenous)
		      (return))
	      (setq first t3))
	 ))

(defun set-check-homogenous (&aux (max 4))
  ;; return the max degree if the input equations are homogenous.
  (sloop for eqn in $eqn-set do
	 (if* (or
	      (variablep (lhs eqn))
	      (neq (op-of (lhs eqn)) $*$)
	      (member0 eqn $theory-rules))
	      then nil
;	      elseif (and (falsep (rhs eqn))
;			  (eq (op-of (lhs eqn)) *=*))
;	      then (setq max (product-degree (first-arg (lhs eqn))))
	      elseif (neq (product-degree (lhs eqn))
			  (product-degree (rhs eqn)))
	      then (return (setq max 0))))

  (when (> max 0)
      (setq $check-homogenous t)
      (if (> $discard-eqn-max-degree max)
	  (setq $discard-eqn-max-degree max)))
  max)

(defun set-short-hand-flag (&aux ops)
  (if* (sloop for op in $skolem-ops always (is-constant-op op))
       then
       (when (and $prove-eqns
		  (applies '(1 (1 (1 -1 -2) (1 -2 -1)) (1 -2 -1))
			   (lhs (car $prove-eqns))))
	     (setq $ordering 's
		   $reduce-system 0
		   $discard-eqn-max-size 13 ;; ; 13
		   $discard-eqn-2max-size 0 ;;
		   ))
       else
       ;; a DEFAULT strategy for this kind of problems. 
       (setq $ordering 's
	     $reduce-system 0)
       (setq ops (sloop for op from *first-user-op* below $num-ops
			if (and (not (memq op $skolem-ops)) 
				(is-constant-op op))
			collect op))
       (if (< (length ops) 3) (setq $instant-seeds t))
       ))
