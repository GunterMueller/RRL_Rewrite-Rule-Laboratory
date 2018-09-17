(in-package "RRL")
;; This file has all functions used to get the successors
;; of a node.

(defun s-successors (eqn  ans)
;; This function tries all possible TOP-LEVEL restructures
;; and all possible DECOMPOSES. Then it returns the list
;; each member of which has a list of equations, and a new
;; answer.
  (let ((top-op   (operator (s-get-eqn-lhs eqn))))
    (if (member  top-op  $ac)
        (s-ac-restr eqn ans)
        (let   ((s-decom   (s-decompose    eqn     ans))
                (s-restr   (s-restructure  eqn     ans)))
            (if s-decom
                (cons  s-decom s-restr)
                s-restr) ) 
        ) ) )


(defmacro rewrite-with-subs (term subs)
    `(if *s-conditional* 
         (norm-ctx (applysubst ,subs ,term))
         (s-norm-bin ,term ,subs) ) )

(defmacro s-rewrite-with-subs (term subs)
    `(if *eager-rewrite*
         (rewrite-with-subs ,term ,subs)
         ,term))

(defmacro is-constructor (oper)
;; Returns TRUE if OPER can't be restructured - i.e. if it is
;; a constructor term.
    `(not  (s-get-binding ,oper *reachable*)))

(defun s-decompose (eqn  ans)
;; This function decomposes the RHS and LHS terms, and returns
;; a list of the newly formed terms. However, if the two terms
;; can't be decomposed then NIL is returned.
    (let  (( lhs       (s-get-eqn-lhs   eqn ))
           ( rhs       (s-get-eqn-rhs   eqn )))
       ( cond ((same-oper? lhs rhs) 
                    (construct-new lhs rhs ans))
              ((and (var? rhs) (not (occurs-in rhs lhs)))
                   (let ((bind  ( s-get-binding rhs ans)))
                     (if bind 
                         (s-decompose (make-eqn  lhs bind) ans)
                         (forced-decompose lhs rhs ans)))))))


(defun forced-decompose (s t1 ans)
;; This function is called when T1 is a variable, and it forces
;; a structure similar to S on T1, and then it tries to decompose.
    (cond ((constant? s)
              (cons nil (normal-form-sub (s-add-binding t1 s ans) nil)) )
          ((is-constructor (operator s))
              (let*  ((aans (s-make-copy s))
                      (nrhs (car aans))
                      (nsub (cdr aans))
                      (all-sub (s-app-list  t1 nrhs ans))
                      (nans (normal-form-sub all-sub nil)))
                 (cond ((null all-sub) nil)
                       ((var? nrhs)    (cons nil nans))
                       ( t             (construct-new s nrhs nans)) ) ) )
           ( t (let* ((op   (operator s))
                      (args (form-args (sub1 (length s))))
                      (nrhs (make-term op args))
                      (nans (normal-form-sub
                                (s-add-binding t1 nrhs ans) nil)))
                  (construct-new s nrhs nans) ) ) ) )

(defun s-app-list (var term lst)
;; Function used exclusively by FORCED-DECOMPOSE.
    (cond ((equal var term)  lst)
          ( t    (s-add-binding var term lst)) ) )

(defun form-args (val)
;; This function returns a list of VAL new variables.
    (cond ((zerop val) nil)
          ( t  (cons (s-new-var) (form-args (sub1 val))))))

(defun s-make-copy (term)
;; This function is used to make a copy of TERM with the
;; condition that whenever a subterm is seen in which the
;; outer operator is not a constructor, then in the result
;; this subterm is replaced by a new variable.
    (cond ((or (var? term) (constant? term))
               (cons term nil))
          ( t
               (let  ((oper (operator  term))
                      (args (arguments term)))
                 (if (not (is-constructor oper))
                     (let ((new  (s-new-var)))
                        (cons new (list (cons new term))))
                     (do* ((alst     args       (cdr alst))
                           (arg      (car alst) (car alst))
                           (cpy      (s-make-copy  arg)
                                     (s-make-copy  arg))
                           (ntrm     (car  cpy) (car cpy))
                           (nsub     (cdr  cpy) (cdr cpy))
                           (coll-ans  nsub      (append  nsub  coll-ans))
                           (coll-trm (list ntrm)
                                     (append coll-trm (list ntrm))))
                          ((null (cdr alst))  
                            (cons (make-term oper coll-trm) coll-ans))))))))


(defun try-forces( s t1 ans)
;; This function checks if a forced UNIFY or DECOMPOSE
;; can be appiled on S and T. If so, it returns the new
;; set of equations and answers, else
    (cond ((var? s)
             (let ((temp  (forced-unify s t1 ans)))
                (if temp (cons nil temp) nil )))
          ((is-unreachable s t1) nil)
          ((is-constructor (operator s))
             (let ((eqn  (make-eqn  s t1)))
                (s-decompose eqn  ans)))
          (t (let ((temp (make-eqn  s t1)))
                (cons (list temp) ans)))))



(defun s-restructure (eqn  ans)
;; This function returns a list of all the possible top level
;; restructures of the equation represented by eqn .
;; The answer returned is a list, such that each element of it
;; has two parts, the first one is the list of equations, and
;; the other the new answer after all forced-unify and decompose
;; has been done.
;; This function makes use of the data-structure $OP_RULES to 
;; get the set of rules that can possibly restructure a given
;; operator.
    (let* ((lhs  (s-get-eqn-lhs      eqn ))
           (rhs  (s-get-eqn-rhs      eqn ))
           (op1  (operator         lhs))
	   (tttt (output-trace lhs rhs op1 ans))
           (temp (get-rules-with-op  op1  nil))
           (temp (delete-unwanted temp)))
           ;; Get the list of rules with OP1
      (prog (lst-of-rules n-rule c-rule c-rlhs c-rrhs cond1 solutions)
          (setq  solutions      nil)
          (setq  lst-of-rules   temp)
          (if (null temp) (return (list (cons nil ans))))
        again
          (setq  n-rule   (car lst-of-rules))
          (setq  c-rule   (make-new-rule (lhs n-rule) (rhs n-rule) (ctx n-rule)
					 (rule-source n-rule)))
          (setq  c-rlhs   (get-rule-lhs c-rule))
          (setq  cond1    (get-rule-cond c-rule))
          (setq  c-rrhs   (get-rule-rhs c-rule))
          (let*  ((temp1  (one-rule-res lhs c-rlhs  ans cond1))
                  (eqns1  (car temp1))
                  (ans1   (cdr temp1))
                  (temp2  (try-forces c-rrhs rhs ans))
                  (eqns2  (car temp2))
                  (ans2   (cdr temp2))
                  (a-eqns (append eqns2 eqns1))
                  (a-ans  (normal-form-sub (append-list ans2 ans1) nil)))
              (if (and a-ans temp1 temp2)
                  (push (cons a-eqns (retrieve a-ans)) solutions)))
          (setq  lst-of-rules (cdr lst-of-rules))
          (if (null lst-of-rules) (return solutions)
              (go again)))))

(defun retrieve (ans)
   (if (equal ans '(())) nil
       ans))

(defun one-rule-res (s t1 ans cond1)
;; This function is called by RESTRUCTURE, when the term bound
;; to S has  to be restructured using the lhs of a rule, which
;; is bound to T1. ANS  gives the partial  answer, while COND1
;; has the condition in case the rule is conditional.
    (let   ((temp1   (s-decompose   (make-eqn  s  t1)  ans)))
       (if cond1
           (let*  ((eqns1   (car  temp1))
                   (ans1    (cdr  temp1))
                   (neqn    (make-eqn  cond1  '(true)))
                   (e-final (cons      neqn    eqns1)))
                (cons  e-final  ans1))
           temp1)))
           



(defun construct-new (s t1 ans)
;; This function constructs a list of equations when the terms
;; S and T are decomposed.
    (if (constant? s) (cons nil ans)
      (loop with new-ans = ans
	    with new-eqns = nil
	    with temp = nil
	    for s-arg in (arguments s)
	    as  t-arg in (arguments t1)	 do
	    (if (setq temp 
                      (try-forces (s-rewrite-with-subs s-arg new-ans)
                                  (s-rewrite-with-subs t-arg new-ans) 
                                   new-ans))
                  (setq new-ans (cdr temp)
			new-eqns (nconc new-eqns (car temp)))
	      (return nil))
	    finally (return (cons new-eqns new-ans)))))

(defun form-init-eqn-lst (lhs rhs)
;; Given an equation of the form LHS --?--> RHS this function
;; converts it into a list of two equations of the form :-
;;     LHS --?--> Z,
;;     RHS --?--> Z, where Z is a new variable.
;; The new equations have to be tried for forced DECOMPOSE and
;; UNIFY before they can be used as the starting point.
    (let*  ((new   (s-new-var))
            (lhs1  (flat-term lhs))
            (rhs1  (flat-term rhs))
            (lhs1  (s-rewrite-with-subs lhs1 nil))
            (tt1   (try-forces lhs1 new nil))
            (eqs   (car tt1))
            (ans   (cdr tt1))
            (rhs1  (s-rewrite-with-subs rhs1 ans))
            (tt2   (try-forces rhs1 new ans))
            (eq2   (car tt2))
            (nans  (cdr tt2))
            (aeqns (append eqs eq2))
            (elst  (make-eqn-lst nil (car aeqns)(cdr aeqns))))
           (if (null tt2) nil
               (make-node 1 elst nans))) )



(defun delete-unwanted (rlst)
;; This function is used to delete all the rules that are
;; not to be used for restructuring. The rules which need
;; not  be used are stored by numbers in a variable named
;; *UNWANTED*, which is used by this function.
    (cond ((null *unwanted*) rlst)
          ( t  (do*  ((lst    rlst    (cdr lst))
                      (nlst   nil ))
                     ((null lst) nlst)
                     (let ((temp  (check-if-needed (car lst))))
                        (if temp (setq nlst (cons temp nlst))) ) ) )))



(defun check-if-needed (rule)
;; This function returns the RULE if this one needs to be used
;; for restructuring, else it returns NIL.
    (let  ((num   (ruleno  rule)))
      (if (memq num *unwanted*) nil rule)))


(defun show-res-rules (rule_set)
    (loop for rule in rule_set do
          (progn 
            (format t "Rule ~a is -  " (ruleno rule) )
            (if (ctx rule)
                (format t " ~a : " (ctx rule))
                (format t "      "))
            (format t " ~a --> ~a ~%" (lhs rule) (rhs rule))))
    (format t "Give rule numbers not needed for restructuring ~%")
    (format t "           Enter NIL if all rules are required    ")
    (setq *unwanted* (read)))
