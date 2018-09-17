(in-package "RRL")

;; use RRL's code for this. <- $op_rules must be correctlys set. - siva
(defun equal-normal-forms (t1 t2 subs)
;; This function checks whether t1 and t2 have the same normal
;; forms. Since partial bindings are not substituted into the
;; equations, they must be done now, before we can check for
;; equality of normal forms.
  (if (not *eager-rewrite*) nil
      (if *s-conditional*
          (equal (norm-ctx (applysubst subs t1))
                 (norm-ctx (applysubst subs t2)) )
          (equal (s-norm-bin t1 subs)
	         (s-norm-bin t2 subs)) ) ) )

; do we need these?
(defun var-or-binding (var lst)
;; This function returns the binding of VAR if it has one,
;; else it returns the variable itself.
   (or (cdr (assoc var lst)) var))

(defun s-norm-bin (term binds &aux l2)
  ;  Works for non-ac, non-commutative only now.
  ;  Used by NORM-INN.  The variables in TERM are bound.
  (if (variablep term)
      then (var-or-binding term binds)
      else
      (setq term (make-term (op-of term)
			    (loop for xa in (args-of term) 
				  collect (s-norm-bin xa binds))))
      (loop for rule in (rules-with-op (op-of term) $op_rules)
	    if (setq l2 (pure-match (lhs rule) term))
	      return (if (cycle-check term) then
			 (if $trace-proof then (push (ruleno rule) $used-rule-nums))
			 (s-norm-bin (rhs rule) l2))
	    finally (return term))))
