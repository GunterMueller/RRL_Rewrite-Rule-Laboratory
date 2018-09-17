;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#+franz (include "datamacs.l")
#-franz (in-package "USER")

(defun auto-kb ()
  (let ( #+franz (temp (set-timer)))
    (if* (or $eqn-set $rule-set) then
     (setq $akb_flag t
	   $max-arity (apply 'max (sloop for op in $operlist
				    collect (get-arity op))))
     (if* (equal '*noway* (*catch 'akb (start-kb))) then
	 (princ "Sorry. I cannot complete your system.") (terpri) (terpri)
#+franz     (format t "Total processor time used = ~f sec" (get-time temp)) 
         (terpri))
     (setq $akb_flag nil)
     else (princ "Sorry. The system is empty.") (terpri))))  

(defun auto-orient (eqn t1 t2 sugg oneway)
  ;  Trying to prove t1 > t2 or t2 > t1 (if* not ONEWAY) automatically.
  (prog (ops memory dup-prec dup-eqop)
     (cond ((and (= $newop-first 1) (null (ctx eqn)) 
		 (can-have-new-op eqn t1 t2))  nil)
	   ($auto-sugg (setq ops (cdr $auto-sugg)
	 	 	     memory (car $auto-sugg)
			     $auto-sugg nil))	   
	   (t (setq ops (status-candidates (op-list t2))
		    memory (nconc (sloop for op in sugg collect 0)
					  (sloop for op in ops collect 0)))))

     (if* (null memory) then (return (postpone-or-undo eqn)))
     (setq dup-prec (copy $glob_prec) dup-eqop (copy $eqop_list))

     loop1
     (if* (*catch 'add-one
	    (progn (setq memory (add1-modulo-n memory 2)) nil))
	then (cond ((< (length $history) $max-history) 
		    (setq $max-history (sub1 $max-history)) (undo))
		   (t (postpone-or-undo eqn) (return 'p))))

     (cond ((is-bad-sugg memory sugg sugg ops)
	    (setq $glob_prec (copy dup-prec) $eqop_list (copy dup-eqop)) 
	    (sloop for op in ops do 
		 (sloop for o in (ops-equiv-to op) do (rem-status o)))
	    (go loop1))
	   ((post-for-while eqn ops)
	    (sloop for op in ops do 
		 (sloop for o in (ops-equiv-to op) do (rem-status o)))
	    (setq $glob_prec (copy dup-prec) 
		  $eqop_list (copy dup-eqop)
	   	  memory (sub1-modulo-n memory 2))
	    (if* $history1 then
		(rplaca $history1 (cons sugg (cons memory ops)))
		(push-history))
	    (return 'p))	    	
	   ((lrpo t1 t2) 
	    (end-auto-order sugg ops memory)
	    (return 1))
	   ((and (not oneway) (lrpo t2 t1))
	    (end-auto-order sugg ops memory)
	    (return 2))
	   (t (setq $glob_prec (copy dup-prec) $eqop_list (copy dup-eqop))
	      (sloop for op in ops do 
		 (sloop for o in (ops-equiv-to op) do (rem-status o)))
	      (go loop1)))))

(defun can-have-new-op (eqn t1 t2)
   (let ((var2 (var-list t2)))
      (if* (and (null $polynomial)
	       (< (length var2) $max-arity)
	       (> (length (op-list t2)) 1) 
	       (> (length (op-list t1)) 1)) then
	 (cond ((< (length $history) $max-history)
	        (setq $max-history (sub1 $max-history))
		(princ "I undo it.") (terpri) (undo))
	       ((or (member-term t1 $newop-terms)
		    (member-term t2 $newop-terms)) 
		(princ "I undo it.") (terpri) (undo))
	       (t 
		 (push t1 $newop-terms)
		 (push t2 $newop-terms)
		 (setq $auto-sugg nil)
		 (princ "New operator is introduced.") (terpri) 
	         (add-operator eqn (var-list t1) var2 nil))))))

(defun postpone-it (eqn)
   ; return 'P iff EQN can be postponed.
   (cond ((and (> $newrule-num 0) (< (length $post-set) $post-max)) 
	  (princ "The equation is postponed.") (terpri)
	  (setq $post-set (cons eqn $post-set))
	   'p)
	 ((< $post-posi 3)
	  (setq $post-posi (1+ $post-posi)
		$eqn-set (nconc $post-set $eqn-set (ncons eqn))
		$post-set nil)
	  (princ "The equation is postponed.") (terpri)
	  'p)))

(defun post-for-while (eqn ops)
   ; return t if EQN has been postponed, otherwise, return nil.
   (cond ((or (= $post-posi 1)
	      (and (= $post-posi 2) 
	   	   (sloop for op in ops thereis (get-status op))))
	  (postpone-it eqn))))

(defun postpone-or-undo (eqn)
   ; if EQN can be postponed then postpone it, otherwise, undo.
    (cond ((postpone-it eqn) (setq $history1 nil) 'p)
	  ((= $newrule-num 0) (terpri)
	   (princ "No new rule has produced since this equation was postponed.")
	   (princ "I undo it.") (terpri)
	   (if* $polynomial then
	       (setq $eqn-set (append1 $post-set eqn)
		     $post-set nil
		     $newrule-num 0
		     $ordering 's
		     $post-bound (+ $post-bound $post-bound))
	       else
	       (undo)))
	  (t (terpri) (princ "WARNING: ") (princ $post-max) 
	     (princ " equations have been postponed. I undo it.") (terpri)
	     (undo))))

(defun is-bad-sugg (auto-sugg pairs sugg ops)
   ;  Returns "t" if the current suggestion $AUTO-SUGG is not good.
   (let (op1 op2 bad)
     (sloop for num in auto-sugg as i from 1 do
        (if* pairs then 
	  (setq op2 (pop pairs)
		op1 (car op2) 
		op2 (cadr op2))
	  (if* (= $pre-first 2) then (cond ((= num 1) (setq num 2))
				              ((= num 2) (setq num 1))))
	  (caseq num
	    (0 nil)
	    (1 (sloop for xa in sugg as n from 1 do
		    (cond ((equal n i) (return))
			  ((and (equal (car xa) op2)
				(equal (cadr xa) op1)) (return (setq bad t)))
	       )    )
	       (if* bad then (return))
	       (if* (setq bad (auto-make-equi op1 op2)) then (return)))
	    (2 (if* (setq bad (auto-add-prec op1 op2)) then (return)))
	  )
	 else
	  (setq op1 (pop ops))
	  (if* (= $rl-first 2) then (cond ((= num 1) (setq num 2))
				             ((= num 2) (setq num 1))))
	  (caseq num
	    (0 nil)
	    (1 (if* (setq bad (auto-add-status op1 'lr)) then (return)))
	    (2 (if* (setq bad (auto-add-status op1 'rl)) then (return))))))
   bad))

(defun auto-make-equi (op1 op2)
  ; Check the status of OP1 and OP2. Try to make OP1 and OP2 to be 
  ; equivalent and consistent with their status. 
  (cond ((eqops op1 op2) nil)
	((is-rel-prec op1 op2) t)
	((and (eq $eq-arity 'n) (same-arity op1 op2)) t)
	((equal (get-status op1) (get-status op2)) (add-equ op1 op2) nil)
	((get-status op1)
	 (if* (get-status op2) then t
	  elseif (intersection (ops-equiv-to op2) $commutative) then t
	  else (trans-status op2 op1) (add-equ op1 op2) nil
	))
	(t (if* (intersection (ops-equiv-to op1) $commutative) then t
	    else (trans-status op1 op2) (add-equ op2 op1) nil))))

(defun auto-add-prec (op1 op2)
  ;  Checking the consistence of the precedence if op1 > op2 is added
  ;	    to the precednece. If it is, then accept op1 > op2.
  (cond ((eqops op1 op2) t)
	((grt-prec op2 op1) t)
	((and (= (get-arity op1) 0) (> (get-arity op2) 0)) t)
	(t (add-sugg op1 op2) nil)))

(defun auto-add-status (op status)
  ; Check the consistence when adding STATUS to OP.
  ; If it is, then accept this adding.
  (cond ((get-status op) (if* (not (equal (get-status op) status)) then t))
	((intersection (ops-equiv-to op) $commutative) t)
	(t (sloop for oper in (ops-equiv-to op) do
	      (if* (not (numberp oper)) then
		(setq $st_list (cons oper $st_list))
		(set-status oper status)))
           (if* (not-auto-prev-rules op) then
		(sloop for oper in (ops-equiv-to op) do (rem-status oper))
		t))))

(defun not-auto-prev-rules (op)
  ; Called when introducing status for an operator in
  ; the middle.  This may upset the orientation of some of the
  ; previous rules and it is not wise to proceed. 
  (let (bad)
    (sloop for xa in $rule-set do
	  (if* (and (member op (op-list (lhs xa))) 
		   (not (lrpo (lhs xa) (rhs xa))))
		   then (return (setq bad t))))
    bad))

(defun end-auto-order (sugg ops memory &aux l1)
  ;  Save MEMORY in the history.
  (if* $history1 then
      (rplaca $history1 (cons sugg (cons memory ops)))
      (sloop for num in memory do
	(if* sugg then 
	    (setq l1 (pop sugg))
	    (if* (= $pre-first 2) then
		(cond ((= num 1) (setq num 2)) ((= num 2) (setq num 1))))
	    (caseq num
	      (0 nil)
	      (1 (princ (uconcat "Precedence relation, " (car l1) " = "
				 (cadr l1) ", is added.")) (terpri))
	      (2 (princ (uconcat "Precedence relation, " (car l1) " > "
				 (cadr l1) ", is added.")) (terpri)))
	    else
	    (setq l1 (pop ops))
	    (if* (= $rl-first 2) then (cond ((= num 1) (setq num 2))
					    ((= num 2) (setq num 1))))
	    (caseq num
	      (0 nil)
	      (1 (princ (uconcat "Operator, " l1 ", given status: lr")) 
		 (terpri))
	      (2 (princ (uconcat "Operator, " l1 ", given status: rl")) 
		 (terpri)))))
      (push-history)))
