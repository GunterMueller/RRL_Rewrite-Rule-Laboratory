;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

(defun print-sugg-info (t1 t2 sugg oneway uncondi &aux l3)
    (terpri) (princ "  To prove:  ")
    (write-term t1) (princ "  >  ") (write-term-bool t2) (terpri)  
    (if (not oneway) then (princ "        or:  ")
        (write-term-bool t1) (princ "  <  ") (write-term-bool t2) (terpri))
    (if sugg then
	(princ "  Here are some precedence suggestions:") (terpri)
	(loop for xa in sugg as i from 1 do
	    (if l3 
	      then (if (< i 10) then (tab 31) else (tab 30))
		   (princ (uconcat "      " i ".  " (print-name (car xa))
					  " > " (print-name (cadr xa))))
		   (terpri) (setq l3 nil) 
	      else (if (< i 10) then (princ " "))
		   (princ (uconcat "      " i ".  " (print-name (car xa))
					  " > " (print-name (cadr xa))))
	           (if oneway then (terpri) else (setq l3 t))))
        (princ "Either type a list of numbers or") (terpri)
     elseif (and oneway uncondi (is-subset (var-list t1) (var-list t2))) 
       then (princ "I have no precedence suggestions.  ") 
	    (princ "You wanted to orient it from left to right,") (terpri)
	    (princ "    however, it may be orientable in the other")
	    (princ " direction. ") (terpri)
	    (princ "Try doing Twoway, Equiv or Status.") (terpri) (terpri)
       else (princ "I have no precedence suggestions.  ") (terpri)
	    (princ "Try doing Equiv or Status.") (terpri) (terpri)
    )
    (princ 
"Type Abort, Display, Drop, Equiv, LR, MakeEq, Operator, Postpone, Quit, RL,"
)   (terpri)
    (princ "     Status, Superpose, Twoway, Undo or Help.")
    (terpri) (princ "RRL>KB> "))

(defun try-sugg-prec (t1 t2 l3 sugg oneway)
   (prog (l1 l2 good)
	; Read in suggestions and reseve old $glob_prec.
	(save-words (list l3))
        (setq l1 (if (is-empty-line $in-port) 
	          then (save-word-end "")
		       (ncons l3)
		  else (cons l3 (read-args $in-port)))
	      l3 (copy $glob_prec))

	; Test whether the suggestions are good.
	(loop for i in l1 do
	    (if (and (numberp i) 
	        (setq l2 (nthelem i sugg))) then
	       (if (grt-prec (cadr l2) (car l2))
		   then (princ "Invalid number, try again.") (terpri)
			(setq $glob_prec l3)
		        (return)
		   else (add-sugg (car l2) (cadr l2))
		        (setq good t)))
 	)
	(if good then
	    (push-history)
  	    ; Orient the equation using the new precedence.
	    (if (setq l1 (try-to-orient2 t1 t2 oneway))
               then (return l1)
	       else (terpri) (princ "Sorry did not work, try again.") (terpri)
	    )
        )
        (return nil)))	

(defun sugg-prec (l1 l2 oneway &aux l3)
  ; L1 and L2 are two lists of operators (one of T1, one of T2
  ; to make a rule T1 -> T2).  Called when LRPO cannot orient
  ; and seek to increment the precedence relation on function
  ; symbols to make this rule orientable.  This returns a list
  ; of pairs of unrelated operators so that the user can choose
  ; which suggestions he wants.
  (setq l1 (remove-eq-op l1)  
	  l2 (remove-eq-op l2))
  (loop for opl in l1 do
	  (loop for opr in l2 do
		(if (or (is-rel-prec opl opr)
			(member (list opl opr) l3))
		    then ()
		    else (setq l3 (append1 l3 (list opl opr)))
			 (if (not oneway)
			     then (nconc l3 (ncons (list opr opl)))))))
   l3)

(defun remove-sugg (sugg)
  ;  Remove the suggestions in "sugg" that have already 
  ; a relation in the precedence.
  (loop for s in sugg if (not (is-rel-prec (car s) (cadr s))) collect s))

(defun add-sugg (op1 op2)
  ;  SUGG is a list of two operators (op1 op2).  Adds the relation
  ; op1 > op2 in the precedence and makes sure the global
  ; varaible $GLOB_PREC is updated correctly.
  (cond ((null $glob_prec) 
         (setq $glob_prec (ncons (cons op1 (ops-equiv-to op2)))))
        ((assoc op1 $glob_prec) (add-sugg1 op1 op2))
	(t (nconc $glob_prec (ncons (ncons op1)))
	   (add-sugg1 op1 op2)))
  (update-by-eq op1))

(defun add-sugg1 (op1 op2)
  ; Local function.  Called by ADD-SUGG.
  (loop for xa in $glob_prec do
     (if (member op1 xa) then
	 (loop for o2 in (ops-equiv-to op2) do (add-at-end xa o2))
	 (loop for o2 in (assoc op2 $glob_prec) do (add-at-end xa o2)))))
