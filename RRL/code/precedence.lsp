;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")



; To orient rules, function symbols must have some precedence relation
; and there is a concept of equivalent operators.  All this information
; is stored in two global variables which are:
;   $GLOB_PREC	A list of list of operators. The first operator
;               in each list is greater in precedence than the other
;               operators in the list.
;   $EQOP_LIST	A list of lists of operators.  All the operators in
;               each list are equivalent in precedence.
; If an operator has status, that information is stored on the property
; list of the operator itself (under status - rl or lr).  There is also a
; need to maintain a global list $ST_LIST which contains a list of all
; operators that have been assigned status.  This is needed because when
; the system is initialized, all operators should have no status.
; It should be noted that equivalent operators have the same status.
; When the precedence relation is extended, information must be updated
; correctly.
;
; The following functions maintain the precedence list and can update them.
;

(defun grt-prec (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  (if* (member op2 (cdr (assoc op1 $glob_prec))) then t
      elseif (member op1 (cdr (assoc op2 $glob_prec))) then nil
      else (> (default-precedence op1) (default-precedence op2))))

(defun default-precedence (op1)
  ; Return the default precedence value of op1.
  ; The following defualt precedence relations is assumed:
  ;    6.  {non-constant-skolem-functions}
  ;    5.  {prdicates, functions} >
  ;    4.  {constant-funcs} > 
  ;    3.  {booleans} >
  ;    2.  not, $anspred >
  ;    1.  {constructors} >
  ;    0.  {constant-constructors}
  (cond 
   ((memq op1 $constructors) (if (is-constant op1) -1 0))
   ((memq op1 '(true false)) -1)
   ((memq op1 $fri-ops) 1)
   ((eq op1 $anspred) 2)
   ((eq op1 'not) 2)
   ((is-bool-op op1) 3)
   ((is-constant op1) 4)
   ((predicatep op1) 5)
   ((skolemp op1) 6)
   (t 5)))

(defun pc-grt-prec (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  (if* (member op2 (cdr (assoc op1 $glob_prec))) then t
      elseif (member op1 (cdr (assoc op2 $glob_prec))) then nil
      else (let ((n1 (default-precedence op1))
		 (n2 (default-precedence op2)))
	     (if* (> n1 n2) then t
		 elseif (< n1 n2) then nil
		 elseif (numberp op1)
		 then (if* (numberp op2) (> op1 op2) nil)
		 elseif (numberp op2) then t
		 elseif (eq op1 op2) then nil
		 elseif (alphalessp op1 op2) then nil
		 elseif (alphalessp op2 op1) then t
		 elseif (symbolp op1)
		 ;; at this point, op1 and op2 have the same print name.
		 then (if* (boundp op1)
			  then (if* (boundp op2) 
				   (> (symeval op1) (symeval op2)) t)
			  elseif (boundp op2) then nil
			  else nil)))))

(defun eqops (l1 l2)
  ; Checks if L1 and L2 are equivalent in the precedence.
  (member l2 (ops-equiv-to l1)))

(defun ops-equiv-to (op)
  ; Returns a list of operators equivalent to OP in the precedence.
  ; Note: at least (OP) will be returned.
  (let (temp)
    (sloop for xa in $eqop_list do
	  (if* (member op xa) then (setq temp xa) (return nil)))
    (if* temp then temp else (ncons op))))

(defun equiv-ops (op)
  ; Returns a list of operators equivalent to OP in the precedence.
  ; Note: If only one operaotr in the list, i.e., OP itself, then
  ; the empty list will be returned.
  (sloop for xa in $eqop_list if (member op xa) return xa))

(defun is-rel-prec (op1 op2)
  ; Check if OP1 and OP2 are related in precedence.
  (or (eqops op1 op2)
      (member op1 (cdr (assoc op2 $glob_prec)))
      (member op2 (cdr (assoc op1 $glob_prec)))
      (neq (default-precedence op1) (default-precedence op2))))

(defun update-by-eq (op1)
  ;  Update $GLOB_PREC such each operator equivalent to OP1 has
  ; the same precedence relation with other operators.
  (let ((tail (cdr (assoc op1 $glob_prec))) l1)
     (sloop for op in (equiv-ops op1) do
	(if* (neq op op1) then
	   (if* (setq l1 (assoc op $glob_prec)) 
		then (rplacd l1 tail)
		else (nconc $glob_prec (ncons (cons op tail))))))))

(defun ok-prev-rules (op &aux (temp t))
  ;  Called when the user introduces status for an operator in
  ; the middle.  This may upset the orientation of some of the
  ; previous rules and it may not be wise to proceed so first
  ; ask the user and flag this.
  (sloop for xa in $rule-set if (not (predicatep (op-of (lhs xa))))
	do (if* (member op (op-list (lhs xa)))
	      then
		(if* (not (lrpo (lhs xa) (rhs xa)))
		    then (terpri)
			 (princ "The following rule is not orientable now:")
			 (terpri) (write-rule xa)
			 (if* (not (ok-to-continue))
			     then (setq temp nil)
				  (return nil)))))
  (if* temp then (princ (uconcat "Operator, " op ", given status: "))
	(princ (get-status op)) (terpri))
  temp)

(defun remove-eq-op (ops)
  ;  If op1 and op2 are equivalent and both in OPS, then remove one of them.
  (let (op ops2)
     (sloop while ops do 
	(setq op (pop ops))
	(if* (> (get-arity op) 1) then
	   (sloop for o in (equiv-ops op) do 
		(setq ops (delete o ops)
		      ops2 (delete o ops2))))
       (setq ops2 (append1 ops2 op)))
   ops2))

(defun trans-status (op2 op1)
  (let ((status (get-status op1)))
     (sloop for op in (ops-equiv-to op2) do
       (if* (not (numberp op)) then
 	(setq $st_list (cons op $st_list))
	(set-status op status)))))

(defun status-candidates (ops)
  ;  Return those operators in OPS that have not status and
  ; their arity is bigger than 1.
  (sloop for op in ops 
	if (and (> (get-arity op) 1) (not (get-status op))) 
	collect op))



;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


;#+franz (include "datamacs.l")
;#-franz (in-package "USER")

(defun print-sugg-info (t1 t2 sugg oneway uncondi &aux l3)
    (terpri) (princ "  To prove:  ")
    (write-term t1) (princ "  >  ") (write-term-bool t2) (terpri)  
    (if* (not oneway) then (princ "        or:  ")
        (write-term-bool t1) (princ "  <  ") (write-term-bool t2) (terpri))
    (if* sugg then
	(princ "  Here are some precedence suggestions:") (terpri)
	(sloop for xa in sugg as i from 1 do
	    (if* l3 
	      then (if* (< i 10) then (tab 31) else (tab 30))
		   (princ (uconcat "      " i ".  " (print-name (car xa))
					  " > " (print-name (cadr xa))))
		   (terpri) (setq l3 nil) 
	      else (if* (< i 10) then (princ " "))
		   (princ (uconcat "      " i ".  " (print-name (car xa))
					  " > " (print-name (cadr xa))))
	           (if* oneway then (terpri) else (setq l3 t))))
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
    (princ "     Status, Twoway, Undo or Help.")
    (terpri) (princ "RRL>ORDER> "))

(defun try-sugg-prec (t1 t2 l3 sugg oneway)
   (prog (l1 l2 good)
	; Read in suggestions and reseve old $glob_prec.
	(save-words (list l3))
        (setq l1 (if* (is-empty-line $in-port) 
	          then (save-word-end "")
		       (ncons l3)
		  else (cons l3 (read-args $in-port)))
	      l3 (copy $glob_prec))

	; Test whether the suggestions are good.
	(sloop for i in l1 do
	    (if* (and (numberp i) 
	        (setq l2 (nthelem i sugg))) then
	       (if* (grt-prec (cadr l2) (car l2))
		   then (princ "Invalid number, try again.") (terpri)
			(setq $glob_prec l3)
		        (return)
		   else (add-sugg (car l2) (cadr l2))
		        (setq good t)))
 	)
	(if* good then
	    (push-history)
  	    ; Orient the equation using the new precedence.
	    (if* (setq l1 (try-to-orient2 t1 t2 oneway))
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
  (sloop for opl in l1 do
	  (sloop for opr in l2 do
		(if* (or (is-rel-prec opl opr)
			(member0 (list opl opr) l3))
		    then ()
		    else (setq l3 (append1 l3 (list opl opr)))
			 (if* (not oneway)
			     then (nconc l3 (ncons (list opr opl)))))))
   l3)

(defun remove-sugg (sugg)
  ;  Remove the suggestions in "sugg" that have already 
  ; a relation in the precedence.
  (sloop for s in sugg if (not (is-rel-prec (car s) (cadr s))) collect s))

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
  (sloop for xa in $glob_prec do
     (if* (member0 op1 xa) then
	 (sloop for o2 in (ops-equiv-to op2) do (add-at-end xa o2))
	 (sloop for o2 in (assoc op2 $glob_prec) do (add-at-end xa o2)))))
