;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)

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
  (if (member op2 (cdr (assoc op1 $glob_prec))) then t
      elseif (member op1 (cdr (assoc op2 $glob_prec))) then nil
      else (> (default-precedence op1) (default-precedence op2))))

(defun default-precedence (op1)
  ; Return the default precedence value of op1.
  ; The following defualt precedence relations is assumed:
  ;    6.  {non-constant-skolem-functions}
  ;    5.  {prdicates, functions} >
  ;    4.  {constant-funcs} > 
  ;    3.  {booleans} >
  ;    2.  $anspred >
  ;    1.  {constructors} >
  ;    0.  {constant-constructors}
  (cond 
   ((memq op1 $constructors) (if (is-constant op1) 0 1))
   ((memq op1 '(true false)) 0)
   ((eq op1 $anspred) 2)
   ((is-bool-op op1) 3)
   ((predicatep op1) 5)
   ((is-constant op1) 4)
   ((skolemp op1) 6)
   (t 5)))

(defun pc-grt-prec (op1 op2)
  ; Checks if OP1 > OP2 in the precedence.
  (if (member op2 (cdr (assoc op1 $glob_prec))) then t
      elseif (member op1 (cdr (assoc op2 $glob_prec))) then nil
      else (let ((n1 (default-precedence op1))
		 (n2 (default-precedence op2)))
	     (if (> n1 n2) then t
		 elseif (< n1 n2) then nil
		 elseif (numberp op1)
		 then (if (numberp op2) (> op1 op2) nil)
		 elseif (numberp op2) then t
		 elseif (eq op1 op2) then nil
		 elseif (alphalessp op1 op2) then nil
		 elseif (alphalessp op2 op1) then t
		 elseif (symbolp op1)
		 ;; at this point, op1 and op2 have the same print name.
		 then (if (boundp op1)
			  then (if (boundp op2) 
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
    (loop for xa in $eqop_list do
	  (if (member op xa) then (setq temp xa) (return nil)))
    (if temp then temp else (ncons op))))

(defun equiv-ops (op)
  ; Returns a list of operators equivalent to OP in the precedence.
  ; Note: If only one operaotr in the list, i.e., OP itself, then
  ; the empty list will be returned.
  (loop for xa in $eqop_list if (member op xa) return xa))

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
     (loop for op in (equiv-ops op1) do
	(if (neq op op1) then
	   (if (setq l1 (assoc op $glob_prec)) 
		then (rplacd l1 tail)
		else (nconc $glob_prec (ncons (cons op tail))))))))

(defun ok-prev-rules (op &aux (temp t))
  ;  Called when the user introduces status for an operator in
  ; the middle.  This may upset the orientation of some of the
  ; previous rules and it may not be wise to proceed so first
  ; ask the user and flag this.
  (loop for xa in $rule-set if (not (predicatep (op-of (lhs xa))))
	do (if (member op (op-list (lhs xa)))
	      then
		(if (not (lrpo (lhs xa) (rhs xa)))
		    then (terpri)
			 (princ "The following rule is not orientable now:")
			 (terpri) (write-rule xa)
			 (if (not (ok-to-continue))
			     then (setq temp nil)
				  (return nil)))))
  (if temp then (princ (uconcat "Operator, " op ", given status: "))
	(princ (get-status op)) (terpri))
  temp)

(defun remove-eq-op (ops)
  ;  If op1 and op2 are equivalent and both in OPS, then remove one of them.
  (let (op ops2)
     (loop while ops do 
	(setq op (pop ops))
	(if (> (get-arity op) 1) then
	   (loop for o in (equiv-ops op) do 
		(setq ops (delete o ops)
		      ops2 (delete o ops2))))
       (setq ops2 (append1 ops2 op)))
   ops2))

(defun trans-status (op2 op1)
  (let ((status (get-status op1)))
     (loop for op in (ops-equiv-to op2) do
       (if (not (numberp op)) then
 	(setq $st_list (cons op $st_list))
	(set-status op status)))))

(defun status-candidates (ops)
  ;  Return those operators in OPS that have not status and
  ; their arity is bigger than 1.
  (loop for op in ops 
	if (and (> (get-arity op) 1) (not (get-status op))) 
	collect op))



