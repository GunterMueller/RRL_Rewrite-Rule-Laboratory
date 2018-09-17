;;; -*- Mode: LISP; Syntax: Zetalisp; Package: FRANZ; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-lispm (include datamacs.l)
(declare (special num-trans))

(defun aclrpo (t1 t2)
  ; Called when some operators are ac in the system. 
  ; Return t iff t1 is bigger than t2.
  ; Suppose t1 and t2 are already flattened.
  (if (not (and (has-acop t2) (has-acop t1)))
     then (pure-lrpo t1 t2)
     elseif (prec-consistent (union (op-list t1) (op-list t2)))
     then (let ((t11 (distr-ac-order t1)) (t22 (distr-ac-order t2)))

	     (if (equal (cdr t11) (cdr t22)) 
		 then (greaterp (car t11) (car t22))
		 else (pure-lrpo (cdr t11) (cdr t22))))))

(defun prec-consistent (ops &aux acops min min2)
  ; return t if
  ;  (a) there are at most two ac-operators;
  ;  (b) one of ac-op is minial, except unary or nullary operators;
  ;  (c) the other ac-op is second minimal.
  (setq ops (loop for op in ops 
		  if (and (not (is-bool-op op))
			  (> (get-arity op) 1)) collect op)
	acops (loop for op in ops if (ac-op-p op) collect op))
  (if (null (cddr acops)) then
      (if (cdr acops) then 
	  (if (grt-prec (first acops) (second acops))
	      then (setq min (second acops) 
			 min2 (first acops))
	      elseif (grt-prec (second acops) (first acops))
	      then (setq min2 (second acops) 
			 min (first acops)))
	  else (setq min (first acops)))
      (if min then
	  (setq ops (set-diff ops acops))
	  (if min2
	      then (loop for op in ops always (grt-prec op min2))
	      else (loop for op in ops always (grt-prec op min))))))

(defun distr-ac-order (term)
   (setq num-trans 0
         term (ac-distri term))
   (cons num-trans term))

(defun ac-distri (term &aux args)
  ; The same as using the rule "(x f y) g z ---> (x g z) f (y g z)"
  ; to simply TERM where f > g in the precedence.
  (if (or (variablep term) (null (args-of term))) then term else
     (setq args (mapcar 'ac-distri (args-of term)))
     (loop with op1 = (op-of term) with arg with args1 while args do
	    (setq arg (pop args))
	    (if (or (variablep arg) (null (args-of arg)))
		then (setq args1 (append1 args1 arg))
		elseif (or (grt-prec op1 (op-of arg))
			   (and (eqops op1 (op-of arg)) 
				(alphalessp (op-of arg) op1))) 
		then (setq args (loop for arg2 in (args-of arg) collect
				       (compress-flat op1
					   (append args1 (cons arg2 args))))
			   term (compress-flat (op-of arg) args)
			   num-trans (add1 num-trans))
		     (return (ac-distri term))
		else (setq args1 (append1 args1 arg)))
	     finally (return (compress-flat op1 args1)))))
