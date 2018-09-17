;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "USER")


;;;; #+franzed merge-list as merge is different in common -- siva 9/24

(defun split-alist (alist)
  (sloop for x in alist  collect (car x) into list1 collect (cdr x) into list2
	finally (return (list list1 list2))))

; Following are some general functions. 
;
;       is-subsequence:   returns a string if the other string is a subsequence
;			of the former.
;       add-at-end:     insert an element at the end of a list.
;       pickout:        pick out all the  elements which are satified a
;			condition in a list.
;       ins-lis:        adds element to a list if not in the list.
;       rem-dups:       remove duplicates from a list.
;       n-tuples:       produce n-tuple products.
;       writeln:        write a line at the terminal then begin a new line.
;       set-timer:      Returns a list consisting of the processor time and 
;			the garbage collector time used so far, measured in 
;			seconds.
;       get-time:	Returns the processor time minus the garbage collection
;			time since TIMERREADING was set by set-timer.
; 	help-file:	print out a help file page by page.
;	is-empty-line:  Return t iff the current line is empty.
;	tyipeek-space:  Skip out all space and return a non-space letter.
;	tyipeek-spa-cr: Skip out all space and <CR>.
;	tyi-cr:		Skip the first <CR>.

#+franz
(defun is-subsequence (symbol1 symbol2)
  ; Returns SYMBOL2 if SYMBOL1 is a subsequence of SYMBOL2 
  ; (from the first character on); otherwise, returns NIL.
  ; This function is used in parsing input to determine if it is
  ; a valid response.
  (let ((c1 (getcharn symbol1 1)) (i1 2))
    (if* c1 
      then (sloop for i2 = 1 then (1+ i2) 
	         as c2 = (getcharn symbol2 i2) until #-franz (eq c2 0)
						  #+franz (null c2) do
	          (if* (eq  c1 c2) then 
		     (setq c1 (getcharn symbol1 i1) i1 (1+ i1))
	             (if* #-franz (eq c1 0) #+franz (null c1) then (return symbol2))
	          )
            )
     else symbol2)))

#-franz
(defun is-subsequence(sym1 sym2)
  (let* ((s1 (symbol-name sym1))
	 (s2 (symbol-name sym2))
	 (l1  (length s1))
	 (l2 (length s2)) tmp)
    (cond ((not (char= (char s1 0) (char s2 0))) nil)
          ((= l1 l2) (string= s1 s2))
	  (t (if* (< l2 l1)
		 (setq tmp s2 s2 s1 s1 tmp l1 l2)) ; make s1 the shorter
	     (sloop with pos = 0
		   for i from 0 to (1- l1)
		   as c = (char s1 i) always
		   (setq pos (sloop for j from pos to (1- (length s2))
				   do (if* (char= c (char s2 j)) (return j))))
		   )))))

(defun is-subseq-list (l1 l2)
  ; Same as the is-subsequence, except that the inputs are lists instead of symbols.
  ; l1 and l2 are integer lists in decreasing order.
  (sloop with c1 = (pop l1)
	for c2 in l2
	if (eq c1 c2) do (if* l1 (setq c1 (pop l1)) (return t))
	else if (> c1 c2) return nil
	finally (return (null c1))))

(defun non-decreasing-seq (l1)
  ; return t iff l1 is a non-decreasing sequence of integers.
  (sloop for pre in l1 as next in (cdr l1) always (>= pre next)))

(defun add-at-end (lis elem)
  ; If ELEM is in LIS, returns LIS with ELEM added at end; Otherwise, returns nil.
  (if* (member0 elem lis) then lis else (nconc lis (ncons elem))))

(defun pickout (condition lis)
  ;  Returns all elements in LIS such that condition is true.
  (sloop for xa in lis if (apply condition xa) collect xa))

(defun get-position (el list)
  ; return the position of "el" in "list".
  (sloop for xa in list for n from 0 
	if (equal xa el) 
	  return n
	finally (return nil)))

(defun ins-lis (elem lis)
  ; Returns LIS if ELEM is in LIS; otherwise, returns a new
  ; list made by adding ELEM to LIS.
  (if* (member0 elem lis) then lis else (push elem lis)))

#+franz ; since common lisp has its own function remove-duplicates
(defun rem-dups (l1)
  ; remove the duplicatives in "l1".
  (sloop for x in l1
	if (not (member0 x l2)) 
	  collect x into l2
	finally (return l2)))

(defun product-lists (lists)
  ;; make cross-product.
  (if (null (cdr lists))
      (mapcar 'ncons (car lists)) 
    (sloop for ls in (product-lists (cdr lists)) 
	   append (sloop for xa in (car lists) collect (cons xa ls)))))

(defun proper-product-lists (lists)
  ;; make cross-products such that each product is a set and no product
  ;; is a superset of other products.
  (if (null (cdr lists))
      (mapcar 'ncons (car lists)) 
    (let ((lls (proper-product-lists (cdr lists))) 
	  bones boness)
      (sloop for xa in (car lists) do
	     (sloop for ls in lls 
		    if (member0 xa ls) do
		    (push ls bones)
		    (setq lls (delete0 ls lls 1)))
	     (push bones boness)
	     (setq bones nil)
	     finally (return (real-collect-products 
			      (car lists) (nreverse boness) lls))))))

(defun real-collect-products (list1 boness lls)
  (sloop for xa in list1 
	 for bones in boness
	 append
	 (if (null bones)
	     (sloop for ls in lls collect (cons xa ls))
	   (append (reverse bones)
		   (sloop for ls in lls 
			  for xb = (cons xa ls)
			  if (not (sloop for xc in bones
					 thereis (is-subset xc xb)))
			  collect xb)))))

(defun n-tuples (n lis)
  ; all elements in [lis x lis x ... x lis].
  ;                   1     2    ...    n
  (cond ((equal n 1) (sloop for x in lis collect (ncons x)))
        ((> n 1) (let ((lists nil))
                  (sloop for li in (n-tuples (sub1 n) lis) do
                    (sloop for x in lis do 
                      (setq lists (cons (cons x li) lists))
                    ) ; loop
                  ) ; loop
                  lists))
	((equal n 0) (ncons nil))))

(defun pp2 (l) (mapcar 'pp l))

#+franz
(defun set-timer ()
  ; Returns a list consisting of the processor time and the garbage
  ; collector time used so far, measured in seconds.
(mapcar (function (lambda (x) (quotient x 60.0))) (ptime)))

#+franz
(defun get-time (time)
  ;  Returns a list consisting of the processor time and the garbage
  ;	    collector time used so far, measured in seconds.
  ;  Returns the processor time minus the garbage collection time since
  ;	    TIMERREADING was set by set-timer.
   (let (t1)
	  (setq t1 (mapcar (function (lambda (x) (quotient x 60.0))) (ptime)))
	  (diff (diff (car t1) (car time))		; CPU time
		(diff (cadr t1) (cadr time))))	; GC time
)


(defun add1-modulo-n (nums n)
  ;  Suppose NUMS is a list of numbers representing a number in base 
  ;  of N + 1. Add one at the first number of NUMS, if the result is 
  ;  equal to N + 1, then set that number to 0 and add one to the rest
  ;  of NUMS. If no numbers in the rest, then throw *overflow*.
  (cond ((null nums) (*throw 'add-one '*overflow*))
	((equal (car nums) n) (cons 0 (add1-modulo-n (cdr nums) n)))
	(t (rplaca nums (1+ (car nums))))))

(defun sub1-modulo-n (nums n)
  ; Suppose NUMS is a list of numbers representing a number in base 
  ; of N + 1. Sub one at the first number of NUMS, if it is not 0. 
  ; Otherwise, borrow one from its high position.
  (cond ((null nums) nil)
	((equal (car nums) 0) (cons n (sub1-modulo-n (cdr nums) n)))
	(t (rplaca nums (sub1 (car nums))))))

#+franz
(defun merge-list (lst1 lst2 orderp)
    (merge (copylist lst1) (copylist lst2) orderp))
;   (sloop while (and lst1 lst2) do
;      (push (if* (funcall orderp (car lst1) (car lst2)) 
;			then (pop lst1) else (pop lst2))
;            l1))
;   (append (reverse l1) lst1 lst2))

(defun insert-list (ele lst2 orderp &aux l1)
  ; This procedure has no side effect on lst2 and can insert an element
  ; into lst2 even ele is already in lst2. 
  ;
  ; The option nil in (insert ele lst order nil) doesn't work when 
  ; ele is a list !!!!
  ;
  (if* (member0 ele lst2) 
      then (sloop for xa in (reverse lst2) do 
		(push xa l1)
		(if* (equal xa ele) then (push xa l1) (setq ele '****))
	      finally (return l1))
      else (insert ele (copylist lst2) orderp t)))


(defun ntimes (n term) (sloop for i from 1 to n collect term))
		     
(defun con-nums (i1 i2) (sloop for i from i1 to i2 collect i))

(defun con1-nums (j p) (sloop for i downfrom (+ j p) to (1+ p) collect i))

(defun less-vector (l1 l2)
  (sloop
    for x in l1
    as y in l2
    always (<= x y)))

(defun car-num-order (x1 x2) (not (greaterp (car x1) (car x2))))

(defun get-rule (num)
  (sloop for r in $rule-set when (= (ruleno r) num) return r))

(defun longest-list (list-list) 
  ; return a longest list in list-list.
  (sloop with max = 0 with len with res
	for xa in list-list
	if (> (setq len (length xa)) max)
	  do (setq max len res xa)
	finally (return res)))

(defun one-presentative (set sets)
  ; return a subset A of "set" such that "a" is in "set" - A 
  ; iff there is a "b" in A and "a" and "b" are in one same set of "sets".
  (sloop with result with first while set do
    (setq first (pop set))
    (sloop for set2 in sets 
	  if (member0 first set2)
	    return (setq set (set-diff set set2)))
    (push first result)
	finally (return result)))

(defun capitalize (ch) (if* (and ch (lower-case-p ch)) (- ch 32) ch))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; set.lsp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains some functions to implement basic
; data-structures like multisets and some functions on lists.

#+franz
(defun intersection (s1 s2)
  ;  Returns the intersection of the sets S1 and S2.
  (sloop for x in s2 if (member0 x s1) collect x))

(defun common-elements (l1 l2)
  (sloop for xa in l2 
	if (member0 xa l1) 
	  collect xa into res
	and do (setq l1 (remove0 xa l1 1))
	finally (return res)))

(defun have-common (l1 l2) 
   (sloop for x1 in l1 if (member0 x1 l2) return x1 finally (return nil)))

#+franz
(defun union (s1 s2)
  ;  Returns the union of the sets S1 and S2.
  (append s1 (sloop for elem in s2 if (not (member0 elem s1)) collect elem)))

(defun set-diff (s1 s2)
  ; Returns the difference of S1 and S2, that is, S1 - S2.
  (sloop for xa in s2 do (setq s1 (remove0 xa s1 1))
	finally (return s1)))

(defun set-diff2 (s1 s2)
  (sloop for xa in s1 if (not (member0 xa s2)) collect xa))

(defun is-subset (l1 l2)
  ;  Returns T if L1 is a subset of L2.
  (sloop for xa in l1 always (member0 xa l2)))

(defun list-diff (l1 l2)
  ; Returns the difference of l1 and l2.
  (sloop for xa in l1 
	if (if* (member0 xa l2) 
	       then (setq l2 (remove0 xa l2 1)) nil
	       else t)
	  collect xa))

(defun is-sublist (l1 l2)
  ;  Returns T if L1 is a sublist of L2.
  (sloop for xa in l1 always (if* (member0 xa l2) then (setq l2 (remove0 xa l2 1)) t)))

(defun mult-insert (m1 ms)
  ; insert a multi iterm into a multi iterm set.
  (sloop for m2 in ms 
	if (equal (car m1) (car m2))
	 return (progn (rplacd m2 (+ (cdr m1) (cdr m2))) ms)
	 finally (return (cons m1 ms))))

(defun mult-sort-insert (m1 ms)
  ; insert a multi iterm into a multi iterm set.
  (sloop for ms2 on ms as m2 = (car ms2)
	if (equal (car m1) (car m2))
	  return (progn (rplacd m2 (+ (cdr m1) (cdr m2))) ms)
	else if (total-order (car m2) (car m1))
	       return (append small (ncons m1) ms2)
	else collect m2 into small
	finally (return (append1 ms m1))))

(defun mult-merge (l1 l2) 
  (sloop for xa in l1
	if (sloop for xb in l2
		 if (equal (car xb) (car xa))
		   return (rplacd xb (+ (cdr xb) (cdr xa)))
		 finally (return nil))
	  do nil
	else collect xa into mlis
	finally (return (append mlis l2))))

(defun mult-sort-merge (l1 l2)
  ; assume l2 is well-order mult-sets.
  (sloop for xa in l1
	do (setq l2 (mult-sort-insert 
		      (cons (flat-term (car xa)) (cdr xa)) l2))
	finally (return l2)))

(defun mult-union (s1 s2)
  (sloop for xa in s1 do (setq s2 (mult-insert xa s2))
	finally (return s2)))

(defun mult-length (ms)
  ; return the number of length of ms.
  (apply '+ (mapcar 'cdr ms)))

(defun mult-diff (m1 m2) 
  ; Returns (M1-M2 . M2-M1) where M1 and M2 must be in mult-form.
  ; However, M1-M2 and M2-M1 are in set form.
  (let (l1 l2 l3)       
    (sloop for xa in m1 do
          (setq l1 (assoc0 (car xa) m2))
          (if* l1 then (if* (greaterp (cdr xa) (cdr l1)) 
                          then (push (car xa) l2))
              else (push (car xa) l2)))
    (sloop for xa in m2 do
          (setq l1 (assoc0 (car xa) m1))
          (if* (and l1 (greaterp (cdr xa) (cdr l1)))
              then (push (car xa) l3)
              elseif (not l1) then (push (car xa) l3)))
    (cons l2 l3)))

(defun mult-diff2 (m1 m2) 
  ; Returns (M1-M2) where M1 and M2 must be in mult-form.
  ; M1-M2 is also in multi-form.
  (sloop with l1 = nil 
	for xa in m1 
	   if (if* (setq l1 (assoc0 (car xa) m2))  
	         then (if* (greaterp (cdr xa) (cdr l1)) then
                         (setq xa (cons (car xa) (- (cdr xa) (cdr l1)))))
                 else xa)
	    collect xa))

(defun mult-form (lis) 
  ; Returns the multiset-form of list LIS.
  ; eg. (* * a b a *) ==> ((* . 3) (a . 2) (b . 1))
  (sloop for xa in lis
	if (sloop for l in mlis
		 if (equal (car l) xa)
		   return (rplacd l (1+ (cdr l)))
		 finally (return nil))
	  do nil
	else collect (cons xa 1) into mlis
	finally (return mlis)))

;(defun mult-form (lis) 
;  (multi-to-one (car lis) (cdr lis) nil))

;(defun multi-to-one (elem rest n_rep)
;  ; Local function.  Called by MULT-FORM.
;  (let ((i 1)) 
;    (if* (null rest)
;        then (if* (not (assoc0 elem n_rep))
;                 (setq n_rep (cons (cons elem i) n_rep)))
;             n_rep
;        elseif (not (assoc0 elem n_rep))
;        then (sloop for xa in rest do
;                   (if* (equal elem xa) then (setq i (1+ i))))
;             (setq n_rep (cons (cons elem i) n_rep)))
;    (multi-to-one (car rest) (cdr rest) n_rep)))

(defun demult-form (mul &aux res) 
  ; Returns the list-form of multi-set MUL.
  ; eg. ((* . 3) (a . 2) (b . 1)) ==> (b a a * * *).
  (sloop for m in mul do 
     (sloop for xa from 1 to (cdr m) do (push (car m) res)))
    res)






