;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.


#+franz (include "datamacs.l")

#-franz (in-package "RRL")


;;;; #+franzed merge-list as merge is different in common -- siva 9/24

(defun split-alist (alist)
  (loop for x in alist  collect (car x) into list1 collect (cdr x) into list2
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
    (if c1 
      then (loop for i2 = 1 then (1+ i2) 
	         as c2 = (getcharn symbol2 i2) until #-franz (eq c2 0)
						  #+franz (null c2) do
	          (if (eq  c1 c2) then 
		     (setq c1 (getcharn symbol1 i1) i1 (1+ i1))
	             (if #-franz (eq c1 0) #+franz (null c1) then (return symbol2))
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
	  (t (if (< l2 l1)
		 (setq tmp s2 s2 s1 s1 tmp l1 l2)) ; make s1 the shorter
	     (loop with pos = 0
		   for i from 0 to (1- l1)
		   as c = (char s1 i) always
		   (setq pos (loop for j from pos to (1- (length s2))
				   do (if (char= c (char s2 j)) (return j))))
		   )))))

(defun is-subseq-list (l1 l2)
  ; Same as the is-subsequence, except that the inputs are lists instead of symbols.
  ; l1 and l2 are integer lists in decreasing order.
  (loop with c1 = (pop l1)
	for c2 in l2
	if (eq c1 c2) do (if l1 (setq c1 (pop l1)) (return t))
	else if (> c1 c2) return nil
	finally (return (null c1))))

(defun non-decreasing-seq (l1)
  ; return t iff l1 is a non-decreasing sequence of integers.
  (loop for pre in l1 as next in (cdr l1) always (>= pre next)))

(defun add-at-end (lis elem)
  ; If ELEM is in LIS, returns LIS with ELEM added at end; Otherwise, returns nil.
  (if (member elem lis) then lis else (nconc lis (ncons elem))))

(defun pickout (condition lis)
  ;  Returns all elements in LIS such that condition is true.
  (loop for xa in lis if (apply condition xa) collect xa))

(defun get-position (el list)
  ; return the position of "el" in "list".
  (loop for xa in list for n from 0 
	if (equal xa el) 
	  return n
	finally (return nil)))

(defun ins-lis (elem lis)
  ; Returns LIS if ELEM is in LIS; otherwise, returns a new
  ; list made by adding ELEM to LIS.
  (if (member elem lis) then lis else (push elem lis)))

#+franz ; since common lisp has its own function remove-duplicates
(defun rem-dups (l1)
  ; remove the duplicatives in "l1".
  (loop for x in l1
	if (not (member x l2)) 
	  collect x into l2
	finally (return l2)))

(defun product-lists (lists)
  ; make cross-product.
  (if (null (cdr lists)) then (mapcar 'ncons (car lists)) else 
      (loop for ls in (product-lists (cdr lists)) 
	    nconc (loop for xa in (car lists) collect (cons xa ls)))))

(defun n-tuples (n lis)
  ; all elements in [lis x lis x ... x lis].
  ;                   1     2    ...    n
  (cond ((equal n 1) (loop for x in lis collect (ncons x)))
        ((> n 1) (let ((lists nil))
                  (loop for li in (n-tuples (sub1 n) lis) do
                    (loop for x in lis do 
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
;   (loop while (and lst1 lst2) do
;      (push (if (funcall orderp (car lst1) (car lst2)) 
;			then (pop lst1) else (pop lst2))
;            l1))
;   (nconc (reverse l1) lst1 lst2))

(defun insert-list (ele lst2 orderp &aux l1)
  ; This procedure has no side effect on lst2 and can insert an element
  ; into lst2 even ele is already in lst2. 
  ;
  ; The option nil in (insert ele lst order nil) doesn't work when 
  ; ele is a list !!!!
  ;
  (if (member ele lst2) 
      then (loop for xa in (reverse lst2) do 
		(push xa l1)
		(if (equal xa ele) then (push xa l1) (setq ele '****))
	      finally (return l1))
      else (insert ele (copylist lst2) orderp t)))


(defun ntimes (n term) (loop for i from 1 to n collect term))
		     
(defun con-nums (i1 i2) (loop for i from i1 to i2 collect i))

(defun con1-nums (j p) (loop for i from (+ j p) downto (1+ p) collect i))

(defun less-vector (l1 l2)
  (loop
    for x in l1
    as y in l2
    always (<= x y)))

(defun car-num-order (x1 x2) (not (greaterp (car x1) (car x2))))

(defun get-rule (num)
  (loop for r in $rule-set when (= (ruleno r) num) return r))

(defun longest-list (list-list) 
  ; return a longest list in list-list.
  (loop with max = 0 with len with res
	for xa in list-list
	if (> (setq len (length xa)) max)
	  do (setq max len res xa)
	finally (return res)))

(defun one-presentative (set sets)
  ; return a subset A of "set" such that "a" is in "set" - A 
  ; iff there is a "b" in A and "a" and "b" are in one same set of "sets".
  (loop with result with first while set do
    (setq first (pop set))
    (loop for set2 in sets 
	  if (member first set2)
	    return (setq set (set-diff set set2)))
    (push first result)
	finally (return result)))

(defun capitalize (ch) (if (and ch (lower-case-p ch)) (- ch 32) ch))
