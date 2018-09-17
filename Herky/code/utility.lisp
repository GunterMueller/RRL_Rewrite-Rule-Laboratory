(in-package "USER")

;;;Created by Hantao Zhang, 11/15/88.

(defmacro insert1 (one lis) `(if (memq ,one ,lis) ,lis (push ,one ,lis)))
(defmacro push-end (one many) `(append1 ,many ,one t))
(defmacro add-end (one many) `(setq ,many (append1 ,many ,one)))
(defmacro cross-product (l1 l2) `(product-lists (list ,l1 ,l2)))

(defmacro aset (value array &rest indices)  
       `(setf (aref ,array ,@indices) ,value))

#+kcl
(defmacro arefn (array index1 &optional index2) 
  (if index2
      `(aref (the (array fixnum) ,array)
	     (the fixnum ,index1) (the fixnum ,index2)) 
      `(aref (the (array fixnum) ,array) (the fixnum ,index1))))

#+kcl
(defmacro asetn (val array index1 &optional index2) 
  `(setf (arefn ,array ,index1 ,index2) (the fixnum ,val)))

#-kcl
(defmacro asetn (val array index1 &optional index2) 
  (if index2
      `(setf (aref ,array ,index1 ,index2) ,val)
    `(setf (aref ,array ,index1) ,val)))

(defmacro pick-out-good-rule (num)
  ; using binary search algorithm to pick out a rule in $rule-set.
  `(binary-pick-rule (sub1 (min ,num (length $rule-set))) $rule-set ,num))

;; (while test :return result body)
(defmacro while (test &body body)
  (if (eq (first body) :return)
      `(do () ((not ,test) ,(second body)) ,@(nthcdr 2 body))
    `(do () ((not ,test)) ,@body)))

;; (until test :return result body)
(defmacro until (test &body body)
  (if (eq (first body) :return)
      `(do () (,test ,(second body)) ,@(nthcdr 2 body))
  `(do () (,test) ,@body)))

;; (repeat test :return result body)
;; Do test *after* body
(defmacro repeat (test &body body)
  (if (eq (first body) :return)
      `(loop ,@(nthcdr 2 body) (when ,test (return ,(second body))))
    `(loop ,@body (when ,test (return)))))

;; (floop :for fixnum-var :below fixnum-limit :do code)
;; Sloop seems to do some bad things with fixnums in this kind of 
;; loop.  (Specifically, it generates a temp object which should 
;; really be a fixnum; so some unnecessary CMPmake-fixnum and 
;; number-compare's are inserted in the C code.) Floop will
;; generate better code in this case.
(defmacro floop (&key for (from 0) below do)
  (let ((end (gentemp "END")) (label (gentemp "LABEL")))
    `(let ((,for (the fixnum ,from))
	   (,end (the fixnum ,below)))
       (declare (type fixnum ,for ,end))
       (block ()
	      (tagbody
	       ,label
	       (when (>= ,for ,end) (return))
	       ,do
	       (incf ,for)
	       (go ,label))))))

; user-menu is a very useful macro used often in building menus.
;
; explained by example --
;    (user-menu
;       (cat  " help about cat "  (setq ans cat))
;       (dog  " some message about dog " (setq ans dog) (do something else))
;       (crow " dbfjdf dsah kjf fjda fj" body to be executed)
;       (dummy " will do something and stay in this function"
;                     (body) (setq failed t)))
; will prompt the user to type some subsequence of cat , dog ,crow or dummy
; and execute the body and return value of last form evaluated.
; If the last form is (setq failed t) then it doesn't exit the prompt loop 
; but asks for another choice. This is useful if the user wants to display 
; rules or eqns before making a choice.
; See functions in options.lisp to get a better idea of how this works.
(defmacro user-menu (&rest options)
  (let ((option-list (cons 'quit (cons 'help (mapcar 'car options))))
        (choice (gensym)))
    `(let (,choice)
       (do ((failed nil nil)
	    (ans nil))
	   (nil)
	 (setq ,choice (progn () (print-head ',option-list)
			      (choose-str (read-atom 'none) ',option-list)))
	 (if (numberp ,choice) 
	    (setq ans ,choice) 
	    (setq ans (case ,choice
			,@(sloop for xa in options 
				 collect `(,(car xa) . ,(cddr xa)))
			(t (unless (eq ,choice 'quit) 
				   (setq failed t)
				   (if* (eq ,choice 'help) 
				       then 
				     (terpri)
				     ,@(sloop for xa in options
					      collect `(princ ',(car xa))
					      collect `(princ ": ")
					      collect `(princ ',(cadr xa)) 
					      collect '(terpri))
				     (princ "HELP:         Print this message.") (terpri)
				     (princ "QUIT:         Quit this procedure.") (terpri)
				     (terpri)
				     else (princ "Please select an option from the list.")
				     (princ "  Try again.") (terpri)))))))
	 (if (not failed) (return ans)) ))))

(defmacro add-associate-list (head elem lists)
  (let ((v1 (gensym)))
    `(let ((,v1 (assq ,head ,lists)))
        (if ,v1 (nconc ,v1 (ncons ,elem))
	        (push (list ,head ,elem) ,lists))
	,lists)))

(defmacro add-associate-list-equal (head elem lists)
  (let ((v1 (gensym)))
    `(let ((,v1 (assoc ,head ,lists :test #'equal)))
        (if ,v1 (nconc ,v1 (ncons ,elem))
	        (push (list ,head ,elem) ,lists))
	,lists)))

(defmacro query-insert (elem list)
  ;; return the list if and only if elem is not in list.
   `(if (member0 ,elem ,list) nil (push ,elem ,list)))

(defmacro remonce (element list) `(removen ,element ,list 1))

(defun remove2 (ele list &optional (num 1) &aux new)
  ;; Return the remaining elements of the list 
  ;; if "num" copies of "ele" can be deleted from "list".
  ;; Otherwise, return nil.
  (dolist (xa list)
    (if (or (= num 0) (not (equal ele xa))) 
	(setq new (cons xa new))
	(setq num (1- num))))
  (if (= num 0) (nreverse new)))	

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

(defun is-subsequence (str1 str2)
  ; Returns STR2 if STR1 is a subsequence of STR2 
  ; (from the first character on); otherwise, returns NIL.
  ; This function is used in parsing input to determine if it is
  ; a valid response.
  (sloop with i2 = 0 with l2 = (1- (length str2)) 
	 for i1 from 0 to (1- (length str1)) 
	 always (sloop for j2 from i2 to l2
		       if (char= (char str1 i1) (char str2 j2))
		       return (setq i2 j2)
		       finally (return nil))))	 

(defun is-subseq-list (l1 l2)
  ; Same as the is-subsequence, except that the inputs are
  ; lists instead of symbols.
  ; l1 and l2 are integer lists in decreasing order.
  (sloop with c1 = (pop l1)
	for c2 in l2
	if (eq c1 c2) do (if l1 (setq c1 (pop l1)) (return t))
	else if (> c1 c2) return nil
	finally (return (null c1))))

(defun non-decreasing-seq (l1)
  ; return t iff l1 is a non-decreasing sequence of integers.
  (sloop for pre in l1 as next in (cdr l1) always (>= pre next)))

(defun add-at-end (lis elem)
  ; If ELEM is in LIS, returns LIS with ELEM added at end; 
  ; Otherwise, returns nil.
  (if (member0 elem lis) lis (nconc lis (ncons elem))))

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
  (if (member0 elem lis) lis (push elem lis)))

(defun rem-dups (l1)
  ; remove the duplicatives in "l1".
  (sloop for x in l1
	 if (not (member0 x l2)) 
	 collect x into l2
	 finally (return l2)))

(defun product-lists (lists)
  ; make cross-product.
  (if (null (cdr lists))
      (sloop for xa in (car lists) collect (ncons xa))
      (sloop for ls in (product-lists (cdr lists)) 
	    nconc (sloop for xa in (car lists) collect (cons xa ls)))))

(defun split-alist (alist)
  (sloop for x in alist
	 collect (car x) into list1
	 collect (cdr x) into list2
	 finally (return (list list1 list2))))

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

(defun add1-modulo-n (nums n)
  ;  Suppose NUMS is a list of numbers representing a number in base 
  ;  of N + 1. Add one at the first number of NUMS, if the result is 
  ;  equal to N + 1, then set that number to 0 and add one to the rest
  ;  of NUMS. If no numbers in the rest, then throw *overflow*.
  (cond ((null nums) (throw 'add-one '*overflow*))
	((equal (car nums) n) (cons 0 (add1-modulo-n (cdr nums) n)))
	(t (rplaca nums (add1 (car nums))))))

(defun sub1-modulo-n (nums n)
  ; Suppose NUMS is a list of numbers representing a number in base 
  ; of N + 1. Sub one at the first number of NUMS, if it is not 0. 
  ; Otherwise, borrow one from its high position.
  (cond ((null nums) nil)
	((equal (car nums) 0) (cons n (sub1-modulo-n (cdr nums) n)))
	(t (rplaca nums (sub1 (car nums))))))

(defun merge-list (lst1 lst2 orderp &aux l1)
  ; assume both lst1 and lst2 are sorted.
  ; has side effect on lst2.
  (sloop while (and lst1 lst2) do
	 (push (if (funcall orderp (car lst1) (car lst2)) 
		   (pop lst1) 
		   (pop lst2))
	       l1))
  (nconc (nreverse l1) (my-copylist lst1 1) lst2))

(defun insert-list (ele lst2 orderp &aux l1)
  ; This procedure has side effect on lst2 and can insert an element
  ; into lst2 even ele is already in lst2. 
  (sloop for xa on lst2 do 
	 (if (funcall orderp ele (car xa))
	     (return (nconc (nreverse l1) (cons ele xa)))
	     (setq l1 (cons (car xa) l1)))
	 finally (return (append1 lst2 ele t))))

(defun ntimes (n term) (sloop for i from 1 to n collect term))
		     
(defmacro con-nums (i1 i2) `(sloop for i from ,i1 to ,i2 collect i))
(defmacro rev-con-nums (i1 i2) `(sloop for i downfrom ,i2 to ,i1 collect i))

(defmacro less-vector (l1 l2)
  `(sloop for x in ,l1 as y in ,l2 always (<= x y)))

(defun car-num-order (x1 x2) (not (greaterp (car x1) (car x2))))

(defun get-rule (num)
  (sloop for r in $rule-set when (eq (ruleno r) num) return r))

(defun longest-list (list-list) 
  ; return a longest list in list-list.
  (sloop with max = 0 with len with res
	for xa in list-list
	if (> (setq len (length xa)) max)
	  do (setq max len res xa)
	finally (return res)))

(defun same-list (l1 l2 &optional (pred 'lessp))
  (equal (sort l1 pred) (sort l2 pred)))


(defun binary-pick (m list num &aux rule n)
  ; using binary search algorithm to pick out a rule in list.
  (if* (< m 2)
      then (if* (eq num (car list)) 
	       then (car list)
	       elseif (eq num (cadr list))
	       then (cadr list))
      else
      (setq n (quotient m 2)
	    rule (nth n list))
      (if* (eq num rule) 
	   then rule
	   elseif (> num rule)
	   then (if* (equal m (+ n n))
		     (binary-pick (sub1 n) (nthcdr (add1 n) list) num)
		     (binary-pick n (nthcdr (add1 n) list) num))
	   else (binary-pick (sub1 n) list num))))

(defun each (l &optional f) 
  (sloop for xa in l 
	do (terpri) (if f (funcall f xa) (princ xa))))

(defmacro fillarray (x y) 
  (if (cdr y)
      `(sloop for i from 0 
	      for val in ,y do
	      (aset val ,x i))
      `(fill ,x (car ,y))))

(defmacro fillarray1 (array b1 val) 
  `(sloop for i from 0 to ,b1 do (aset ,val ,array i)))

(defmacro fillarray2 (array b1 b2 val) 
  `(sloop for i from 0 to ,b1 do
	  (sloop for j from 0 to ,b2 do
		 (aset ,val ,array i j))))

(defmacro listarray (x &optional (n (1- (car (array-dimensions x)))))
  `(sloop for i from 0 to ,n collect (aref ,x i)))

(defmacro def-array (name dims &optional fixnum)
  `(progn
     (defvar ,name nil)
     (def-array2 ,name ,dims ,fixnum)))

(defmacro def-array2 (name dims &optional fixnum)
  `(eval-when 
    (load eval compile)
    (cond (,fixnum
	   #+kcl (setf ,name (make-array ,dims
					 :element-type 'fixnum
					 :static t))
	   #-kcl (setf ,name (make-array ,dims))
	   )
	  (t
	   #+kcl (setf ,name (make-array ,dims :static t))
	   #-kcl (setf ,name (make-array ,dims))
	   ))))

;; From coverset.lisp
(defun car-lessp (s1 s2) (lessp (car s1) (car s2)))

;; Temporarily disable interrupts in AKCL.  This is useful to
;; maintain consistency of data structures and avoid dangling
;; pointers in case the user interrupts the program.
#+kcl (defmacro disabling-interrupts (&body code)
	`(let ((si::*interrupt-enable* nil))
	   ,@code))

#-kcl (defmacro disabling-interrupts (&body code)
	`(progn ,@code))

(defun is-sorted (lis order)
  (sloop with first = (car lis)
	for second in (cdr lis)
	always (prog1 (or (equal first second)
			  (funcall order first second))
		      (setq first second))))

;;; Taken from history.lisp
(defun my-copylist (list &optional (depth 2))
  ; >>>>> 4/5/89
  ; Make new list from elements of "list".
  (if* (eq depth 1)
      ;(mapcan 'list list)		
      (append list nil)
      (sloop for xa in list collect (my-copylist xa (sub1 depth)))))

(defmacro start-timer (&optional x)
  (if x `(setq ,x (get-internal-run-time)) `(get-internal-run-time)))
(defmacro run-time (x)  `(- (get-internal-run-time) ,x))
(defmacro time-in-sec (x)
  `(/ (float ,x) (float internal-time-units-per-second)))

(defmacro add-time (variable body)
  ; instead of having to use run-time and set-timer in the code
  ; this macro adds to variable the time required to execute body
  (if *no-time-counting*
      `,body
    `(let (v1)
       (start-timer v1)
       (prog1
	   ,body
	 (setq ,variable (+ ,variable (run-time v1))))
       )))

(defmacro add-rule-time (rule) `(add-time $add-time (add-rule ,rule)))
(defmacro orient-rule-time (eqn) 
  `(add-time $ord-time (orient-eqn-to-rule ,eqn)))
(defmacro norm-term-time (term) `(add-time $norm-time (norm-term ,term)))

(defun date () ; print the current date.
  (let (sec min hou day mon yea)
    (multiple-value-setq (sec min hou day mon yea) (get-decoded-time))
    (princ hou) (princ ":") (princ min) (princ ":") (princ sec) (princ " ")
    (princ (case mon
		  (1 "Jan")
		  (2 "Feb")
		  (3 "Mar")
		  (4 "Apr")
		  (5 "May")
		  (6 "Jun")
		  (7 "Jul")
		  (8 "Aug")
		  (9 "Sep")
		  (10 "Oct")
		  (11 "Nov")
		  (12 "Dec")
		  (t "ERROR")))
    (princ " ") (princ day) 
    (princ " ") (princ yea)
    (terpri)))

; Franz Lisp functions that don't exist in Common Lisp.
;  Some functions to emulate Franz Lisp functions:

(defmacro probef (&rest rest) `(probe-file . ,rest))

(defmacro getchar (x n) `(char ,x (1- ,n)))
(defmacro getcharn (x n) `(char-int (getchar ,x ,n)))
(defmacro lowercasep (n) `(lower-case-p (int-char ,n)))
(defmacro reset () `(throw 'reset '*reset*))

(defmacro member0 (x y) `(member ,x ,y :test #'equal))
#+kcl (defmacro memq (x y) `(member ,x ,y))
(defmacro delete0 (x list) `(delete ,x ,list :test #'equal))
(defmacro delete1 (x list) `(delete ,x ,list :count ,1 :test #'equal))
(defmacro deleten (x list n) `(delete ,x ,list :count ,n :test #'equal))
#+kcl (defmacro delq (x alist) `(delete ,x ,alist))
(defmacro remove0 (x list) `(remove ,x ,list :test #'equal))
(defmacro removen (x list n) `(remove ,x ,list :count ,n :test #'equal))
(defmacro assoc0 (x alist) `(assoc ,x ,alist :test #'equal))
#+kcl (defmacro assq (x alist) `(assoc ,x ,alist))

(defmacro add (&rest args) `(+ ,@args))
(defmacro plus (&rest args) `(+  ,@args))
(defmacro minus (x y) `(- ,x ,y))
(defmacro times (&rest args) `(* ,@args))
(defmacro sub1 (x) `(1- ,x))
(defmacro add1 (x) `(1+ ,x))
(defmacro diff (&rest args) `(- ,@args))
(defmacro remainder (x y) `(rem ,x ,y))
(defmacro quotient (x y) `(truncate (/ ,x ,y)))

(defmacro lessp (x y) `(< ,x ,y))
(defmacro alphalessp (x y) `(char< ,x ,y))
(defmacro greaterp (x y) `(> ,x ,y))

(defmacro symeval (x) `(symbol-value ,x))
(defmacro ncons (x) `(cons ,x nil))
(defmacro append1 (list elem &optional destroy) 
  (if destroy
      `(if ,list 
	   (nconc ,list (ncons ,elem))
	   (setf ,list (ncons ,elem)))
      `(append ,list (ncons ,elem))))

(defmacro append2 (l1 l2 &optional l3)
  (let ((c (gensym)))
    (if l3
	`(let ((,c ,l3))
	   (dolist (xa ,l2) (setq ,c (cons xa ,c)))
	   (dolist (xa ,l1) (setq ,c (cons xa ,c)))
	   ,c)
	`(let ((,c ,l2))
	   (dolist (xa ,l1) (setq ,c (cons xa ,c)))
	   ,c))))      

(defmacro copy (list) `(copy-tree ,list))
(defmacro copylist (list) `(copy-list ,list))

(defmacro dsubst (new old tree) `(nsubst ,new ,old ,tree :test #'equal))

(defun concat (&rest args)
  (apply 'concatenate (mapcar 'princ-to-string args)))

(defmacro infile (fname) `(open ,fname :if-does-not-exist nil))

(defmacro outfile (fname &optional append)
  ; opens a port to write fname.  If st-type is a symbol or
  ; string whose name begins with 'a', then the file will
  ; be opened in append mode; otherwise, a new file will be
  ; created.
  (if append
      `(open ,fname :direction :output :if-exists :append
	     :if-does-not-exist :create)
      `(open ,fname :direction :output :if-exists :new-version 
	     :if-does-not-exist :create)))

(defmacro localf (x) `(ignore ,x))
(defmacro selectq (&rest body) `(case . ,body))
(defmacro caseq (&rest body) `(case . ,body))
(defmacro nequal (x1 x2) `(not (equal ,x1 ,x2)))
(defmacro neq (x1 x2) `(not (equal ,x1 ,x2)))

(defun attach (g-x l-l)
  (setf (cdr l-l ) (cons (car l-l) (cdr l-l)))
  (setf (car l-l) g-x))

(defmacro uconcat (&rest args) `(concatenate 'string ,@args))

(defun sum-up (list &aux (sum 0))
  (dolist (xa list) (setq sum (+ sum xa)))
  sum)

(defmacro insert (elem list &optional (pred #'<))
  ;; Insert elem into list, which is sorted by the predicate pred.
  ;; the original list will be destroyed.
  `(if ,list
       (sloop for current on ,list do
	      (when (funcall ,pred ,elem (car current))
		(attach ,elem current)
		(return ,list))
	      finally (return (append1 ,list ,elem)))
       (setq ,list (ncons ,elem))))

(defmacro tab (n) 
  `(format t (uconcat "~" (princ-to-string ,n) "T")))

(eval-when (compile load eval)

;------ if* macro 
; This macro allows the following forms:
;	(if* a b c)           ==>  (if a b c)
;	(if* a then b)        ==>  (when a b)
;	(if* a then b else c) ==>  (cond (a b) (t c))
;	(if* a then b b2      ==>  (cond (a b b2) (c d d2) (t e))
;	 elseif c then d d2
;	 else e)
; (IF* test then-action else-action1 else-action2 ...)

  (defun else-keyword-p (x)
    (member x '(elseif else)))

  (defun elements-before-else (list &aux res)
    (dolist (xa list)
	    (if (else-keyword-p xa) (return))
	    (setq res (append res (list xa))))
    res)

  (defun handle-condition (list)
    (cond ((or (null list)
	       (not (else-keyword-p (car list))))
	   nil)
	  ((equal (car list) 'else)
	   (if (find-if #'else-keyword-p  (cdr list))
	       (error "IF: ELSE or ELSEIF follows an ELSE"))
	   (list (cons t (cdr list))))
	  ((not (equal (caddr list) 'then))
	   (error "IF: THEN keyword expected"))
	  (t (list (cons (cadr list)
			 (elements-before-else (cdddr list)))))))
  )

(defmacro if* (test &rest clauses)
  (cond ((eq (car clauses) 'then)
	 (if (find-if #'else-keyword-p (cdr clauses))
	     `(cond . ,(mapcon #'handle-condition
			       `(elseif ,test . ,clauses)))
	     `(when ,test . ,(cdr clauses))))
	(t `(if ,test . ,clauses))))

#|
(defun getenv (name)
  (progn nil
         #+kcl (si:getenv (string name))
         #+ibcl (si:getenv (string name))
	 #+allegro (sys:getenv (string name))
	 #+lucid (sys:environment-variable (string name))
	 ))
|#

; This file contains some functions to implement basic
; data-structures like multisets and some functions on lists.

;(defun intersection (s1 s2)
;  ;  Returns the intersection of the sets S1 and S2.
;  (sloop for x in s2 if (member0 x s1) collect x))

(defun common-elements (l1 l2)
  (sloop for xa in l2 
	if (member0 xa l1) 
	  collect xa into res
	and do (setq l1 (removen xa l1 1))
	finally (return res)))

(defun have-common (l1 l2) 
   (sloop for x1 in l1 if (member0 x1 l2) return x1 finally (return nil)))

;(defun union (s1 s2)
;  ;  Returns the union of the sets S1 and S2.
;  (nconc s1 (sloop for elem in s2 if (not (member0 elem s1)) collect elem)))

(defun set-diff (s1 s2) 
  ; (ldiff s1 s2)
  ; Returns the difference of S1 and S2, that is, S1 - S2.
  (sloop for xa in s2 do (setq s1 (removen xa s1 1))
	finally (return s1)))

(defun is-subset (l1 l2)
  ;  Returns T if L1 is a subset of L2.
  (sloop for xa in l1 always (member0 xa l2)))

(defun list-diff (l1 l2)
  ; Returns the difference of l1 and l2.
  (sloop for xa in l1 
	if (if* (member0 xa l2) 
	       then (setq l2 (deleten xa l2 1)) nil
	       else t)
	  collect xa))

(defun is-sublist (l1 l2)
  ;  Returns T if L1 is a sublist of L2.
  (sloop for xa in l1 always
	 (if* (member0 xa l2) then
	      (setq l2 (removen xa l2 1))
	      t
	      else
	      nil)))

(defun mult-insert (m1 ms)
  ; insert a multi iterm into a multi iterm set.
  (sloop for m2 in ms 
	if (equal (car m1) (car m2))
	 return (progn (rplacd m2 (+ (cdr m1) (cdr m2))) ms)
	 finally (return (cons m1 ms))))

(defun mult-merge (l1 l2) 
  (sloop for xa in l1
	if (sloop for xb in l2
		 if (equal (car xb) (car xa))
		   return (rplacd xb (add (cdr xb) (cdr xa)))
		 finally (return nil))
	  do nil
	else collect xa into mlis
	finally (return (append mlis l2))))

(defun mult-sort-insert (m1 ms &aux small m2 (ms2 ms))
  ; insert a multi iterm into a multi iterm set.
  (sloop while ms2 do
	 (setq m2 (car ms2))
	 (if* (equal (car m1) (car m2))
	      then
	      (return
		(if (equal (+ (cdr m1) (cdr m2)) 0)
		    (nconc (nreverse small) (cdr ms2))
		    (progn 
		      (setf (cdr m2) (+ (cdr m1) (cdr m2)))
		      ms)))
	      else (setq small (cons m2 small)
			 ms2 (cdr ms2)))
	 finally (return (append1 ms m1 t))))

(defun mult-sort-merge (l1 l2)
  ; assume l2 is well-order mult-sets.
  (sloop for xa in l1
	 do (setq l2 (mult-sort-insert xa l2))
	 finally (return l2)))

(defun mult-union (s1 s2)
  (sloop for xa in s1 do (setq s2 (mult-insert xa s2))
	finally (return s2)))

(defun mult-length (ms)
  ; return the number of length of ms.
  (apply '+ (mapcar 'cdr ms)))

(defun mult-diff-set (m1 m2 &aux l2 l1) 
  ; Returns (m1-m2 . m2-m1) where m1 and m2 are lists of elements 
  ; which may have duplicates, but the returned two lists don't 
  ; have duplicates.
  (setq m1 (mult-form m1) m2 (mult-form m2))
  (dolist (xa m1)
	  (sloop for xb in m2 do
		 (when (equal (car xa) (car xb))
		       (if (> (cdr xa) (cdr xb)) 
			   (push (car xa) l1)
			 (if (< (cdr xa) (cdr xb)) 
			     (push (car xa) l2)))
		       (setq m2 (delete xb m2))
		       (return nil))
		 finally (push (car xa) l1)))
  (cons l1 (nconc l2 (sloop for xa in m2 collect (car xa)))))

(defun mult-diff2 (m1 m2) 
  ; Returns (M1-M2) where M1 and M2 must be in mult-form.
  ; M1-M2 is also in multi-form.
  (sloop with l1 = nil 
	 for xa in m1 
	 if (if (setq l1 (assoc (car xa) m2))  
		(if (greaterp (cdr xa) (cdr l1))
		    (setq xa (cons (car xa) (- (cdr xa) (cdr l1)))))
	      xa)
	 collect xa))

(defun mult-diff3 (m1 m2) 
  ; Returns (M1-M2) where M1 and M2 must be in mult-form.
  ; M1-M2 is also in multi-form.
  (sloop with l1 = nil 
	 for xa in m1 
	 if (if (setq l1 (assoc (car xa) m2))  
		(if (neq (cdr xa) (cdr l1))
		    (setq xa (cons (car xa) (- (cdr xa) (cdr l1)))))
	      xa)
	 collect xa))

(defun mult-form (lis) 
  ; Returns the multiset-form of list LIS.
  ; eg. (* * a b a *) ==> ((* . 3) (a . 2) (b . 1))
  (sloop for xa in lis
	if (sloop for l in mlis
		 if (equal (car l) xa)
		   return (rplacd l (add1 (cdr l)))
		 finally (return nil))
	  do nil
	else collect (cons xa 1) into mlis
	finally (return mlis)))

;(defun mult-form (lis) 
;  (multi-to-one (car lis) (cdr lis) nil))

;(defun multi-to-one (elem rest n-rep)
;  ; Local function.  Called by MULT-FORM.
;  (let ((i 1)) 
;    (if* (null rest)
;        then (if (not (assoc elem n-rep))
;                 (setq n-rep (cons (cons elem i) n-rep)))
;             n-rep
;        elseif (not (assoc elem n-rep))
;        then (sloop for xa in rest do
;                   (if (equal elem xa) (setq i (add1 i))))
;             (setq n-rep (cons (cons elem i) n-rep)))
;    (multi-to-one (car rest) (cdr rest) n-rep)))

(defun demult-form (mul) 
  ; Returns the list-form of multi-set MUL.
  ; eg. ((* . 3) (a . 2) (b . 1)) ==> (b a a * * *).
  (sloop for m in mul nconc (ntimes (cdr m) (car m))))

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

#+kcl (defun quit () (bye))
#+lucid (defun bye () (quit))
