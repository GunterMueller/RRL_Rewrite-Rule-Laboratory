;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#-franz (in-package "RRL")

;; 
;;
;; Contains macros for use in RRL.
;; this file should only be loaded in Common lisp.
;; re-implements some Franz-things that RRL uses. -- siva.
;;
;; will be needed by all other RRL files for compilation.
;;
;;
;;

;     character

(shadow '(lisp:if
	  lisp:princ
	  #-franz lisp:terpri
	  lisp:type-of lisp:remove lisp:delete
	  lisp:member lisp:assoc lisp:subst lisp:position
	 ))

;; franz uses equal test.
(defmacro subst(new old tree)
  `(lisp:subst ,new ,old ,tree :test #'equal))


(defmacro member (x list)
  `(lisp:member ,x ,list :test #'equal))
(defmacro memq (x list)
  `(lisp:member ,x ,list))  ; no #'eq to work for integers too.
(defmacro member-equal (x list)
  `(lisp:member ,x ,list :test #'equal))

(defmacro assq(a b) `(lisp:assoc ,a ,b))
(defmacro assoc(a b) `(lisp:assoc ,a ,b :test #'equal))

;; equal test for remove like member bcos of ac-match etc.
(defmacro remove (elem lis &optional num)
  `(lisp:remove ,elem ,lis :count (if ,num ,num 1) :test #'equal))

(defmacro remq (x list &optional n)
  `(lisp:remove ,x ,list ,@(when n `(:count ,n))))

;--- caseq
; use is 
;    (caseq expr
;	    (match1 do1)
;	    (match2 do2)
;	    (t  doifallelsefails))
; the matchi can be atoms in which case an 'eq' test is done, or they
; can be lists in which case a 'memq' test is done.
;

(defmacro caseq (switch &body clauses)
  `(case ,switch
     ,@(mapcar #'(lambda (clause)
		   (cond ((member (car clause) '(nil otherwise))
			  `((,(car clause)) ,@(cdr clause)))
			  (t clause)))
	clauses)))

;--- selectq :: just like caseq
; except 'otherwise' is recogized as equivalent to 't' as a key
;
(defmacro selectq (switch &body clauses)
  `(case ,switch
     ,@(mapcar #'(lambda (clause)
		   (cond ((eq (car clause) 'nil)
			  `((,(car clause)) ,@(cdr clause)))
			 (t clause)))
	       clauses)))

;--- if :: macro for doing conditionalization
;
;  This macro is compatible with both the crufty mit-version and
; the keyword version at ucb.
;
;  simple summary:
;   non-keyword use:
;	(if a b) ==> (cond (a b))
;	(if a b c d e ...) ==> (cond (a b) (t c d e ...))
;   with keywords:
;	(if a then b) ==> (cond (a b))
;	(if a thenret) ==> (cond (a))
;	(if a then b c d e) ==> (cond (a b c d e))
;	(if a then b c  else d) ==> (cond (a b c) (t d))
;	(if a then b c  elseif d  thenret  else g)
;		==> (cond (a b c) (d) (t g))
;
;   
;
;
; In the syntax description below,
;    optional parts are surrounded by [ and ],
;    + means one or more instances.
;    | means 'or'
;    <expr> is an lisp expression which isn't a keyword
;       The keywords are:  then, thenret, else, elseif.
;    <pred> is also a lisp expression which isn't a keyword.
; 
; <if-stmt> ::=  <simple-if-stmt>
; 	       | <keyword-if-stmt>
; 
; <simple-if-stmt> ::=  (if <pred> <expr>)
; 		      | (if <pred> <expr> <expr>)
; 
; <keyword-if-stmt> ::= (if <pred> <then-clause> [ <else-clause> ] )
; 
; <then-clause> ::=  then <expr>+
; 		   | thenret
; 
; <else-clause> ::=  else <expr>+
; 		   | elseif <pred> <then-clause> [ <else-clause> ]
;

(proclaim '(special if-keyword-list))

(eval-when (compile load eval)
   (setq if-keyword-list '(then thenret elseif else)))

;--- if
;
;  the keyword if expression is parsed using a simple four state
; automaton.  The expression is parsed in reverse.
; States:
;	init - have parsed a complete predicate,  then clause
;	col  - have collected at least one non keyword in col
;	then - have just seen a then, looking for a predicate
;	compl - have just seen a predicate after an then, looking
;		for elseif or if (i.e. end of forms).
;
(defmacro if (&rest args)
   (let ((len (length args)))
      ;; first eliminate the non-keyword if macro cases
      (cond ((< len 2)
	     (error "if: not enough arguments " args))
	    ((and (= len 2)
		  (not (memq (cadr args) if-keyword-list)))
	     `(cond (,(car args) ,(cadr args))))
	    ; clause if there are not keywords (and len > 2)
	    ((do ((xx args (cdr xx)))
		 ((null xx) t)
		 (cond ((memq (car xx) if-keyword-list)
			(return nil))))
	     `(cond (,(car args) ,(cadr args))
		    (t ,@(cddr args))))
	    
	    ;; must be an instance of a keyword if macro
	    
	    (t (do ((xx (reverse args) (cdr xx))
		    (state 'init)
		    (elseseen nil)
		    (totalcol nil)
		    (col nil))
		   ((null xx)
		    (cond ((eq state 'compl)
			   `(cond ,@totalcol))
			  (t (error "if: illegal form " args))))
		   (cond ((eq state 'init)
			  (cond ((memq (car xx) if-keyword-list)
				 (cond ((eq (car xx) 'thenret)
					(setq col nil
					      state 'then))
				       (t (error "if: bad keyword "
						 (car xx) args))))
				(t (setq state 'col
					 col nil)
				   (push (car xx) col))))
			 ((eq state 'col)
			  (cond ((memq (car xx) if-keyword-list)
				 (cond ((eq (car xx) 'else)
					(cond (elseseen
						 (error
						    "if: multiples elses "
						    args)))
					(setq elseseen t)
					(setq state 'init)
					(push `(t ,@col) totalcol))
				       ((eq (car xx) 'then)
					(setq state 'then))
				       (t (error "if: bad keyword "
						 (car xx) args))))
				(t (push (car xx) col))))
			 ((eq state 'then)
			  (cond ((memq (car xx) if-keyword-list)
				 (error "if: keyword at the wrong place "
					(car xx) args))
				(t (setq state 'compl)
				   (push `(,(car xx) ,@col) totalcol))))
			 ((eq state 'compl)
			  (cond ((not (eq (car xx) 'elseif))
				 (error "if: missing elseif clause " args)))
			  (setq state 'init))))))))

(defmacro delete (elem lis &optional num)
   `(lisp:delete ,elem ,lis :count (if ,num ,num 1) :test #'equal))

(defmacro delq (elem lis &optional num)
   `(lisp:delete ,elem ,lis :count (if ,num ,num 1)))


(setf (symbol-function 'add) (symbol-function '+))
(setf (symbol-function 'add1) (symbol-function '1+))
(setf (symbol-function 'sub1) (symbol-function '1-))

(defmacro neq (a b) `(not (eq ,a ,b)))
(defmacro nequal (a b) `(not (equal ,a ,b)))
(defmacro copy (arg)  `(copy-tree ,arg))
(defmacro copysymbol (s x) `(copy-symbol ,s ,x))
(defmacro copylist (list) `(append ,list nil))
(defmacro symeval (sym) `(symbol-value ,sym))
(defmacro nthelem (n1 l1) `(nth (1- ,n1) ,l1))

;;; numeric
(defmacro diff (&rest args) `(- ,@args))
(defmacro greaterp (&rest args) `(> ,@args))
(defmacro lessp (&rest args) `(< ,@args))
(defmacro minus (arg) `(- ,arg))
(defmacro quotient (arg1 arg2) `(truncate ,arg1 ,arg2))
(defmacro remainder (arg1 arg2) `(rem ,arg1 ,arg2))
(defmacro times (&rest args) `(* ,@args))



(defmacro putprop (sym val prop)
   `(setf (get ,sym ,prop) ,val))

(defmacro aset (val arr &rest indices)
  `(setf (aref ,arr ,@indices) ,val))


(defmacro *catch (x y) `(catch ,x ,y))
(defmacro *throw (x y) `(throw ,x ,y))
(defmacro get_pname (sym) `(symbol-name ,sym))
(defmacro append1 (lis elem) `(append ,lis (cons ,elem nil)))

; actually not a franz macro
(defmacro rem-dups (lis) `(remove-duplicates ,lis :test #'equal))


;; rick
;     input/output

;     misc

(defmacro pntlen (arg)
  `(length (symbol-name ,arg)))

(defmacro errset (expr &optional (flag t))
  (declare (ignore flag))
  `(let ((value (catch *errset-flag*
		  ,expr)))
     (if (and (consp value)
	      (eq (car value) *errset-flag*))
	 nil
	 (list value))))

;; printing etc from RICK
(defmacro princ (form &optional stream &environment env)
  (setq form (macroexpand form env))
  (cond ((and (consp form)
	      (eq (car form) 'uformat))
	 `(format ,(cond ((eq stream 'nil) '*standard-output*)
			 ((eq stream 't) '*terminal-io*)
			 (t stream))
	          ,@(cdr form)))
	(t `(lisp:princ ,form ,stream))))

#-franz
(defun terpri (&optional stream)
  (lisp:terpri stream)
  (force-output stream)
)

(defmacro uconcat (&rest args)
  `(format nil ,(apply #'concatenate 'string
		       (mapcar #'(lambda (arg &aux v)
				   (if (and (constantp arg)
					    (stringp (setq v (eval arg))))
				       v
				       "~a"))
			       args))
            ,@(mapcan #'(lambda (arg)
			  (if (and (constantp arg)
				   (stringp (eval arg)))
			      nil
			      (list arg)))
	              args)))

