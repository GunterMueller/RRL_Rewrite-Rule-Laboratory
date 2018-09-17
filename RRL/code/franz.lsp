;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#-franz (in-package "USER")

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

;(shadow '(
;          lisp:if   ;; if*
;          lisp:eq
;          lisp:princ ;; princ0
;          lisp:terpri
;          lisp:type-of 
;          lisp:remove ;; remove0
;          lisp:delete ;; delete0
;          lisp:member ;; member0
;          lisp:assoc  ;; assoc0
;          lisp:subst  ;; subst0
;          lisp:position
;         ))

;(defmacro eq (e1 e2) 
;#+kcl `(lisp:equal ,e1 ,e2)
;#-kcl `(lisp:eq ,e1 ,e2)
;)

;; franz uses equal test.
(defmacro subst0 (new old tree)
  `(lisp:subst ,new ,old ,tree :test #'equal))


(defmacro member0 (x list)
  `(lisp:member ,x ,list :test #'equal))
#+kcl (defmacro memq (x list) `(lisp:member ,x ,list)) 
(defmacro member-equal (x list)
  `(lisp:member ,x ,list :test #'equal))

#+kcl (defmacro assq (a b) `(lisp:assoc ,a ,b))
(defmacro assoc0 (a b) `(lisp:assoc ,a ,b :test #'equal))

;; equal test for remove like member bcos of ac-match etc.
(defmacro remove0 (elem lis &optional (num 1))
  `(lisp:remove ,elem ,lis :count ,num :test #'equal))

(defmacro remq (x list &optional n)
  `(lisp:remove ,x ,list ,@(when n `(:count ,n))))

;--- caseq
; use is 
;    (caseq expr
;            (match1 do1)
;            (match2 do2)
;            (t  doifallelsefails))
; the matchi can be atoms in which case an 'eq' test is done, or they
; can be lists in which case a 'memq' test is done.
;

(defmacro caseq (switch &body clauses)
  `(case ,switch
     ,@(mapcar #'(lambda (clause)
                   (cond ((member0 (car clause) '(nil otherwise))
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

;--- if* :: macro for doing conditionalization
;
;  This macro is compatible with both the crufty mit-version and
; the keyword version at ucb.
;
;  simple summary:
;   non-keyword use:
;        (if* a b) ==> (cond (a b))
;        (if* a b c d e ...) ==> (cond (a b) (t c d e ...))
;   with keywords:
;        (if* a then b) ==> (cond (a b))
;        (if* a thenret) ==> (cond (a))
;        (if* a then b c d e) ==> (cond (a b c d e))
;        (if* a then b c  else d) ==> (cond (a b c) (t d))
;        (if* a then b c  elseif d  thenret  else g)
;                ==> (cond (a b c) (d) (t g))
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
;                | <keyword-if-stmt>
; 
; <simple-if-stmt> ::=  (if* <pred> <expr>)
;                       | (if* <pred> <expr> <expr>)
; 
; <keyword-if-stmt> ::= (if* <pred> <then-clause> [ <else-clause> ] )
; 
; <then-clause> ::=  then <expr>+
;                    | thenret
; 
; <else-clause> ::=  else <expr>+
;                    | elseif <pred> <then-clause> [ <else-clause> ]
;

(proclaim '(special if-keyword-list))

(eval-when (compile load eval)
   (setq if-keyword-list '(then thenret elseif else)))

;--- if
;
;  the keyword if expression is parsed using a simple four state
; automaton.  The expression is parsed in reverse.
; States:
;        init - have parsed a complete predicate,  then clause
;        col  - have collected at least one non keyword in col
;        then - have just seen a then, looking for a predicate
;        compl - have just seen a predicate after an then, looking
;                for elseif or if (i.e. end of forms).
;
(defmacro if* (&rest args)
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

(defmacro delete0 (elem lis &optional (num 1))
   `(lisp:delete ,elem ,lis :count ,num :test #'equal))

#+kcl (defmacro delq (elem lis &optional (num 1))
   `(lisp:delete ,elem ,lis :count ,num))


(setf (symbol-function 'add) (symbol-function '+))
(setf (symbol-function 'add1) (symbol-function '1+))
(setf (symbol-function 'sub1) (symbol-function '1-))

(defmacro neq (a b) `(not (equal ,a ,b)))
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

;; printing etc from RICK
(defmacro princ0 (form &optional stream &environment env)
  (setq form (macroexpand form env))
  (cond ((and (consp form)
              (eq (car form) 'uformat))
         `(format ,(cond ((eq stream 'nil) '*standard-output*)
                         ((eq stream 't) '*terminal-io*)
                         (t stream))
                  ,@(cdr form)))
        (t `(lisp:princ ,form ,stream))))

; (defun terpri (&optional stream)
;  (lisp:terpri stream)
;  (force-output stream)
;)

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

;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

;#-franz (in-package "USER")


;; 
;; This file has functions available in franz but not in common
;; that RRL uses. Some are borrowed from Franz sources.
;; Some re-implemented.          -- Siva.
;;
;;

(defun alphalessp (s1 s2)
  (cond ((symbolp s1) (string< (symbol-name s1) (symbol-name s2)))
	((stringp s1) (string< s1 s2))
	(t)))

;borrowed from Franz
(defun attach (x y)
  (cond ((atom y) "ERROR attaching to atom")
	(t (rplacd y (cons (car y) (cdr y)))
	   (rplaca y x))))

(defun merge-list (l1 l2 fn)
  (if* (null l1) l2
    (if* (null l2) l1
      (sloop while (and l1 l2)
	    with ans = nil do
	    (push (if* (funcall fn (car l1) (car l2))
		      (pop l1) (pop l2)) ans)
            finally (return (nconc (reverse ans) l1 l2))))))

(defun Cnth(x n)
           (cond ((> 1 n) (cons nil x))
                 (t
                    (prog nil
                     lp   (cond ((or (atom x) (= n 1)) (return x)))
                          (setq x (cdr x))
                          (setq n (1- n))
                          (go lp)))))


(defun insert (x l comparefn nodups)
      (cond ((null l) (list x))
            ((atom l) (error "an atom, can't be inserted into" l))
            ((and nodups (member0 x l)) l)
            (t (cond
                ((null comparefn) (setq comparefn (function alphalessp))))
               (prog (l1 n n1 y)
                     (setq l1 l)
                     (setq n (length l))
                a    (setq n1 (truncate (1+ n) 2))
                     (setq y (Cnth l1 n1))
                     (cond ((< n 3)
                            (cond ((funcall comparefn x (car y))
                                   (cond
                                    ((not (equal x (car y)))
                                     (rplacd y (cons (car y) (cdr y)))
                                     (rplaca y x))))
                                  ((= n 1) (rplacd y (cons x (cdr y))))
                                  ((funcall comparefn x (cadr y))
                                   (cond
                                    ((not (equal x (cadr y)))
                                     (rplacd (cdr y)
                                             (cons (cadr y) (cddr y)))
                                     (rplaca (cdr y) x))))
                                  (t (rplacd (cdr y) (cons x (cddr y))))))
                           ((funcall comparefn x (car y))
                            (cond
                             ((not (equal x (car y)))
                              (setq n (sub1 n1))
                              (go a))))
                           (t (setq l1 (cdr y)) (setq n (- n n1)) (go a))))
               l)))


(defun drain (&optional port)
  (unless port (setq port poport))
  (clear-output poport))

(defun infile (filename)
  (setq filename (string filename))
  (if (probe-file filename) (open filename :direction :input)))

(defun outfile (filename)
  (open (string filename) :direction :output))

(defun pp (form)
  (pprint form))
  
#+lucid (defmacro char-ascii (char) `(char-code ,char))
; (defmacro ascii-char (ascii) `,ascii)

(defun readc (&optional port eof)
  (unless port (setq port piport))
  (let ((char (read-char port nil nil)))
    (if* (null char)
	eof
	(char-ascii char))))


(defun tab (col &optional port)
  (format (or port poport) "~VT" col))


(defun tyi (&optional port)
  (or (readc port) -1))

(defun tyipeek (&optional port)
  (unless port (setq port piport))
  (let ((char (peek-char nil port nil nil)))
    (if* (null char)
	-1
	(char-ascii char))))

;(defun tyo (char &optional port)
;  (unless port (setq port poport))
;  (write-char (ascii-char char) port))


(defun makesym (symbol index)
  (intern (format nil "~a~d" symbol index) *rrl-package*))

(defun initsym (&optional symbol)
  (makesym symbol (setf (get symbol 'symctr) 0)))

(defun newsym (&optional symbol)
  (makesym symbol (incf (get symbol 'symctr))))

(defun allsym (&optional symbol &aux result)
  (dotimes (i (or (get symbol 'symctr) 0))
    (push (makesym symbol i) result))
  result)

#+kcl (defun getenv (name)
  (progn nil
         #+kcl (si:getenv (string name))
         #+ibcl (si:getenv (string name))
	 #+allegro (sys:getenv (string name))
	 #+lucid (sys:environment-variable (string name))
  )
)

(defun reset ()
  (throw 'reset '*reset*))


#+lispm (defun bye() (exit))
#+:allegro (defun bye () (excl:exit))
;#+:lucid (defun bye () (quit))
;#-kcl (defun bye() (quit))

;; from Rick.
(defun subpair (old new expr)
  (sublis (mapcar #'cons old new) expr))

; works for 1 or 2 dim arrays only
; can be called with singleton vec
(defun fillarray (array list)
  (let ((dimensions (array-dimensions array)) last)
    (case (length dimensions)
      (1 (dotimes (i (first dimensions))
	   (setf (aref array i) (if* (null list) last (setq last (pop list))))))
      (2 (dotimes (i (first dimensions))
	   (dotimes (j (second dimensions))
	     (setf (aref array i j) (if* (null list) last (setq last (pop list)))))))
      (t (error "fillarray is implemented only for arrays of rank 1 and 2"))))
  array)

(defun listarray (array &optional number)
  (let ((dimensions (array-dimensions array)) result)
    (case (length dimensions)
      (1 (dotimes (i (first dimensions))
	   (when number (if* (zerop number) (return nil) (decf number)))
	   (push (aref array i) result)))
      (2 (dotimes (i (first dimensions))
	   (dotimes (j (second dimensions))
	     (when number (if* (zerop number) (return nil) (decf number)))
	     (push (aref array i j) result))))
      (t (error "listarray is implemented only for arrays of rank 1 and 2")))
    (nreverse result)))

;; not a macro as it is funcalled.
(defun ncons(a)
  (cons a nil))
