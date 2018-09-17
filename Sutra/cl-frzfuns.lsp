;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#-franz (in-package "RRL")


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
  (if (null l1) l2
    (if (null l2) l1
      (loop while (and l1 l2)
	    with ans = nil do
	    (push (if (funcall fn (car l1) (car l2))
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
            ((and nodups (member x l)) l)
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
  (if (probe-file filename)
      (open filename :direction :input)
      (throw *errset-flag* (list *errset-flag* "File not found"))))

(defun outfile (filename &optional mode)
  (when (and mode 
	     (let ((string (string mode)))
	       (and (plusp (length string))
		    (char-equal #\a (aref string 0)))))
    (error "append mode is not supported"))
  (open (string filename) :direction :output))

(defun pp (form)
  (pprint form))
  
(defun readc (&optional port eof)
  (unless port (setq port piport))
  (let ((char (read-char port nil nil)))
    (if (null char)
	eof
	(char-ascii char))))


(defun tab (col &optional port)
  (format (or port poport) "~VT" col))


(defun tyi (&optional port)
  (or (readc port) -1))

(defun tyipeek (&optional port)
  (unless port (setq port piport))
  (let ((char (peek-char nil port nil nil)))
    (if (null char)
	-1
	(char-ascii char))))

(defun tyo (char &optional port)
  (unless port (setq port poport))
  (write-char (ascii-char char) port))


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

(defun getenv (name)
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
#+:lucid (defun bye () (sys:quit))

;; from Rick.
(defun subpair (old new expr)
  (sublis (mapcar #'cons old new) expr))

; works for 1 or 2 dim arrays only
; can be called with singleton vec
(defun fillarray (array list)
  (let ((dimensions (array-dimensions array)) last)
    (case (length dimensions)
      (1 (dotimes (i (first dimensions))
	   (setf (aref array i) (if (null list) last (setq last (pop list))))))
      (2 (dotimes (i (first dimensions))
	   (dotimes (j (second dimensions))
	     (setf (aref array i j) (if (null list) last (setq last (pop list)))))))
      (t (error "fillarray is implemented only for arrays of rank 1 and 2"))))
  array)

(defun listarray (array &optional number)
  (let ((dimensions (array-dimensions array)) result)
    (case (length dimensions)
      (1 (dotimes (i (first dimensions))
	   (when number (if (zerop number) (return nil) (decf number)))
	   (push (aref array i) result)))
      (2 (dotimes (i (first dimensions))
	   (dotimes (j (second dimensions))
	     (when number (if (zerop number) (return nil) (decf number)))
	     (push (aref array i j) result))))
      (t (error "listarray is implemented only for arrays of rank 1 and 2")))
    (nreverse result)))

;; not a macro as it is funcalled.
(defun ncons(a)
  (cons a nil))
