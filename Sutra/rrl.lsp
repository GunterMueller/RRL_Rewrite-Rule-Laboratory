;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-franz
(in-package 'user)

#+lispm
(if (not (find-package "RRL")) (make-package "RRL"))

#+franz (load "frz-rrl")

;;;----------------------------------------------------------------------
;;; Add ".lsp" as known source file extension for loading and compiling.

#+allegro
(progn
  (let ((tail (member (make-pathname :type "cl")
		      sys:*load-search-list* :test #'equal)))
    (setq sys:*load-search-list*
	  (append (ldiff sys:*load-search-list* tail)
		  (list (make-pathname :type "lsp"))
		  tail)))
  (push "lsp" sys:*source-file-types*)
)
#+lucid
(setq sys:*load-source-pathname-types*
      (cons (first sys:*load-source-pathname-types*)
	    (cons "lsp"
		  (rest sys:*load-source-pathname-types*)
	    )))

;;;----------------------------------------------------------------------

(defun getenv (name)
  (progn nil
         #+kcl (si:getenv (string name))
         #+ibcl (si:getenv (string name))
         #+allegro (sys:getenv (string name))
         #+lucid (sys:environment-variable (string name))
  )
)


(defparameter *rrl-proclaim*
  '(optimize (safety 1) (space 3) (speed 3)))

(defvar *rrl-directory* (or (getenv "PWD") ""))

(if *rrl-directory* (setq *rrl-directory*
                      (concatenate 'string *rrl-directory* "/")))

(export '*rrl-directory*)


;;  #-lispm "/usa/siva/crrl/"
;;  #+lispm "D:>rrl>"

(defparameter *rrl-pathname-extensions* ; Modified from pcl/defsys.lisp
  (let ((files-renamed-p t)
        (proper-extensions
          (car
           '(
	     #+allegro				 ("lsp"   . "fasl")
	     #+(and Genera (not imach))          ("lisp"  . "bin")
	     #+(and Genera imach)                ("lisp"  . "ibin")
             #+(and dec common vax (not ultrix)) ("LSP"   . "FAS")
             #+(and dec common vax ultrix)       ("lsp"   . "fas")
             #+KCL                               ("lsp"   . "o")
             #+IBCL                              ("lsp"   . "o")
             #+Xerox                             ("lisp"  . "dfasl")
	     #+(and lucid HP)                    ("lsp"   . "b")
             #+(and Lucid MC68000)               ("lsp"   . "lbin")
             #+(and Lucid VAX)                   ("lsp"   . "vbin")
             #+(and Lucid Prime)                 ("lsp"   . "pbin")
	     #+(and Lucid SUNRise)               ("lsp"   . "sbin")
	     #+(and Lucid SPARC)                 ("lsp"   . "sbin")
             #+(and Lucid IBM-RT-PC)             ("lsp"   . "bbin")
	     #+excl                              ("lsp"   . "fasl")
             #+:CMU                              ("slisp" . "sfasl")
             #+HP                                ("lsp"   . "b")
             #+TI ("lisp" . #.(string (si::local-binary-file-type)))
             #+:gclisp                           ("LSP"   . "F2S")
             #+pyramid                           ("clisp" . "o")
             #+:coral                            ("lisp"  . "fasl")
             ))))
    (cond ((null proper-extensions) '("l" . "lbin"))
          ((null files-renamed-p) (cons "l" (cdr proper-extensions)))
          (t proper-extensions))))

; :object :newest :lisp
(defvar *rrl-load-version-default* :newest)
(defvar *rrl-default-compile-args* nil)
(defvar *rrl-default-load-args* nil)

(defun lisp-file (file)
  (concatenate 'string *rrl-directory* file "."
	       (car *rrl-pathname-extensions*)))

(defun fasl-file (file)
  (concatenate 'string *rrl-directory* file "."
	       (cdr *rrl-pathname-extensions*)))

(defparameter *sutra-files*
  '("bug-fixes"
    "defvars" #-lispm "cl-loop" "cl-frzmacs" "datamacs"
    "cl-frzfuns" "help"
    "term" "miscel" "ac-match" "ac-unify" "ac" "orderpc" "dioph"
"uni-match" ; clean versions for non-AC
    "subst" "operators" "boolean" "initialize" "critical"
    "kb" "history" "normalize" "normstrat" "lrpo" "order"
    "precedence" "cancel" "makerules" "consist" "commut"
    "set" "pickrules" "output" "suggprec" "normbool"
    "aclrpo" "polynomial" "cyclerule" "coverrule" "typing"
    "statistics" "toplevel" "syntax"
    "cl-input" "options" "autoorder"
    "condit" "building" "premises" "prem-norm"
    "prove" "induc" "suffic" "narrow" "abstract"
    "quasired" "paramod" "skolem" "pccrit" "assertion"
    "refut" "conject" "testset" "equality" "structure"
    "saveload" ))

(defparameter *solve-files*
  '("solve/var-macs" "solve/compile" "solve/solve"
    "solve/successors" "solve/normalize" "solve/output" "solve/ac"))

(defparameter *modal-files*
  '("modal/modal"))

(defvar *rrl-files*        ;; *sutra-files*
  (append *sutra-files* *solve-files* *modal-files*))

;; file-data is (truename file-write-date)
(defvar *rrl-loaded-file-table* (make-hash-table :test 'equal))

(defun fwd (file)
  (if (probe-file file)
      (file-write-date file)
      0))

(defun compile-rrl-file (file &key force-p
			      (compile-args *rrl-default-compile-args*))
  (proclaim *rrl-proclaim*)
  (let* ((lisp-file (lisp-file file))
	 (fasl-file (fasl-file file)))
    (when (or force-p
	      (> (fwd lisp-file) (fwd fasl-file)))
      (apply #'compile-file lisp-file compile-args))))

(defun load-rrl-file (file &key force-p
			   (load-version *rrl-load-version-default*)
			   (load-args *rrl-default-compile-args*))
  (let* ((lisp-file (lisp-file file))
	 (fasl-file (fasl-file file))
	 (file-to-load (case load-version
			 (:lisp lisp-file)
			 (:object fasl-file)
			 (:newest (if (> (fwd lisp-file) (fwd fasl-file))
				      lisp-file
				      fasl-file))
			 (t (error "Invalid load-version")))))
    (let ((file-data (gethash file *rrl-loaded-file-table*))
	  (new-file-data (cons (truename file-to-load) (fwd file-to-load))))
      (when (or force-p
		(not (equal file-data new-file-data)))
	(apply #'load file-to-load load-args)
	(setf (gethash file *rrl-loaded-file-table*) new-file-data)))))

(defmacro with-compiler-warnings-context (&body forms)
  `(#+Genera compiler:compiler-warnings-context-bind
    #+TI COMPILER:COMPILER-WARNINGS-CONTEXT-BIND
    #+:LCL3.0 lucid-common-lisp:with-deferred-warnings
    #-(or Genera TI :LCL3.0) progn
    ,@forms))

(defun compile-rrl (&key force-p
			 (force-compile-p force-p)
			 (force-load-p force-p)
			 (compile-args *rrl-default-compile-args*)
			 (load-version *rrl-load-version-default*)
			 (load-args *rrl-default-compile-args*))
  (with-compiler-warnings-context
   (dolist (file *rrl-files*)
     ;; Sometimes need to load before compile to define macros used.
     (load-rrl-file file
		    :force-p :lisp
		    :load-version load-version
		    :load-args load-args)
     (compile-rrl-file file
		       :force-p force-compile-p
		       :compile-args compile-args)
     (load-rrl-file file
		    :force-p force-load-p
		    :load-version load-version
		    :load-args load-args)
   )))

(defun load-rrl (&key force-p
		      (force-load-p force-p)
		      (load-version *rrl-load-version-default*)
		      (load-args *rrl-default-compile-args*))
  (dolist (file *rrl-files*)
    (load-rrl-file file :force-p force-load-p :load-version load-version :load-args load-args)))

#-franz
(time (compile-rrl))


#-franz
(defun start-rrl() 
 (let ((*package* (find-package "RRL")))
   (rrl:start-up)
 ))

(defun resume-rrl()
  (let ((*package* (find-package "RRL")))
   (rrl:rrl)
 ))

