(in-package "USER")

(defconstant *lisp-type* ".lsp")

(defconstant *bin-type*
  #+kcl ".o"
  #+sparc ".sbin"
  #-sparc ".lbin"
  )

(defun file-date (file)
  (if (probe-file file) (or (file-write-date file) 0) 0))
(defun bin-is-current (subdir file)
  (< (file-date (source-name subdir file)) (file-date (obj-name subdir file))))
(defun source-name (subdir file)
  (concatenate 'string *rrl-directory* subdir file *lisp-type*))
(defun obj-name (subdir file)
  (concatenate 'string *rrl-directory* subdir file *bin-type*))

(defun fload (file &optional (subdir *code-directory*))
  (cond
   ((probe-file (source-name subdir  file))
    (if (bin-is-current subdir file) 
	(load (obj-name subdir file)) 
      (load (source-name subdir file))))
   ((probe-file (obj-name subdir file))(load (obj-name subdir file)))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file)))))

(defun bload (file &optional (subdir *code-directory*))
  (cond
   ((probe-file (obj-name subdir file)) (load (obj-name subdir file)))
   ((probe-file (source-name subdir file))
    (compile-file (source-name subdir file))
    (if (probe-file (obj-name subdir file)) 
	(load (obj-name subdir file))))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file))
      )))

(defun cload (file &optional (subdir *code-directory*))
  (cond
   ((probe-file (source-name subdir file))
    (when (not (bin-is-current subdir file))
	  ;;(format t "Already up to date: ~s~%" file)
	  (compile-file (source-name subdir file))
	  (if (probe-file (obj-name subdir file)) 
	      (load (obj-name subdir file)))))
   ((probe-file (obj-name subdir file))	(load (obj-name subdir file)))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file)))))

(defun cload2 (file &optional (subdir *code-directory*))
  (when (and (probe-file (source-name subdir file))
	     (not (bin-is-current subdir file)))
	(compile-file (source-name subdir file))
	(if (probe-file (obj-name subdir file)) 
	    (load (obj-name subdir file)))))

(defun fcload (file &optional (subdir *code-directory*))
  (if (probe-file (source-name subdir file))
      (progn (compile-file (source-name subdir file))
	     (if (probe-file (obj-name subdir file))
		 (load (obj-name subdir file))))
      (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file))))

(bload "sloop")
(use-package "SLOOP")

(defconstant $rrl-files
  '(
    "defvars" "franz" "datamacs" "miscel" 

    "operators" "term" "subst" "match" "acdio" "acunify"

    "input" "syntax" "output" "options" "initialize" "history" 

    "kb" "prove" "induc" 
    "precedence" "lrpo" "aclrpo" "order" "makerules"
    "pickrules" "critical" "normalize" 

    "cancel" "consist" "commut" "cyclerule" "typing" 
    "equality" "polynomial" "autoorder"

    "boolean" "boolring" "orderpc" "normbool" "pccrit"

    "condit" "premises"

    "scheme" "building" "abstract" "structure"

    "suffice" "narrow"

    "xtree" "xprover" "xrrl" "xmanual"
    ))

(defun lrrl () (dolist (f $rrl-files) (fload f)))
(defun crrl () (dolist (f $rrl-files) (cload2 f)))

(defvar $test-examples  ;; Examples for testing RRL.
  '(
    ;; Groups with three axioms.
    "test-g3" "test-x2e" 
    ;; Group with one axiom.
    "test-group1"
    ;; AC examples
    "test-acg3" "test-lattice1" "test-ring1" "test-ring3" 
    ;; Jim Christian's benchmarks:
    "test-acg16" "test-group16"
    ;; Nonassociative ring problems:
    "test-moufang"
    ;; Boolean Ring Method works:
    "test-andrews"
    ;; Kalman's axiomatization produces z22:
    "test-z22"
    ;; Boolean Algebra associativity problems:
    "test-associate"
    ))

(defun start-rrl() (start-up))
(defun start() (start-up)) 
(defun resume-rrl() (rrl))
	
(proclaim '(optimize (safety 0) (space 0) (speed 3)))
;; If you want faster code at the expense of longer compile time,
;; you should use the production mode of the compiler, which can be obtained
;; by evaluating (proclaim '(optimize (compilation-speed 0)))

(princ "==========================================================") (terpri)
(princ "Starting Load/Compile RRL Files ...") (terpri)
(princ "==========================================================") (terpri)

;; First, load all files to make sure all macros are loaded,
;; and then compile each updated file.
(lrrl) 
(crrl)

(princ "==========================================================") (terpri)
(princ "Finished Load/Compile RRL Files.") (terpri)
(princ "[To enter RRL, you may need to type (start)]") (terpri) 
(princ "==========================================================") (terpri)

#+lucid (start-up)



