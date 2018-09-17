(in-package "USER")

(defun file-date (file)
  (if (probe-file file) (or (file-write-date file) 0) 0))
(defun bin-is-current (subdir file)
  (< (file-date (source-name subdir file)) (file-date (obj-name subdir file))))
(defun source-name (subdir file)
  (concatenate 'string $herky-directory subdir file $lisp-type))
(defun obj-name (subdir file)
  (concatenate 'string $herky-directory subdir file $bin-type))

(defun fload (file &optional (subdir "code/"))
  (cond
   ((probe-file (source-name subdir  file))
    (if (bin-is-current subdir file) 
	(load (obj-name subdir file)) 
      (load (source-name subdir file))))
   ((probe-file (obj-name subdir file))(load (obj-name subdir file)))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file)))))

(defun bload (file &optional (subdir "code/"))
  (cond
   ((probe-file (obj-name subdir file)) (load (obj-name subdir file)))
   ((probe-file (source-name subdir file))
    (compile-file (source-name subdir file))
    (if (probe-file (obj-name subdir file)) 
	(load (obj-name subdir file))
      (format t "************* File does not exist: ~s ~%" 
	      (obj-name subdir file))
      ))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file))
      )))

(defun cload (file &optional (subdir "code/"))
  (cond
   ((probe-file (source-name subdir file))
    (when (not (bin-is-current subdir file))
	  ;;(format t "Already up to date: ~s~%" file)
	  (compile-file (source-name subdir file))
	  (if (probe-file (obj-name subdir file)) 
	      (load (obj-name subdir file))
	    (format t "************* File does not exist: ~s ~%" 
		    (obj-name subdir file))
	    )))
   ((probe-file (obj-name subdir file))	(load (obj-name subdir file)))
   (t (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file)))))

(defun cload2 (file &optional (subdir "code/"))
  (when (and (probe-file (source-name subdir file))
	     (not (bin-is-current subdir file)))
	(compile-file (source-name subdir file))
	(if (probe-file (obj-name subdir file)) 
	    (load (obj-name subdir file))
	  (format t "************* File does not exist: ~s ~%" 
		  (obj-name subdir file))
	  )))

(defun fcload (file &optional (subdir "code/"))
  (if (probe-file (source-name subdir file))
      (progn (compile-file (source-name subdir file))
	     (if (probe-file (obj-name subdir file))
		 (load (obj-name subdir file))
	       (format t "************* File does not exist: ~s ~%" 
		       (obj-name subdir file))
	       ))
      (format t "************* File does not exist: ~s ~%" 
	      (source-name subdir file))))

(bload "sloop")
(use-package "SLOOP")

(defconstant $herky-files
	'("defs" "utility" 
	  "symbols" "terms" "axioms" "rules"
	  "parser" "input" "output"
	  "lrpo" "order" "match" "rewrite" "unify" "critical"
	  "initialize" "kb" "options" "prove" "equality" 
	  "ackb" "acsuper" "acdio"
	  "boolkb" "boolsuper" "boolring" 
	  "polykb" "polynorm"
	  "distree" "distreekb" "acdistree"
	  ))

(defun lherky () (dolist (f $herky-files) (fload f)))
(defun cherky () (dolist (f $herky-files) (cload2 f)))

(defvar $hiper-files 
  '("hi-globals" "hi-symbols" 
    "hi-arrays" "hi-stacks" "hi-queues" 
    "hi-misc" "hi-flatterms" 
    "hi-equal" "hi-copy" "hi-print" "hi-read"
    "hi-unify" "hi-match" 
    "hi-nodes" "hi-reduce" "hi-pairs" "hi-orient"
    "hi-enodes" "hi-permuters"
    "hi-kborder" "hi-rpo" "hi-kbrpo" "hi-autorpo"
    "hi-newf"
    "hi-main"))
(defvar $hiper-loaded nil) ;; t iff the code of "hiper" is loaded.

(defun lhiper () (dolist (f $hiper-files) (fload f "hiper/")))
(defun chiper () (dolist (f $hiper-files) (cload f "hiper/")))

(defvar $test-examples  ;; Examples for testing HERKY.
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
	
(proclaim '(optimize (safety 0) (space 0) (speed 3)))
;;; If you want faster code at the expense of longer compile time,
;;; you should use the production mode of the compiler, which can be obtained
;;; by evaluating
;; (proclaim '(optimize (compilation-speed 0)))

(princ "==========================================================") (terpri)
(princ "Loading/Compiling HERKY Files ...") (terpri)
(princ "==========================================================") (terpri)

;; First, load all files to make sure all macros are loaded,
;; and then compile each updated file.
(lherky) 
(cherky)

(princ "==========================================================") (terpri)
(princ "Loading/Compiling HERKY Files Finished.") (terpri)
(princ "  [You may need to type (init) to enter HERKY.]") (terpri)
(princ "==========================================================") (terpri)

(startup)


