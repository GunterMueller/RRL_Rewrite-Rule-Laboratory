(in-package "USER")

;; $herky-directory is the herky top directory. 
;; It has the following structure:
;;                     $herky-directory
;;                    /    |     \   \            [ ] -- optional.
;;                  code  test  [lab] [hiper] 

(defconstant $herky-directory "/home/zambini/csf/hzhang/herky/")

;; You may move the test directory anywhere and then change the following
;; definition accordingly.
(defconstant $example-directory
  (concatenate 'string $herky-directory "test/"))


;; The kerky files' default suffix is ".lisp", except the file "init.lsp".
(defconstant $lisp-type ".lisp")

;; If your lisp produces a binary file with different suffix, you have
;; to change the following definition accordingly.
(defconstant $bin-type
  #+kcl ".o"
  #+sparc ".sbin"
  #+lucid ".rbin"
  #-sparc ".lbin"
  )

;;; If you want faster code at the expense of longer compile time,
;;; you should use the production mode of the compiler, which can be obtained
;;; by evaluating
;; (proclaim '(optimize (compilation-speed 0)))
(proclaim '(optimize (safety 0) (space 0) (speed 3)))

;; HERKY can run faster if one or all of the following constants are 
;; set to t. When one of these constants is changed, all the files have 
;; to recompiled (by deleting all the binary files).
(defconstant *no-time-counting* t)
(defconstant *no-trace-message* nil)
(defconstant *no-type-checking* t)

;; Load/Compile HERKY files.
(load (concatenate 'string $herky-directory "code/herky.lisp"))
