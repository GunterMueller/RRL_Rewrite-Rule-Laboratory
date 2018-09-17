;; Copy this file to the directory where you like to run RRL, then
;; invoke AKCL (or any other Common Lisp) in that directory.
;; If your common lisp cannot automatically load the file "init.lsp",
;; type the lisp command (load "init.lsp").

(in-package 'user)

(defconstant *rrl-directory* "/home/zambini/csf/hzhang/crrl/")
(defconstant *code-directory* "code/") 
(defvar $example-directory (concatenate 'string *rrl-directory* "induc/"))
(defun rrlload (file) (load (concatenate 'string *rrl-directory* *code-directory* file)))

(rrlload "rrl.lsp")
