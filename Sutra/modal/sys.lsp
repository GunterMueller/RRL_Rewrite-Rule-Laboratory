;; this is to be loaded from Stefan (not Common Lisp).
;; assumes RRL-files are already loaded correctly.

(in-package 'user)

(defparameter *modal-files*
  '("work"))

(setq *rrl-files* *modal-files*)

(time (compile-rrl))


