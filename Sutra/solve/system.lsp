;; this is to be loaded from Sutra (not Common Lisp).
;; assumes RRL-files are already loaded correctly.

(in-package 'user)

(defparameter *solve-files*
  '("var-macs" "compile" "solve"
    "successors" "normalize" "output" "ac"))

(setq *rrl-files* *solve-files*)

(time (compile-rrl))


