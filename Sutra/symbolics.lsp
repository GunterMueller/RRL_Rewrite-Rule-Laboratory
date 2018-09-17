;;; -*- Mode: LISP; Syntax: Common-lisp; Package: User; Base: 10; -*-

(if (not (find-package "RRL")) (make-package "RRL"))
(load "rrl")
(compile-rrl)
(setq *package* (find-package "RRL"))

