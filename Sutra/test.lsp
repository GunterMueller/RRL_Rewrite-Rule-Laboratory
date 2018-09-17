(setq *package* (find-package "RRL"))
; (pre-init)
(initialize)

(setq $eqn-set '(((f (e) x) x nil nil (user 1))
		 ((f (i x) x) (e) nil nil (user 2))
		 ((f (f x y) z) (f x (f y z)) nil nil (user 3))))

(putprop 'i 1 'arity)
(putprop 'e 0 'arity)
(putprop 'f 2 'arity)
(setq $trace_flag 2)
(setq $ac '(f))
(setq $glob_prec '((i f  e)))
