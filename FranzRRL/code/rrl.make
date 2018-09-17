(sstatus dumpmode 413)		; starts faster...
(sstatus translink on)		; runs faster but can't look at stack.
(load "rrl.files")
(dumplisp nrrl)
(terpri) (princ "New version RRL is made in nrrl.") (terpri)
(exit)
