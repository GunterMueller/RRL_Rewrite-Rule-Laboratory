#-franz
(in-package "RRL")

;;; This file contains code to workaround bugs in various implementations of
;;; Lisp.  If the bug can be fixed using a stand-alone definition, put it
;;; here.  In-line fixes may still be scattered thoughout other files.
;;;
;;; Note that some of these may be fixed in newer releases, so say what version
;;; the bug occurs in, and check if the fix is still needed for newer version.


#+allegro
;;; Workaround ACL 3.0.3 bug where explicit NIL for stream fails.
(progn
  (setq excl:*compile-advice* t)
  (excl:defadvice read-preserving-whitespace (fix-for-nil-stream :before)
    (when (and excl:arglist
	       (null (first excl:arglist)))
      (setq excl:arglist (cons *standard-input* (rest excl:arglist)))
    ))
)


#+lucid
;;; In Lucid 2.15, at least some input routines cannot handle an explicit NIL
;;; stream.
(progn
  (sys:defadvice (peek-char fix-for-nil-stream)
		 (&optional peek-type stream &rest other-args)
     (sys:apply-advice-continue peek-type
				(or stream *standard-input*)
				other-args)
  )
  (sys:defadvice (read-char fix-for-nil-stream)
		 (&optional stream &rest other-args)
     (sys:apply-advice-continue (or stream *standard-input*) other-args)
  )
  (sys:defadvice (clear-input fix-for-nil-stream)
		 (&optional stream &rest other-args)
     (sys:apply-advice-continue (or stream *standard-input*) other-args)
  )
)
