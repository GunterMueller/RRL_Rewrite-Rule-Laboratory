;; This file contains many definitions that are to be
;; used only in FRANZ lisp version. -- Siva. Jan 31, 1990.


#+franz (include "datamacs.l")

#+franz
(defun is-valid-var (char)
  ; Returns T iff CHAR is a valid variable; otherwise, NIL.
  ; A valid variable is a symbol with the first character being
  ; between 'u' and 'z' (i.e.  u <= CHAR(1) <= z).
  (not (or (numberp char)
	   (greaterp (getcharn char 1) (getcharn 'z 1))
	   (lessp (getcharn char 1) (getcharn 'u 1)))))

#+franz
(defun is-infix-op (op)
  ; A infix operator is a valid operator with arity 2 and starting with
  ; a character not in [a..z].
  (and (is-valid-op op) (not (letterp (getcharn op 1)))))

#+franz
(defun print-wash-file (exp file &aux port2)
  ; Remove "#:" from the content of "file".
  (setq port2 (car (errset (outfile "tmp.junk" 'b) nil)))
  (print exp port2)
  (close port2)
  (setq port2 (car (errset (infile "tmp.junk") nil)))
  (loop for ch = (my-tyi port2) 
	if (or (null ch) (eq ch -1)) return nil
	else if (eq ch #/#)
	       do (if (eq (my-tyipeek port2) #/:)
		      then (my-tyi port2)
		      else (tyo ch file))
	else do (tyo ch file))
  (close port2))

