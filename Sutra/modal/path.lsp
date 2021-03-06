(defmacro op-of (term) `(car ,term))
(defmacro args-of (term) `(cdr ,term))
(defmacro first-arg (term) `(cadr ,term))
(defmacro second-arg (term) `(caddr ,term))

(defmacro new-max (m1 m2) `(cond ((<, m1, m2), m2)
                                 (t, m1)))


(defvar $path-limit 0)

(defun path-length (path)
  (cond ((equal (car path) '!) (+ 1 (path-length (second path))))
        (t 0)
  )
)

(defun max-path (formula)
  (let ((t-op (op-of formula)))
    (cond ((equal t-op 'not)
                    (max-path (first-arg formula)))
        ((member t-op '(and or xor -> equ))
                    (new-max (max-path (first-arg formula))
                             (max-path (second-arg formula))))
        ((member t-op '(all exist))
                    (max-path (second-arg formula)))
        (t (path-length (first-arg formula)))
    )
  )
)

(defun compute-cp (lhs)
  (cond ((< (max-path lhs) $path-limit) 'ok)
        ( t  nil)
  )
)
