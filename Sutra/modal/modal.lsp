(in-package "RRL")

;; this file contains the functions to translate a modal formula
;; into path logic format

; taken from "datamacs.lsp"

(defmacro make-term (op arg) `(cons ,op ,arg))
(defmacro op-of (term) `(car ,term))
(defmacro args-of (term) `(cdr ,term))
(defmacro first-arg (term) `(cadr ,term))
(defmacro second-arg (term) `(caddr ,term))

; end

; the make-new-variable function in term.lsp returns
; always the same variable name

(defun make-new-variable1 ()
  (newsym 'w)
)



(defun expand (path var)
  (make-term '! (list path var))
) 

(defun trans (path formula)
  (cond ((null formula) nil)
        (t (let ((t-op (op-of formula)))
           (cond ((equal t-op 'not)
                    (make-term t-op (list (trans path (first-arg formula)))))
                    
                 ((member t-op '(and or xor -> equ))
                    (make-term t-op (list (trans path (first-arg formula))
                                          (trans path (second-arg formula)))))
                                          
                 ((member t-op '(all exist))
                    (make-term t-op (list (first-arg formula)
                                          (trans path (second-arg formula)))))
                                          
                 ((equal t-op 'L)
                    (let ((new-var (make-new-variable1)))
                    (make-term 'all (list new-var
                                           (trans (expand path new-var)
                                                  (first-arg formula))))))
                                           
                 ((equal t-op 'M)
                    (let ((new-var (make-new-variable1)))
                    (make-term 'exist (list new-var
                                           (trans (expand path new-var)
                                                  (first-arg formula))))))

; everything else is considered to be a predicate
                 (t
                    (make-term t-op (cons path (args-of formula))))
           )
           )
         )
   )
)

(defun translate (formula)
  (initsym 'w)
  (trans '(eps) formula))
)




; taken from "refut.lsp"
;   and adapted for the modal proofs

(defun modal-refute-eqn (l1 &aux eqn)  
  (when l1 
    (setq eqn (car (last l1))
	  $eqn-set (append $eqn-set (delq eqn l1))
	  $guest-eqn eqn
	  
	  
	  eqn (negate-eqn eqn t)
	  $del_rule_str 1
	  $trace-proof t)

    (if $instant then
	(setq l1 (skolemize (lhs eqn))
	      $instant-seeds (get-instance-seeds l1)
	      eqn (change-lhs eqn l1))
	else (setq $instant-seeds nil))

    (push eqn $eqn-set)))



(defun modal-proof (&aux l1 chosen-system modal-system)
  (setq modal-system (ask-choice chosen-system '(t s4 s5)
                                 "Which modal system do you want ? "))
;  (princ "Now the Modal system ")
;  (princ modal-system)
;  (princ " should be loaded !")
;  (terpri) (terpri)

  (load-modal modal-system)
 
  (if (is-empty-line $in-port) then
      (princ "Input the modal formula you want to prove ")
      (terpri))
  (setq l1 (read-input t))

  (if l1 then
    (if (> (list-length l1) 1) then
      (terpri) (terpri)
      (princ "Only the first formula of your input is accepted ")
      (terpri)
      (print ')
    )

; the rest of the input equations is deleted
; from the input data structure, before it is passed
; to the refute function. only the formula is passed to
; the function

 ;   (setq l1 (change-lhs (car l1) (translate (lhs (car l1)))))
    
    (modal-refute-eqn (list (change-lhs (car l1) (translate (lhs (car l1))))))
    
    (setq $akb_flag nil)
    (start-kb)
   else
    (terpri) (terpri)
    (princ "No modal formula was provided")
    (terpri)
    (princ "No proof could be performed")
    (terpri) (terpri)
  )
)


;; path-length returns the length of a world path given as an argument

(defun path-length (path)
  (cond ((equal (car path) '!) (+ 1 (path-length (second path))))
        (t 0)
  )
)


;; max-path returns the longest path among the predicates in the given
;; formula


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

(defun load-modal (modal-system  &aux file)
  ; Load the modal system X from the file "X.rrl".
      (if (setq file (open-read-modal modal-system "rrl")) then
	  (setq $history (read file))
	  (undo1 t)
	  (restore-properties (read file))
	  (restore-rest-globals (read file))
	  (close file)
	  (terpri)))



(defun open-read-modal (modal-system &optional suffix)
  ; Read in the file name and try to open it to read for the system T.
  ; Look for the file 
  ; with the default suffix and in the example-directory, too.
  (let (filename port)
   (setq filename modal-system)
   (cond  ((setq port
	    (or (car (errset (infile filename) nil))
		(car (errset (infile (string-downcase filename)) nil))
		(car (errset (infile (uconcat filename "." suffix)) nil))
		(car (errset (infile (string-downcase
				       (uconcat filename "." suffix))) nil))
		(car (errset (infile (uconcat $example-dir filename)) nil))
		(car (errset (infile (uconcat user:*rrl-directory* "modal/" filename)) nil))
		(car (errset (infile (uconcat user:*rrl-directory* "modal/"
					      filename "." suffix)) nil))
		(car (errset (infile (uconcat $example-dir
					    filename "." suffix)) nil)))))
	  (t (princ (uconcat "   Error : Couldn't open file: " filename))
	     (terpri)))
      port))
