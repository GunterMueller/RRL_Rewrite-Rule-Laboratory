(in-package "USER")

;;; This file contains functions for handling function and variable 
;;; symbols.

(defmacro every-ops ()
  `(sloop for i from *first-user-op* below $num-ops
	  if (op-name i)
	  collect i))

;; Operators are represented as integers beginning 0, endging at *max-ops*.
;;
;;; [-*max-vars-all*, ..., -1, 0, 1, ..., *predef-ops*, ... *max-ops*]
;;; \---------------------- /     \-----------/  \-----------------/     
;;;        variables                user-ops      pre-defined-ops

;; Access operations for symbol arrays
(defmacro op-name (i)
  `(aref (the (array t) $op-names) (the fixnum ,i)))

(defmacro set-arity (i a)  `(setf (aref $op-arities ,i) ,a))
(defmacro get-arity (i) `(aref $op-arities ,i))
(defmacro has-arity (i) `(> (get-arity ,i) -1))
(defmacro is-constant-op (op) `(= (get-arity ,op) 0))

(defmacro get-arity2 (i) `(aref $op-arities2 ,i))
(defmacro set-arity2 (i types)  `(setf (aref $op-arities2 ,i) ,types))

(defmacro predicatep (op) `(= (aref $op-pred ,op) 1))
(defmacro set-predicate (op) `(setf (aref $op-pred ,op) 1))

(defmacro is-type-predicate (op)
  `(and	(predicatep ,op)
	(= (get-arity ,op) 1)
	(> (length (op-name ,op)) 2)
	(equal (char (op-name ,op) 0) #\i)
	(equal (char (op-name ,op) 1) #\s)))

(defmacro is-infix-op (op) `(member ,op $infix-ops))
(defmacro set-infix (op) `(query-insert ,op $infix-ops))

(defmacro set-op-status (op status)
  `(case ,status
     (lr (query-insert ,op $l-st-list))
     (rl (query-insert ,op $r-st-list))))
(defmacro op-has-lr-status (op) `(member ,op $l-st-list))
(defmacro op-has-rl-status (op) `(member ,op $r-st-list))
(defmacro op-has-status (op) `(or (member ,op $l-st-list) (member ,op $r-st-list)))
(defmacro get-op-status-name (op)
  `(if* (member ,op $l-st-list) then 'lr
	elseif (member ,op $r-st-list) then 'rl))
(defmacro rem-op-status (op) 
  `(and (setq $l-st-list (delete1 ,op $l-st-list))
	(setq $r-st-list (delete1 ,op $r-st-list))))
(defun cancel-status (op)
  (format $out-port "~%~s has been given the status ~s. "
	  (op-name op) (get-op-status-name op))
  (princ " Now, the status is cancelled." $out-port) (terpri $out-port)
  (rem-op-status op))

(defmacro ac-op-p (op) `(memq ,op $ac))
(defmacro set-commutative (op) `(push ,op $commutative))
(defmacro comm-op-p (op) `(memq ,op $commutative))
(defmacro assoc-op-p (op) `(memq ,op $associative))
(defmacro commutativep (op) `(or (ac-op-p ,op) (comm-op-p ,op)))

(defmacro set-constructor (op) `(push ,op $constructors))
(defmacro constructorp (op) `(memq ,op $constructors))
(defmacro is-free-constructor (op) `(memq ,op $free-constructors))

;; Return t iff "op" is a skolem function.
(defmacro is-skolem-op (op) `(memq ,op $skolem-ops))

(defmacro get-noncons ()
  ; Returns all the non-constructor
  `(sloop for op from *first-user-op* below $num-ops
	  if (not (memq op $constructors)) 
	  collect op))

(defmacro op-weight (i)
  `(the fixnum (aref (the (array fixnum) $op-weights) (the fixnum ,i))))
(defmacro op-lex-weight (i)
  `(the fixnum (aref (the (array fixnum) $op-lex-weights) (the fixnum ,i))))
(defmacro op-slot-num (i)
  `(the fixnum (aref (the (array fixnum) $op-slot-nums) (the fixnum ,i))))
(defmacro op-mutations (i)
  `(aref (the (array t) $op-mutations) (the fixnum ,i)))

(defun get-op-id (name)
  ;; Fetch the integer ID of a function symbol, given its print-name
  (or 
      (sloop for i from *first-user-op*
	     below $num-ops
	     when (equal (aref (the (array t) $op-names) i) name)
	     return i)
      (sloop for i from *predef-ops*
	     below *max-ops*
	     when (equal (aref (the (array t) $op-names) i) name)
	     return i)
      ))

(proclaim '(function get-new-op-id (t) t))
(defun get-new-op-id (sym &aux id)
  ;; Fetch the integer ID of a function symbol, given its print-name
  (unless (setq id (get-op-id sym))
    (setf id $num-ops)
    (incf $num-ops)
    (push id $newops)
    (setf (aref $op-arities id) -1)
    (setf (aref $op-names id) sym))
  id)

(defun enter-op (sym arity &aux id)
  ;; Declare a new function symbol or check that the declared arity 
  ;; of a symbol matches the parsed arity.
  (if (setf id (get-op-id sym))
      (when (not (= (get-arity id) arity))
	(error "Symbol ~s already declared with arity ~s" sym (get-arity id)))
    (progn
      (setf id $num-ops) (incf $num-ops)
      (push id $newops)
      (setf (aref $op-names id) sym)
      (setf (aref $op-weights id) 1)
      (setf (aref $op-arities id) arity)))
  id)


(defmacro quantifierp (x) `(memq ,x *exist*all*))

(defmacro is-predefined-op (id) `(and (< ,id *max-ops*) (> ,id *predef-ops*)))
(defmacro is-bool-op (id) `(is-predefined-op ,id))

(defmacro enter-predefined-op (name arity pred preid)
  `(let ()
     (setf id $num-ops)
     (incf $num-ops)
     (setf (aref $op-names id) ,name)
     (setf (aref $op-weights id) 1)
     (setf (aref $op-arities id) ,arity)
     (if ,pred (setf (aref $op-pred id) 1))
     (unless (eq id ,preid) 
	     (error (uconcat "Id for *" ,name "* is incorrect.")))
     ))

(defun init-op-table (&aux id)
  ;; Predefined function symbols. These functions are assumed that
  ;; they will not appear in the left side of any rewrite rule.
  (setq $num-ops *predef-ops*)

  (enter-predefined-op "=" 2 t *=*)  ;; 0
  (enter-predefined-op "false" 0 t *false*) ;; 1
  (enter-predefined-op "true" 0 t *true*)  ;; 2
  (enter-predefined-op "and" 2 t *and*) ;; 3
  (enter-predefined-op "xor" 2 t *xor*) ;; 4
  (enter-predefined-op "or" 2 t *or*) ;; 5
  (enter-predefined-op "not" 1 t *not*) ;; 6
  (enter-predefined-op "=>" 2 t *->*) ;; 7
  (enter-predefined-op "exist" 2 t *exist*) ;; 8
  (enter-predefined-op "all" 2 t *all*) ;; 9
  (enter-predefined-op "equ" 2 t *equ*) ;; 10

#|
  (setq $type-rela '((bool)) 
	$constructors (list *true* *false*)
	$free-constructors $constructors
	$type-of-num       '(univ)  ; the type name for numbers.
	$type-constructors `((bool ,*true* ,*false*))) 
|#

  (setq $num-ops *first-user-op*)
  )

(proclaim '(function clear-ops () t))
(defun clear-ops ()
  ;; Initialize the symbol manager.
  (sloop for i from *first-user-op* below $num-ops
	 do (progn
	      (setf (aref $op-names i) nil)
	      (setf (aref $op-arities i) -1)
	      (setf (aref $op-arities2 i) nil)
	      (setf (aref $op-weights i) -1)
	      (setf (aref $op-pred i) 0)
	      ))
  (setf $num-ops *first-user-op*) ;; don't clear the predefined ops.
  )

(defun get-op-properties ()
  (sloop for i from *first-user-op* below $num-ops
	 collect
	 (list
	      (aref $op-names i)
	      (aref $op-arities i)
	      (aref $op-arities2 i)
	      (aref $op-weights i) 
	      (aref $op-pred i)
	      )))

(defun restore-properties (props)
  ; restore the properties of operators.
  (sloop for i from *first-user-op* below $num-ops
	 for prop in props do
	 (setf (aref $op-names i) (pop prop))
	 (setf (aref $op-arities i) (pop prop))
	 (setf (aref $op-arities2 i) (pop prop))
	 (setf (aref $op-weights i) (pop prop))
	 (setf (aref $op-pred i) (pop prop))
	 ))

;-------------------------------------
; Miscellanous functions on operators.
;-------------------------------------

(defun exist-op (op)
  (or (sloop for xa in $eqn-set thereis
	   (or (memq op (op-list (lhs xa))) 
	       (memq op (op-list (rhs xa)))))
      (sloop for xa in $post-set thereis
	   (or (memq op (op-list (lhs xa))) 
	       (memq op (op-list (rhs xa)))))
      (sloop for xa in $rule-set thereis
	     (and (not (is-deleted-rule xa))
		  (or (memq op (op-list (lhs xa))) 
		      (memq op (op-list (rhs xa))))))))
      
(defun same-arity (op1 op2)
  ; Return true iff there is an operator f1 equivalent to op1 and
  ; an operator f2 equivalent to op2 such that f1 and f2 have the same
  ; arity.
  (have-common (sloop for xa in (ops-equiv-to op1) collect (get-arity xa))
	       (sloop for xb in (ops-equiv-to op2) collect (get-arity xb))))
                 
(defun get-constants (ops)
  ; Returns all constant in OPS.
  (sloop for xa in ops if (equal (get-arity xa) 0) collect xa))

(defun non-constants (ops)
  ; Returns all non-constant operators in OPS
  (sloop for xa in ops if (neq (get-arity xa) 0) collect xa))

(defun get-free-constructors ()
  ; Returns all free constructors in $constructors.
  (sloop for op in $constructors 
	 if (not (commutativep op))
	 collect op))

(defun display-constructors (type-ops)
   (princ "The system has the following constructors:") (terpri)
   (if* (cddr type-ops) 
     then (sloop for xa in (cdr (reverse type-ops)) do
		 (princ "     Type '")
		 (princ (car xa)) 
		 (princ "': ")
		 (princ (display-ops (cdr xa)))
		 (terpri))
     else 
     (setq type-ops (car type-ops))
     (princ "     Type '")
     (princ (car type-ops))
     (princ "': ")
     (princ (display-ops (cdr type-ops)))
     (terpri)))

(defun clean-ops (ops &aux ops1 ops2)
    (sloop for xa in $rule-set 
	   if (not (is-deleted-rule xa)) do
	   (setq ops1 (op-list (lhs xa))
		 ops2 (op-list (rhs xa)))
	   (setq ops (sloop for op in ops 
			    if (not (or (memq op ops1) (memq op ops2)))
			    collect op))
	   (if (null ops) (return nil)))
    (sloop for xa in $eqn-set 
	  as ops1 = (op-list (lhs xa))
	  as ops2 = (op-list (rhs xa)) do
	(setq ops (sloop for op in ops 
			if (not (or (memq op ops1) (memq op ops2)))
			collect op))
	(if (null ops) (return nil)))

    (sloop for op in ops do 
	   (setf (aref $op-names op) 'DELETE)
	   (setq $constructors (deleten op $constructors 1))
	   (delete op (assoc (get-op-type op) $type-constructors))))

(defun get-max-arity ()
  (sloop with maxarity = 0
	 for op from *first-user-op* below $num-ops
	 if (> (get-arity op))
	 do (setq maxarity (get-arity op))
	 finally (return maxarity)))


; Abbreviation for a common getcharn idiom.  It means to get the
; ascii code of a character.
(defmacro code (char) `(getcharn ,char 1))

(defun get-new-operator (seed &aux op)
  (gensym $new-sym-num)
  (incf $new-sym-num)
  (while (get-op-id (setq op (princ-to-string (gensym seed)))) nil)
  op)

(defun create-new-operator (flag arity)
  ;; Return a new operator of arity "arity"
  (if flag
      (setq flag (enter-op (get-new-operator "f") arity))
    (setq flag (ask-for-operator arity)))
  (push flag $newops) ;; $newops is used in add-shorthand-ops.
  flag)

(defun ask-for-operator (arity)
  ; Asks user for a new operator and gives arity ARITY.
  ; Returns operator after adding it 
  (prog (ans)
    loop-op
    (if (io-eoln $in-port) (princ "Give me a new operator name: "))
    (setq ans (read-atom 'end))
    (terpri)
    (unless (stringp ans) 
      (princ "Sorry, not a valid operator.") (terpri)
      (go loop-op))
    (when (get-op-id ans) 
      (princ "A new name please!") (terpri)
      (go loop-op))

    (setq ans (enter-op ans arity))
    (return ans)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; Macros and Functions about VARIABLES.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A variable id is a negative number between -(*max-vars-all*) and -1.
(defmacro init-var-tab () `(setq $num-vars 1))

;; Sometimes it is useful to iterate vars from 1 to some limit, 
;; so we have to convert the index variable to a valid variable symbol ID.
(defmacro upto-var (int) `(the fixnum (- ,int))) ; from index to id.
(defmacro var-index (int) `(the fixnum (- ,int))) ; from id to index.

;; Retrieve the print name of a variable.
(defmacro var-name (i) `(aref (the (array t) $var-print-names) ,i))
(defmacro user-var-name (i) `(aref (the (array t) $var-bindings) ,i))
(defmacro write-variable (var port) `(princ (var-name (var-index ,var)) ,port))

(defmacro make-new-variable () 
  ;; return a new variable id.
  `(upto-var (- *max-vars-all* (1+ (mod (incf $new-variable) *max-vars-half*)))))

(defmacro is-valid-var (s)
  ; s is a string. Returns T iff CHAR is a valid variable; otherwise, NIL.
  ; A valid variable is a symbol with the first character being
  ; between 'u' and 'z'.
  `(memq (char ,s 0) *var-letters*))

(defmacro is-var-id (var) `(< ,var 0))

(proclaim '(function get-var-id (t) t))
(defun get-var-id (sym &aux id)
  ;; Fetch the integer ID of a variable name, given its print-name
  (unless 
   (setq id (sloop for i from 1
		   below $num-vars
		   declare (fixnum i)
		   when (equal (user-var-name i) sym)
		   return (upto-var i)))
   (setf id (upto-var $num-vars))
   (setf (user-var-name $num-vars) sym))
   (incf $num-vars)
  id)

(defun init-var-table ()
  (setf (aref $var-print-names 0) "w0")
  (setf (aref $var-print-names 1) "x")
  (setf (aref $var-print-names 2) "y")
  (setf (aref $var-print-names 3) "z")
  (setf (aref $var-print-names 4) "u")
  (setf (aref $var-print-names 5) "v")
  (setf (aref $var-print-names 6) "w")

  (init-var-table-aux 7 (1- *max-vars*) 2)
  (init-var-table-aux *max-vars* *max-vars-all* 1)
  )

(defun init-var-table-aux (i max-i j)
  (while (< i max-i)
    (setf (aref $var-print-names i) (format nil "x~S" j)) (incf i)
    (setf (aref $var-print-names i) (format nil "y~S" j)) (incf i)
    (setf (aref $var-print-names i) (format nil "z~S" j)) (incf i)
    (setf (aref $var-print-names i) (format nil "u~S" j)) (incf i)
    (setf (aref $var-print-names i) (format nil "v~S" j)) (incf i)
    (setf (aref $var-print-names i) (format nil "w~S" j)) (incf i)
    (incf j 2)
    ))

;; HERKY maintains two banks of variables, those with even-number subscripts 
;; (called x-variables) and those with odd-number subscripts (called x-variables).
;; They can be changed uniformly from each other by adding (or substracting)
;; the value *max-vars*.
(defmacro rename-var-x-to-y (var) `(+ ,var 1 (- *max-vars*)))

