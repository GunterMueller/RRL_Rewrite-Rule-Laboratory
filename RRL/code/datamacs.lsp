;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-
;;;> ** (c) Copyright 1989 Deepak Kapur.  All rights reserved.
;;;> ** (c) Copyright 1989 Hantao Zhang.  All rights reserved.

#-franz (in-package "USER")

;;
;; contains macros for use in RRL's code.
;; except for a few, most are common to Franz and Common versions.
;; 
;; 

;; add-time implemented differently for franz & common -- siva.
;;

#+franz (eval-when (compile) (load 'loop))
#+franz (include "frz-spl.l")  ;; all the special variables.
                               ;; and the array functions for franz

;      This file is a gathering of data abstractions manipulation functions
; in macro format. It allows the use of access functions to data while not
; losing on run time efficiency.

;
;      The first set of macros are those for terms. They are the macro
; form for those functions originally in terms.l
;
; A non variable term is represented as (OP . (ARGS)).
;
;       operator:       operator of non-variable terms.
;       arguments:      arguments of terms.
;       variablep:      t if a variable term, otherwise nil.
;       nthsubt:        nth subterm of a non-variable term.
;       make-term:      make a term when given operator and arguments.
;       make-terms:     a list of terms made of given operator and given 
;                       arguments list.
;       nargs:          arity of root operator of a term.
;       applysubst:     substitute variables in a term.

(defmacro make-term (op args) `(cons ,op ,args))
(defmacro make-term-1arg (op arg) `(list ,op ,arg))
(defmacro op-of (term) `(car ,term))
(defmacro args-of (term) `(cdr ,term))
(defmacro args (s) `(cdr ,s))
(defmacro variablep (term) `(symbolp ,term))
(defmacro var?(x) `(symbolp ,x))
(defmacro arguments(t1) `(cdr ,t1))
(defmacro constant? (term) `(null (cdr ,term)))

(defmacro nonvarp (term) `(consp ,term))
(defmacro nargs (term) `(length (cdr ,term)))
(defmacro first-arg (term) `(cadr ,term))
(defmacro second-arg (term) `(caddr ,term))
(defmacro same-op (t1 t2) `(eq (op-of ,t1) (op-of ,t2)))
(defmacro same-op? (s t1) `(eq (op-of ,s) (op-of ,t1)))
(defmacro same-root (t1 t2) `(eq (op-of ,t1) (op-of ,t2)))
(defmacro nthsubt (n term) `(nthelem (1+ ,n) ,term))



(defmacro make-terms (op args-list)
  `(sloop for args in ,args-list collect (cons ,op args)))
(defmacro is-bool-root (term)
  `(and (nonvarp ,term) (memq (op-of ,term) `(xor or and & not -> equ))))
(defmacro is-rooted-+ (term) `(and (nonvarp ,term) (eq (op-of ,term) '+)))
(defmacro same-pname (x1 x2) 
   `(or (eq ,x1 ,x2) (not (or (alphalessp ,x1 ,x2) (alphalessp ,x2 ,x1)))))

(defmacro unitp (rule)
   `(if* $in-fopc then
	(if* $induc then (not (ctx ,rule))
	    elseif (predicatep (op-of (lhs ,rule)))
	    then (not (memq (op-of (lhs ,rule)) '(xor and)))
	    else t)
	else t))

(defmacro applysubst (alist term)
  ; Returns a new term with ALIST used as the substitution alist
  ; that is applied to TERM.
  `(if* (eq ,alist *empty-sub*) ,term (sublis ,alist ,term)))

(defmacro falsep (ctx) `(and (not (symbolp ,ctx)) (eq (op-of ,ctx) 'false)))
(defmacro not-falsep (ctx) `(not (falsep ,ctx)))
(defmacro truep (ctx) `(or (equal ,ctx '(true)) (null ,ctx)))
(defmacro null-ctx (ctx) `(null ,ctx))
(defmacro is-bool-op (op) `(memq ,op $bool-ops))

;
;      The third set of macros are those for equations.
;
; An equation is represented as (LHS RHS CTX mark source)
;
;	make-eqn: makes an equation given two terms and a context.
;	eqn-ctx:  context of given equation.
;	is-condi-eqn: Returns T if given equation is conditional.

(defmacro make-eqn (t1 t2 ct source &optional mark)
  `(list ,t1 ,t2 ,ct ,mark ,source))
(defmacro eqn-ctx (eqn) `(if* (equal (caddr ,eqn) '(true)) 
	then (rplaca (cddr ,eqn) nil) nil else (caddr ,eqn)))
(defmacro is-condi-eqn (eqn) `(eqn-ctx ,eqn))
(defmacro eqn-source (eqn) `(nth 4 ,eqn))
;;; >>>>> 1/18/89
(defmacro eqn-source-type (eqn) `(car (nth 4 ,eqn)))
(defmacro is-source-type (eqn type) `(eq ,type (eqn-source-type ,eqn)))
(defmacro change-lhs (eqn lhs) `(cons ,lhs (cdr ,eqn)))
(defmacro change-rhs (eqn rhs) `(list* (lhs ,eqn) ,rhs (cddr ,eqn)))
(defmacro change-lhs-rhs (eqn lhs rhs) `(list* ,lhs ,rhs (cddr ,eqn)))
(defmacro change-lhs-rhs-ctx (eqn lhs rhs ctx) `(list* ,lhs ,rhs ,ctx (cdddr ,eqn)))
(defmacro change-ctx (eqn ctx) `(list* (lhs ,eqn) (rhs ,eqn) ,ctx (cdddr ,eqn)))
(defmacro exchange-lr (eqn) `(list* (rhs ,eqn) (lhs ,eqn) (cddr ,eqn)))
(defmacro change-source (so eqn) `(append1 (butlast ,eqn) ,so))

(defmacro is-prop-eqn (eqn)
  `(and (nonvarp (lhs ,eqn)) (nonvarp (cadr ,eqn))
	(neq (caar ,eqn) '=) (predicatep (caar ,eqn))
	(neq (caadr ,eqn) '=) (predicatep (caadr ,eqn))))

(defmacro ass2eqn (ass source &optional first) 
   `(make-eqn ,ass nil nil ,source ,first))
(defmacro eqn2ass (eqn) `(list 'eq (lhs ,eqn) (rhs ,eqn)))
(defmacro is-assertion (eqn) `(truep (cadr ,eqn)))
(defmacro assertionp (eqn) `(or (is-assertion ,eqn) (is-prop-eqn ,eqn)))
(defmacro set-eqn-mark (eqn mark) (let ((v1 (gensym)))
    `(let ((,v1 (copylist ,eqn))) (setf (cadddr ,v1) ,mark) ,v1)))
(defmacro is-oneway (eqn) `(or (cadddr ,eqn) (eq 'def (car (eqn-source ,eqn)))))
(defmacro is-input-ass (eqn) `(cadddr ,eqn))

;
;      The fourth set of macros are those for rules. They are the macro
; form for those functions originally in rules.l
;
; A rule is represented as (lhs rhs context mark ruleno lhsize)
;
;	make-rule:  makes a rule given two terms, a context and a number.
;	lhs:        the left-hand-side of given rule.
;	rhs:        the right-hand-side of given rule.
;	ctx:   the context of given rule.
;	ruleno:	    the number of given rule.
;	set-crit-mark:    set mark to the given rule.
;	set-extend-mark:  T if the rule is marked.
;	extensible:
;	crit-marked:
;	rukesize:   the size of the left-hand-side of tgiven rule.
;	lhsize:     the size of the left-hand-side of tgiven rule.
;       rules-with-op: list of rules with given left-hand-side 
;                                  toplevel operator.
; for ac -- mark is nil if not extensible t if extensible

(defmacro make-rule (lhs rhs ctx number source size reduction nonground)
  ; Returns a rule made from terms T1 and T2, and context C.
  `(list ,lhs ,rhs ,ctx nil ,source ,size nil ,number nil ,reduction ,nonground))
(defmacro lhs (rule) `(car ,rule))
(defmacro rhs (rule) `(cadr ,rule))
(defmacro ctx (rule) `(eqn-ctx ,rule))
(defmacro is-condi-rule (rule) `(eqn-ctx ,rule))
;(defmacro set-mark (rule m)  `(progn (rplaca (cdddr ,rule) ,m) ,rule))
(defmacro set-crit-mark (rule) `(progn (rplaca (cdddr ,rule) t) ,rule))
;(defmacro set-extend-mark (rule) `(progn (setf (nth 8 ,rule) t) ,rule))
(defmacro set-symmetry-mark (rule terms) `(setf (nth 8 ,rule) ,terms))
(defmacro crit-marked (rule) `(cadddr ,rule))
(defmacro ref-symmetry-terms (rule)  `(cdr (nth 8 ,rule)))
(defmacro ref-symmetry-vars (rule)  `(if* (nth 8 ,rule) (car (nth 8 ,rule))))
(defmacro set-no-reduction-mark (rule) `(setf (nth 9 ,rule) t))
(defmacro set-extra-pre-variables (vars rule) `(setf (nth 9 ,rule) ,vars))
(defmacro ref-extra-pre-variables (rule) `(cdr (nth 9 ,rule)))

(defmacro pred-rulep (rule) `(get (caar ,rule) 'predicate))
(defmacro ruleno (rule)  `(nth 7 ,rule))
(defmacro change-ruleno (rule num) `(rplaca (cdddr ,rule) ,num))
(defmacro lhsize (rule)  `(nth 5 ,rule))
(defmacro pairswith (rule)  `(nth 6 ,rule))
(defmacro rule-source (rule)  `(nth 4 ,rule))
; >>>>>>>> 1/18/89
(defmacro rule-source-type (rule)  `(car (nth 4 ,rule)))
(defmacro is-reduction (rule) `(null (nth 9 ,rule)))
(defmacro is-general-rule (rule) `(nth 10 ,rule))
(defmacro lhs-vars (rule) `(nth 10 ,rule))
(defmacro ref-pres-vars (rule) `(nth 10 ,rule))
(defmacro rules-with-op (op op-list) `(cdr (assq ,op ,op-list)))
(defmacro get-rules-with-op (op op-rules)
  `(cdr (assq ,op
	      (if* ,op-rules
		  then ,op-rules
		  elseif (and $narrow $goal-reduce)
		  then (append $op_rules $op_goal_rules)
		  else $op_rules))))

;      The fifth set of macros are those for io functions. They are the macro
; form for those functions originally in io.l
;
;       set-arity:     set arity of operator.
;	set-status:    gives status to operator.
;	get-status:    get the status of operator.
;	get-noncons:   all non-constructor operators.
;	set-infix:     set operator to infix.
;	infixp:        tell operator is infix.
;	set-predicate: declares an operator as predicate.
;	predicatep:    return true iff an operator is predicate.
;	set-commutative: declares an operator as commutative.
;	commutativep:  return true iff an operator is commutative.
;	set-constructor: declares an operator as constructor.
;	constructorp:  return true iff an operator is constructor.

(defmacro set-infix (op) 
   `(cond ((numberp ,op) nil) (t (putprop ,op t 'infix))))
(defmacro rem-infix (op) 
   `(cond ((numberp ,op) nil) (t (remprop ,op 'infix))))
(defmacro infixp (op) `(cond ((numberp ,op) nil) (t (get ,op 'infix))))

(defmacro change-rule-source-type (rule type) 
   `(rplaca (rule-source ,rule) ,type))
(defmacro is-rule-source-type (rule type)
   `(eq ,type (car (rule-source ,rule))))
(defmacro set-arity (op arity)
   `(cond ((numberp ,op) nil) (t (putprop ,op ,arity 'arity))))
;(defmacro get-arity (op) 
;  `(cond ((numberp ,op) 0) (t (get ,op 'arity))))
(defmacro is-constant (op) 
  `(or (numberp ,op) (equal (get ,op 'arity) 0)))
(defmacro rem-arity (op) 
  `(cond ((numberp ,op) nil) (t (remprop ,op 'arity))))
(defmacro set-arity2 (op arity)
  `(cond ((numberp ,op) (setq $num-type ,arity)) (t (putprop ,op ,arity 'arity2))))
(defmacro get-arity2 (op) 
  `(cond ((numberp ,op) $num-type) (t (get ,op 'arity2))))
(defmacro rem-arity2 (op)
  `(cond ((numberp ,op) nil) (t (remprop ,op 'arity2))))

(defmacro set-status (op status) 
  `(if* (numberp ,op) then nil else (putprop ,op ,status 'status)))

(defmacro get-status (op) 
  `(if* (numberp ,op) nil (get ,op 'status)))

(defmacro rem-status (op)
  `(if* (not (numberp ,op)) then (remprop ,op 'status) 
				(setq $st_list (delete ,op $st_list))))

(defmacro ac-op-p (op) `(memq ,op $ac))
(defmacro ac-root (term) `(ac-op-p (car ,term)))
(defmacro comm-op-p (op) `(memq ,op $commutative))
(defmacro comm-root (term) `(comm-op-p (car ,term)))

(defmacro set-predicate (op) 
  `(cond ((numberp ,op) nil) (t (putprop ,op t 'predicate))))
(defmacro rem-predicate (op) 
  `(cond ((numberp ,op) nil) (t (remprop ,op 'predicate))))
(defmacro predicatep (op)
  `(cond ((numberp ,op) nil) (t (get ,op 'predicate))))

(defmacro set-skolem (op) 
  `(cond ((numberp ,op) nil) (t (putprop ,op t 'skolem))))
(defmacro rem-skolem (op) 
  `(cond ((numberp ,op) nil) (t (remprop ,op 'skolem))))
(defmacro skolemp (op)
  `(cond ((numberp ,op) nil) (t (get ,op 'skolem))))

(defmacro set-commutative (op) `(push ,op $commutative))
(defmacro commutativep (operator) `(memq ,operator $commutative))

(defmacro set-constructor (op) `(push ,op $constructors))
(defmacro constructorp (op) `(memq ,op $constructors))
(defmacro is-free-constructor (op) `(memq ,op $free-constructors))

(defmacro get-noncons ()
  ; Returns all the non-constructor in $operlist.
  `(do ((op $operlist (cdr op))
	(res nil (if* (not (memq (car op) $constructors)) 
		     (cons (car op) res)
		     res)))
       ((null op) (nreverse res))))

;; I/O macros

(defmacro my-probef(file)
  #+franz `(probef ,file)
  #-franz `(probe-file (string ,file)))

(defmacro my-tyipeek(port)
  #+franz `(lowcase (tyipeek ,port))
  ;; #-franz `(capitalize (tyipeek nil ,port -1))
  #-franz `(let ((char (peek-char nil ,port nil -1)))
	     (if* (eql char -1) -1 (char-code char)))
)

(defmacro my-tyi(port)
  #+franz `(lowcase (tyi ,port))
  ;#+franz `(tyi ,port)  ; --------- we want UPCASE letters. HZ 12/88.
  ;; #-franz `(capitalize (tyi ,port nil))
  #-franz `(char-code (read-char ,port nil))
)

(defmacro my-tyo (ch port)
  #+franz `(tyo ,ch ,port)
  #-franz `(princ (code-char ,ch) ,port)
)

(defmacro my-untyi(fixnum port)
  #+franz `(untyi ,fixnum ,port)
  ;;#-franz `(untyi ,fixnum ,port nil)
  #-franz `(unread-char (code-char ,fixnum) ,port)
)

(defmacro drain-it(port)
  #+franz `(zapline)
  ;; #-franz `(drain ,port)
  #-franz `(read-line ,port)		; Maybe (read-line ,port nil -1) ?
)

; Abbreviation for a common getcharn idiom.  It means to get the
; ascii code of a character.
(defmacro code (char)
  #+franz `(getcharn ,char 1)
  #-franz `(char-code (string ,char) 0)
)

;;;; Copy the top level elements of list.  This is already defined 
;;;; for the lisp machine.
#+franz (defmacro copylist (list) `(append ,list nil))

; user-selectq is a very useful macro used often in kb-option etc.
;
; explained by example --
;    (user-selectq
;       (cat  " help about cat "  (setq ans cat))
;       (dog  " some message about dog " (setq ans dog) (do something else))
;       (crow " dbfjdf dsah kjf fjda fj" body to be executed)
;       (dummy " will do something and stay in this function"
;                     (body) (setq failed t)))
; will prompt the user to type some subsequence of cat , dog ,crow or dummy
; and execute the body and return value of last form evaluated.
; If the last form is (setq failed t) then it doesn't exit the prompt
; loop but asks for another choice. 
;   This is useful if the user wants to display rules -eqns 
; before making a choice.
; See functions in kb-option to get a better idea of how this works.
(defmacro user-selectq (&rest options)
  (let ((option-list (list* 'quit 'help (mapcar 'car options)))
        (choice (gensym)))
    `(let ((,choice nil))
       #-franz (terpri)
       (do ((failed nil nil)
	    (ans nil))
	   (nil)
	 (setq ,choice (progn () (print-head ',option-list)
			      (choose-str (read-atom 'none) ',option-list)))
	 (if* (numberp ,choice) 
	   then (setq ans ,choice) 
	   else (setq ans (caseq ,choice
				 ,@(sloop for xa in options 
					 collect `(,(car xa) . ,(cddr xa)))
			    (t (setq failed t)
			       (if* (eq ,choice 'help) 
				   then 
				   #-franz (terpri) (terpri)
				   (princ "HELP:      Print this message.") (terpri)
				   ,@(sloop for xa in options
					   collect `(princ ',(car xa))
					   collect '(princ ":  ")
					   collect `(princ ',(cadr xa)) 
					   collect '(terpri))
				   (princ "QUIT:      Quit this menu.") (terpri)
				   (terpri)
				   elseif (eq ,choice 'quit)
				   then (setq failed nil)
				   else 
				   (princ "Please select an option from the list.")
				   (princ "  Try again.") (terpri))))))
	 (if (not failed) (return ans)) ))))

#+franz
(defmacro add-time (variable &rest body)
  ; instead of having to use get-time and set-timer in the code
  ; this macro adds to variable the time required to execute body
  (let ((v1 (gensym)) (v2 (gensym)))
    `(let ((,v1 (set-timer)) ,v2)
       (setq ,v2 ,@body
	     ,variable (add ,variable (get-time ,v1))) ,v2)))

#-franz
(defmacro add-time (var &rest body)
  (let ((v1 (gensym)))
    `(let ((,v1 (get-internal-run-time) ))
       (prog1
        (let () ,@body)
	(setq ,var (+ ,var (- (get-internal-run-time) ,v1)))))))

(defmacro add-associate-list (head elem lists)
  (let ((v1 (gensym)))
    `(let ((,v1 (assq ,head ,lists)))
        (if* ,v1 then (nconc ,v1 (ncons ,elem))
	        else (push (list ,head ,elem) ,lists))
	,lists)))

(defmacro query-insert (elem list)
   `(if* (member0 ,elem ,list) then t else (push ,elem ,list) nil))

(defmacro remonce (element list) `(remove0 ,element ,list 1))

(defmacro ac-equal (t1 t2) `(equal ,t1 ,t2))
(defmacro c-permu (term)
   `(if* $commutative then (c-permutation ,term) else ,term))

(defmacro reducible-time (t1) 
  `(add-time $reduce_time (reducible ,t1)))

(defmacro guide-reducible-time (t1 t2) 
  `(add-time $reduce_time (guide-reducible ,t1 ,t2)))

;  Returns the correponding defining domain of OP.
(defmacro get-def-domain (op) `(cdr (assq ,op $def-domains)))

; From unify
(defmacro cur-val (var a-list) `(or (cdr (assq ,var ,a-list)) ,var))

; Macros to access the fields of a token-buffer.
(defmacro token-port (buffer) `(car ,buffer))
(defmacro token-text (buffer) `(cadr ,buffer))
(defmacro token-type (buffer) `(caddr ,buffer))
; Use throw to signal a syntax error.
(defmacro synerr () `(*throw 'error 'error))

; From match
(defmacro one-arg(term) `(null (cddr ,term)))
(defmacro single(list) `(null (cdr ,list)))


(defmacro print-name (op) `(caseq ,op (xor '+) (t ,op)))


(defmacro process-assertion (eqn)
  `(if* (is-input-ass ,eqn) then
       (complete-well-typed (lhs ,eqn))
       (process-ass (lhs ,eqn) (eqn-source ,eqn))
       else 
       (process-ass-simple (lhs ,eqn) (eqn-source ,eqn))))

;; from assertion.l

(defmacro domain-rulep (rule) `(not (predicatep (op-of (lhs ,rule)))))

(defmacro boolean-opp (x) `(memq ,x '(or & equ -> xor and)))

(defmacro quantifierp (x) `(memq ,x '(all exist)))

;; from match.l

(defmacro c-match (t1 t2) `(c-match1 (ncons ,t1) (ncons ,t2)))

;; from orderpc.l

(defmacro half-canonicalize (term)
   `(if* (eq (op-of ,term) 'and) then (args-of ,term) else (ncons ,term)))

(defmacro inc (num) `(setq ,num (1+ ,num)))
(defmacro insert1 (one lis) `(if* (memq ,one ,lis) then ,lis else (push ,one ,lis)))
(defmacro push-end (one many) `(setq ,many (nconc ,many (ncons ,one))))
(defmacro add-end (one many) `(setq ,many (append1 ,many ,one)))

;; new macro for typing:
(defmacro letterp (p)
  ;;; #+franz `(or (and (>= ,p #/a) (<= ,p #/z)) (eq #/_ ,p) (eq #/. ,p))
  #+franz `(or (and (>= ,p 97) (<= ,p 122)) (eq 95 ,p) (eq 46 ,p))
  ;;; ---------- add "." in a symbol. HZ 12/88 
  ;;; #-franz `(or (and (>= ,p #/A) (<= ,p #/Z)) (eq #/_ ,p))
  #-franz `(or (and (>= ,p 65) (<= ,p 90)) (eq ,p 95)))

(defmacro last-letter (p)
  #+franz `(car (last (explodec ,p)))
  #-franz `(let ((s (string ,p)))
	     (char s (1- (length s))))
)

(defmacro sort-of (term) `(get-domain-type (op-of ,term)))

;    is-premise-set: return t if (eq (car (ctx eqn)) '*&*).
(defmacro is-premise-set (ctx) `(and ,ctx (eq (car ,ctx) '*&*)))
;    get-premises: return a list of premises without the mark.
(defmacro get-premises (pres) `(cdr ,pres))
;    get-pre-lhs: return the left-hand side when a premise is viewed as a rule.
(defmacro get-pre-lhs (pre) 
   `(if* (variablep (car ,pre)) then (cadr ,pre)
	elseif (cadr ,pre) then (car ,pre) 
	elseif (eq (caar ,pre) '=) then (cadar ,pre)
	else (car ,pre)))
;    get-pre-rhs: return the right-hand side when a premise is viewed as a rule.
(defmacro get-pre-rhs (pre) 
   `(if* (variablep (car ,pre)) then (car ,pre)
	elseif (cadr ,pre) then (cadr ,pre) 
	elseif (eq (caar ,pre) '=) then (caddar ,pre)
	else '(true)))
(defmacro make-pre (lhs rhs &optional info) `(attach ,lhs (cons ,rhs ,info)))
(defmacro is-hypo-pre (pre) `(memq 'hypo (cddr ,pre)))
(defmacro is-used-pre (pre) `(memq 'used (cddr ,pre)))

(defmacro flat-term (term2) 
  ; Make sure every term in the system is flattend and brted.
  (let ((term (gensym)))
    `(let ((,term ,term2))
       (if* (variablep ,term) then ,term else
	   (setq ,term (if* $polynomial 
			   then (add-time $brt_time (poly-simplify ,term))
			   elseif $ac then (make-flat ,term)
			   elseif $commutative then (c-permutation ,term)
			   else ,term))
	   (if $induc
	       (ba-simplify ,term)
	     (if $in-fopc (brt ,term) 
	       ,term))))))

(defmacro is-type-predicate (op)
  `(and	(predicatep ,op)
	(equal (get-arity ,op) 1)
#+franz	(memq (getcharn ,op 1) '(73 105)) ; #\I = 73, #\i = 105
#+franz	(memq (getcharn ,op 2) '(83 115)) ; #\S = 83, #\s = 115
#-franz (and (> (length (symbol-name ,op)) 2)
	     (string-equal "is" (symbol-name ,op) :start2 0 :end2 2))
    ))

(defmacro is-poly (term)
  `(and $polynomial (nonvarp ,term) (eq (car ,term) '+)))

(defmacro thereis (list pred)
  `(sloop for xa in ,list thereis (funcall ,pred xa)))

(defmacro always (list pred)
  `(sloop for xa in ,list always (funcall ,pred xa)))

(defmacro collect-if (list pred result)
  `(sloop for xa in ,list if (funcall ,pred xa) collect (funcall ,result xa)))

(defmacro equal-term (t1 t2) `(or (equal ,t1 ,t2) (and (null ,t2) (truep ,t1))))

(defmacro cover-of (op)
  `(or (assoc ,op $non-comm-cover-sets) (assoc ,op $cover-sets)))

(defmacro cross-product (l1 l2) `(product-lists (list ,l1 ,l2)))

(defmacro ask-number (current &rest messages)
  ; ask the user to give a natural number. 
  `(let ()
     (print-choice-message ,@messages)
     (if* (and (is-empty-line $in-port) ,current) 
	 then (terpri) (princ (uconcat "(current value: " ,current ") "))
	 else (setq ,current 0))
     (setq ,current (ask-a-number ,current))))

(defmacro ask-choice (current choices &rest messages)
  ; >>>>>>> 1/16/89
  ; Ask the user to choose one from "choices". The current value is displayed.
  `(let ()
     (print-choice-message ,@messages)
     (if* (and ,current (is-empty-line $in-port)) then
       (terpri) (princ (uconcat "(current value: " ,current ") ")))
     (setq ,current (ask-a-choice ,choices (print-atoms ,choices ",")))))

(defmacro process-del-rule (l2 xa)
  ; >>>>>> 5/5/89 hzhang.
  `(caseq $del_rule_str
	 (1 (process-equation ,l2 t))
	 (2 (push ,l2 $eqn-set))
	 (3 (setq $del-eqns (insert (list (lhsize ,xa) ,l2)
				    $del-eqns 'car-lessp t)))
	 (t (break "Invalid $del_rule_str")))       )

(defmacro arrange-eq-args (t1 t2)
  `(if* (pseudo-term-ordering ,t1 ,t2) (psetf ,t1 ,t2 ,t2 ,t1)))

(defmacro all-pre-vars (pres)
  `(rem-dups (sloop for pre in ,pres nconc (pre-vars pre))))

