(in-package 'user)

(defvar $debug nil)
(defvar $x_choose_term nil)  ; flag for user to choose induction term
(defvar $strong-induc nil)       ; flag for using new induction method
(defvar $x_indhyps nil)       ; list of induction hypothesis
(defvar $x_indeqn nil)       ; the eqn to do induction on

#|
===============================================================================
  File: x_rrl.lsp

This file contains the following functions which are taken from 
the original rrl files.

  Index:
    0. induc-subgoal-proofs (scheme eqn num step)
    1. abstract-proof (eqn num step &aux neweqns l2)
    2. cover-induc-on (eqn num &aux vars p-term conjs hypo)
       renamed to cover-set-scheme (eqn num &aux vars p-term conjs hypo)
    3. cover-induc-prove (eqn)
    4. structure-induc-on (eqn num &aux vars p-term conjs hypo)
    5. proof-under-new-premises (term oldeqn num step )
    6. cover-proof-process2 (eqn num step &aux l2)
    7. trace-generated-result (done num2 new num eqn)
    8. split-premises (new pres vars tuples eqn num &aux junk)
    9. form-subgoals-from-patterns (conj vars eqn num &aux pres neweqn)
   10. reduction-proof (eqn num &aux new)
   11. cover-proof-process (eqn step &optional num norm)
   12. succ-end-induc ()

===============================================================================
|#

(defmacro eqn-as-rule-info () 
  `(if (is-subset (all-pre-vars (cdr (ctx eqn))) (var-list (lhs eqn))) t nil))

(defun induc-subgoal-proofs (scheme eqn num step)
  (push (cons (cons (eqn-as-rule-info) $induc-vars) eqn) $induc-eqns)
  (if* (sloop for n from 1 for e1 in (cdr scheme) 
	      always (prove-all-eqns 
		      (form-subgoals-from-patterns e1 (car scheme) eqn (append1 num n))
		      (append1 num n) (sub1 step)))
	then
	(if* (> $trace_flag 1) then (trace-succ-prove eqn num))
	(push eqn $succ-eqns)
	(when (and num (null $x_indhyps))
	      (push eqn $eqn-set)
	      (order-eqns))
	(pop $induc-eqns)
	else
	(pop $induc-eqns)
	(push eqn $failed-eqns)
	nil))

(defun abstract-proof (eqn num step &aux neweqns l2)
  (if* (and
	    num ;; don't generalize the user's equation.
	   (neq (car (eqn-source eqn)) 'gene)
	   (setq neweqns (abstraction eqn))) then
      (sloop for n from 1 
	    for new in neweqns do
        (if* (and $x_hint (< 1 $cover-auto-level))
                                       then (return nil))  ; added by XH
	(if* (> $trace_flag 1) then
	    (terpri) 
	    (princ "Generalize") (write-seq-eqn num eqn) 
	    (princ "    to") (write-seq-eqn (append1 num n) new))

        (setf $x_state 'gen)  ; added by XH

        (setq l2 (cover-proof-process new step (append1 num n) t))
	(if* (> $trace_flag 1) then
		(trace-generated-result l2 (append1 num n) new num eqn))
	(if* (and (null l2) (null $x_hint)) (setf $x_fail 'gen-lemma)
                                               nil )
	(if* l2 then (return t))

	finally (return nil))))


(defun cover-set-scheme (eqn num &optional conjs &aux vars p-term hypo)
  ; eqn is the equation to be proven.
  ; return (vars . list_of_patterns). 
  ; then "form-subgoals-from-pattern" generates subgoals

  (setq conjs (if conjs 
		  (make-one-scheme (list conjs))
		(if $x_choose_term 
		    (make-one-scheme (list (x_get_induc_term eqn)))
		  (choose-best-schemes eqn (if* (null num) $first-induc-op)))))
  (if* conjs
       then
;--- if strong induction is used, remove ind hyp from conjectures ------------
      (if $strong-induc (setf conjs (x_remove_hyp conjs))) ;; added 8/13/91 by XH
;-----------------------------------------------------------------------------
      (setq vars (car conjs)
	    p-term (make-term 'P vars))
      (terpri) (princ "Let ") (write-term p-term)
      (princ " be") (write-seq-num num) (write-f-eqn eqn nil t) (terpri)
      (princ "The induction will be done on ")
      (write-variable (car vars) nil)
      (sloop for xa in (cdr vars) do (princ ", ") (write-variable xa nil))
      (princ " in ")
      (sloop for xa in $induc-terms do (write-term-simple xa) (princ ", "))
      (if (null num)
	   (setq $first-induc-op (append $induc-terms $first-induc-op)))
      (princ "and will follow the scheme: ") (terpri)
      (sloop for n from 1 for sch in (cdr conjs) do
	(princ "   ") 
	(write-seq-num (append1 num n))
	(setq hypo (car sch))
	(write-term-simple (make-term 'P (cadr sch)))
	(if* (cddr sch) then 
	    (setq p-term (make-term '*&* (sloop for xa in (cddr sch)
					      collect (make-pre (make-term 'P xa) nil)))
		  hypo (merge-premises hypo p-term)))
	(if* hypo then (princ " if ") (write-premises (cdr hypo)))
	(terpri))

      conjs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; replace prove() by the following:
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun cover-induc-prove (eqn)

; ---- XH begin
             ; -- initialization
             (x_initial eqn)
             (setf $x_lemmas nil)
	     (setq $x_indhyps nil)
	     ;; add $induc into the proof tree
             (if* (not (equal eqn $induc)) then
	       (add_child $root nil nil $seq-no 'new nil $induc)
	       (setf $seq-no (+ 1 $seq-no))
	       (setf $leaf   (first (node-chdlst $root)))
               (setf (node-status $root) 'virtual)
	       (setf $peek   $leaf))
	     (setf $x_state 'non)
; ---- XH end

  (get-cover-sets)
  (setq $failed-eqns nil
	$succ-eqns nil
	$case-split-terms nil
	$induc-eqns nil
	$first-induc-op nil)
  (if* (*catch 'prove 
	(progn
	  (if* (cover-proof-process eqn $step-deep nil t)
	      then (succ-end-induc) 
	      else
	      (terpri)
	      (sloop while (and $first-induc-op
			       (ok-to-continue 
				(uconcat "Do you want to try more inductions on other terms ?")))
		    do
		(setq $failed-eqns nil
		      $induc-eqns nil)
		(when (cover-proof-process eqn $step-deep)
		      (succ-end-induc)
		      (return-from cover-induc-prove nil))
		)
	      (fail-end-induc $failed-eqns))
	  nil))
      then (fail-end-induc $failed-eqns)))

(defun structure-induc-on (eqn num &aux vars p-term conjs hypo)
  ; eqn is the equation to be proven.
  ; return a list of conjectures.
  (if* (setq conjs (str-choose-one-scheme eqn)) then
      (setq vars (car conjs)
	    p-term (make-term 'P vars))
      (terpri) (princ "Let ") (write-term p-term)
      (princ " be") (write-seq-num num) (write-f-eqn eqn nil t) (terpri)
      (princ "The induction will be done on ")
      (write-variable (car vars) nil)
      (princ " and will follow the scheme: ") (terpri)
      (sloop for n from 1 for sch in (cdr conjs) do
	(princ "   ") 
	(write-seq-num (append1 num n))
	(setq hypo nil)
	(write-term-simple (make-term 'P (cadr sch)))
	(if* (cddr sch) then 
	    (setq hypo (list '*&* (make-pre (make-term 'P (caddr sch)) nil)))
	    (princ " if ") (write-premises (cdr hypo)))
	(terpri))

      conjs))

; -- 2/1/92 --
(defun proof-by-hint-term (hint oldeqn num step &aux l2 eqn)
  (when (> $trace_flag 1)
	(terpri) (princ "Proving") (write-seq-eqn num oldeqn)
	(princ "    by ") 
	(write-one-pre hint nil) (terpri))

  ;; l2 is the new premises
  (setq l2 (delete hint (ctx oldeqn)))
  (if (null (cdr l2)) (setq l2 nil))
  ;; eqn is the new eqn.
  (setq eqn (copylist oldeqn))
  (setq eqn (change-ctx eqn l2))

  (setq hint (first-arg (car hint)))
  
  (case (op-of hint)
	(case (proof-under-new-premises
		 (list 'cond (first-arg hint) $true-term $false-term)
		 eqn num step))
	(induc (if (and (sloop for var in (var-list (first-arg hint))
			       always (occurs-in-rule var eqn))
			(setq l2 (cover-set-scheme eqn num (first-arg hint))))
		   (induc-subgoal-proofs l2 eqn num step)
		 (let () 
		   (terpri) (princ "Bad induction term: ")
		   (write-term (first-arg hint))
		   (terpri))))
	(t (terpri) (princ "Undefined hint term: ") (write-term hint) (terpri)
	   nil)))		     

; -- 10/01/90 --

(defun proof-under-new-premises (term oldeqn num step &optional bool
				 &aux l2 eqn premises t4 t9)
  (push (first-arg term) $case-split-terms)

  (setq premises (make-pre-ass (first-arg term) nil))
  (setq premises (if (eq (car premises) '*&*) (cdr premises) (ncons premises)))

  ;;(if* $try then (terpri) (princ "NEW CONDI TERM: ") (princ term) (terpri))
  (when (> $trace_flag 1)
	(terpri) (princ "Proving") (write-seq-eqn num oldeqn)
	(princ "          under the condition ") 
	(write-term-simple (first-arg  term)) (terpri)
	(princ "          and its negation.") (terpri))

  (setq eqn (if bool (copy oldeqn) (subst0 (second-arg term) term oldeqn)))
  (setq eqn (subst0 $true-term (first-arg term) eqn))
  (setq l2 (if (ctx eqn)
	       (append (ctx eqn) premises) 
	     (cons '*&* premises)))
  (setq l2 (flatten-eqn (change-ctx eqn l2)))

; ---- XH begin
  (setf $x_state 'pre)
; ---- XH end

  (setf t4 (cover-proof-process l2 step (append1 num 1) t))

  (when t4
  (setq eqn (if bool
		oldeqn
	      (subst0 (nth 3 term) term oldeqn)))
  (setq premises (mapcar #'negate-one-pre premises))
  (setq eqn (subst0 $false-term (first-arg term) eqn))
  (setq l2 (if (ctx eqn) (append (ctx eqn) premises) (cons '*&* premises)))
  (setq l2 (flatten-eqn (change-ctx eqn l2)))

; ---- XH begin
  (setf $x_state 'pre)
; ---- XH end

  (setf t9 (cover-proof-process l2 step (append1 num 2) t))
  )

  (pop $case-split-terms)

  (when (and t4 t9 (> $trace_flag 1))
	(terpri)
	(princ "Following equation is proven successfully by case-split:") 
	(terpri) (princ "    ") (write-seq-eqn num oldeqn)
	)

  (and t4 t9)
)


; -- 10/02/90 --
; -- 10/09/90 --
 
(defun cover-proof-process2 (eqn num step &aux l2)
  (if* (and (null $x_choose_term) (> $cover-auto-level 5)) then

      ;-- XH begin --
      (setf $x_fail 'no-scheme) 
      (setf $xnode (search-tree num $root))
      (setf (node-status $xnode) 'fail)
      (setf (node-source $xnode) $x_fail)
      ; -- XH end --

      nil

      ;; 2/2/1992-start
      elseif (setq l2 (has-hint-term (ctx eqn)))
      then (proof-by-hint-term l2 eqn num step)
      ;; 2/2/1992-end

      elseif (and $case-cond (setq l2 (build-premises-from-cond-term eqn)))
      then (proof-under-new-premises l2 eqn num step)

      elseif (and $case-bool (setq l2 (build-premises-from-bool-term eqn)))
      then (proof-under-new-premises l2 eqn num step t)

      elseif (and $abstract-proof (building eqn num (sub1 step)))
      then t

      elseif (and $abstract-proof (abstract-proof eqn num (sub1 step)))
      then t

      elseif (and (< step 3) (> (length (ctx eqn)) 9))
      then (if* (> $trace_flag 1) then 
	       (terpri) (princ "We won't prove it by induction because it has too many premises:")
	       (terpri) (princ "   ") (write-seq-eqn num eqn))

           ;-- XH begin --
           (setf $x_fail 'ctx-size) 
	   (setf $xnode (search-tree num $root))
	   (setf (node-status $xnode) 'fail)
	   (setf (node-source $xnode) $x_fail)
	   ; -- XH end --

           (push eqn $failed-eqns) 
	   nil

      elseif (< step 1) then
            (if* (> $trace_flag 1) then
		(terpri) (princ (uconcat "Proof failed at Step " $step-deep ":"))
		(terpri) (princ "   ") (write-seq-eqn num eqn))

           ;-- XH begin --
           (setf $x_fail 'too-deep) 
	   (setf $xnode (search-tree num $root))
	   (setf (node-status $xnode) 'fail)
	   (setf (node-source $xnode) $x_fail)
	   ; -- XH end --

	    (push eqn $failed-eqns)
	    nil

      elseif (and (null $x_choose_term) (> $cover-auto-level 3)) then

      ;-- XH begin --
      (setf $x_fail 'no-scheme) 
      (setf $xnode (search-tree num $root))
      (setf (node-status $xnode) 'fail)
      (setf (node-source $xnode) $x_fail)
      ; -- XH end --

      nil
      elseif (setq l2 (cover-set-scheme eqn num))
      then (induc-subgoal-proofs l2 eqn num step)
      elseif (and (null num)
		  (setq l2 (structure-induc-on eqn num)))
      then (induc-subgoal-proofs l2 eqn num step)
      elseif (setq l2 (have-boolean-constant eqn))
      then (proof-under-new-premises 
	    (list 'cond l2 $true-term $false-term) eqn num step)
      else 
      (if (null num) (setq $first-induc-op nil))
      (if* (> $trace_flag 1) then 
	  (terpri) (princ "No induction schemes are possible for:")
	  (terpri) (princ "   ") (write-seq-eqn num eqn))

      ;-- XH begin --
      (setf $x_fail 'no-scheme) 
      (setf $xnode (search-tree num $root))
      (setf (node-status $xnode) 'fail)
      (setf (node-source $xnode) $x_fail)
      ; -- XH end --

      (push eqn $failed-eqns) nil))

(defun trace-generated-result (done num2 new num eqn)
   (terpri)
   (if* done 
       then (princ "Generalized lemma is proven: ") (terpri) 
          (princ "   ") (write-seq-eqn num2 new)
     else (princ "Fail to prove the generated lemma: ") (terpri)
          (princ "   ") (write-seq-eqn num2 new)
;          (setf $x_fail 'gen-lemma) ; -- added by XH --
	  (princ " of") (write-seq-eqn num eqn)))



; -- new3.lsp --
; -- 10/05/90 --


(defun split-premises (new pres vars tuples eqn num &aux junk)
  ; tuples are induction hypotheses.
  ; eqn is conditional.
  ; Return a list of eqnations.
  (setq ; pres (cdr pres)
	junk (or-condi-eqn vars eqn)
	junk (sloop for tup in tuples 
		   collect (premises-instances vars tup junk))
	junk (rem-dups junk)
        junk (proper-product-lists junk))

  (setq junk (sloop for xa in junk 
		    collect (change-ctx new (append pres (copylist xa)))))

  (if* (and (cdr junk) (> $trace_flag 1)) then 
      (terpri)
      (princ "Subgoal") (write-seq-num num) 
      (princ "is split into:") (terpri)
      (sloop for xa in junk for n from 1 do
	(write-seq-eqn (append1 num n) xa)))


; ---- XH begin
; -- in this case, we don't prove the eqn-"num" but we have to
;    link a "virtual node" to the proof tree as  parent of those
;    splitted conjectures.
; -- Note that a virtual node can not be restarted!
    (if* (rest junk) then
          (setf $peek (search-tree (butlast num) $root))               
          (add_child $peek num nil
                    $seq-no   'isp  'virtual   eqn )
          (setf $seq-no (+ 1 $seq-no))
	  (debug-msg "Handle split-premises")
	  ;; (show-tree $root)
    )
    (setf $x_state 'csp)
; ---- XH end

  junk)


(defun form-subgoals-from-patterns (conj vars eqn num &aux pres neweqn)
  ; Substitute "vars" of "eqn" by the terms in "conj" to make conjectures,
  ; i.e, a list of equations.
  (setq pres (car conj)
	neweqn (eqn-instance vars (cadr conj) eqn))

   (setf $x_state 'ind)  ; -- added by XH
     
  (if* (ctx eqn) then 
      (setq pres (merge-premises pres (ctx neweqn)))
      (if* (cddr conj) then
	  (split-premises neweqn pres vars (cddr conj) eqn num)
	  else
	  (ncons (change-ctx neweqn pres)))
      elseif (cddr conj) then
      (setq pres (merge-premises pres (form-premises-from-conj (cddr conj) vars eqn)))
      ;;(write-eqn $induc) (mark "DEBUG3")
      (ncons (change-ctx neweqn pres))
      else
      ;;(write-eqn $induc) (mark "DEBUG4")
      (ncons (change-ctx neweqn pres))))


; -- new5.lsp --
(defun reduction-proof (eqn num &aux new)
  ; return nil iff eqn is proved by reduction or by adding new premises.
  (setq $used-rule-nums nil)
  (setq new (cover-normalize eqn))
  (print-normalized-eqn eqn new num)

  (if* (or (null new) (null (car new))) then
      ; -- XH begin -- 
      (if* (endp num)
              (setf $xnode (search_by_eqn eqn (list $root)))
	      (setf $xnode (search-tree num $root)))
      (if* (equal '(not find) $xnode) then nil
	   else
	      (setf (node-source $xnode) $used-rule-nums)
              (setf (node-status $xnode) 'true))
      ; -- XH end --
      nil
      else new))

(defun debug-msg (&rest rest)
  (if* $debug (dolist (xa rest) (princ xa) (terpri))))


(defun x_initial (eqn)
	     (setf $seq-no   1)
	     (setf $eqn-pool nil)
             (setf (node-label  $root) nil
	           (node-source $root) nil
                   (node-seqno  $root) $seq-no
                   (node-state  $root) '>
                   (node-status $root) nil

		   (node-info   $root) eqn
		   (node-parent $root) nil
		   (node-chdlst $root) nil)
	     (setf $leaf     $root)
	     (setf $peek     $root)
             (setf $cursor   $root)
	     (setf $seq-no (+ 1 $seq-no))
             (setf $x_hint  nil)
             (setf $x_restart_eqn   nil)
	     (setf $x_restart_seqno '1)
             (setf $x_fail  'none)
)



; -- 8/6/91 -- XH



(defun x_name (name nmap)
;; according to nmap, find the inside name  of "name" 
;; names -- a user input variable name
;; nmap -- a list of pairs, ((#:X . "X") (#:Y . "Y") ....) indicating
;;         the relation between inside name and print name.
;; (x_name 'y '((#:x . "x") (#:y . "y") ....)) returns  #:y
  ;; covert name into a string, say x to "x"
  (setq name (get_pname name))
  (sloop for xa in nmap
	if (equal (cdr xa) name)
	   return (car xa)))

(defun x_real_vars (vars nmap)
;; vars -- a list of variables
;; nmap -- the mapping list 
;; (x_real_vars vars) returns the inside name list of vars
  (sloop for xa in vars
	collect (x_name xa nmap)))

(defun x_read_term ()
;; this is a copy read-t-term with modified prompt.
  (if* (is-empty-line $in-port) then 
          (princ "By induction on the term you input as: ") )
   (let (term (buffer (make-buffer $in-port)))
     (if* (not (eq (token-eoln buffer) 'eof)) then
	  (setq term (*catch 'error (get-rhs buffer))))
     (if* (and term (nequal term 'error)) then
       (setq term (first term))


      (if* $log-port then (write-term term $log-port) (terpri $log-port))
      (if* $in-port then (write-term term) (terpri))
      term)))

(defun x_get_induc_term (eqn &aux nmap term vars flag option)
;; from given eqn, get variable mapping list l__2
;; ask user input a term, then change its var list according to l__2
  (setf $x_choose_term nil)
  (princ "Prove equation:" ) (terpri)
  (write-eqn eqn)
  (setq nmap l__2)
  
  (setq option nil)
  (sloop while t do
    (when option (return term))
    (setq term (x_read_term))

    ; check if the input term is valid here
    (setq $newops nil)
    (setq flag nil)
    (setq flag (*catch 'error  (expecting-functions term)))
    (setq vars (x_real_vars (rest term) nmap))
    (setq term (cons (first term) vars))
    (setq option (and (not (eq flag 'ERROR)) 
                      (null $newops) 
                      (> (get-arity (op-of term)) 0 )))
    (if* (null option) (princ "Invalid term, try again : "))
   )
)


(defun cover-proof-process (eqn step &optional num norm 
                            &aux x_eqn eqn0 x_step-deep  result x_exit)
  ;; x_eqn -- save the original eqn to prove;
  ;; eqn0  -- save the resulting equation after manual_induction;
  ;; eqn   -- the equation being proven currently.

  ; Return t iff "eqn" is a theorem.

  ; check whether eqn is in the proof tree; if not, add it in.
  (check_and_add eqn num)

; ---- save current state ----
  (setf x_eqn eqn
        x_step-deep $step-deep)

; ---- initialization ----
  (setf eqn0 eqn)
  (setf x_exit nil)
  (setf result nil)

; ---- main loop ----
  (sloop while t do
   (when x_exit (return result))

   ; ---- get hints from user ----
   (cond  ((and  $x_hint (or (equal eqn   $x_restart_eqn)
                             (equal eqn0  $x_restart_eqn)
                             (equal x_eqn $x_restart_eqn))) 
              (setf eqn0 (x_manual_induc $x_restart_eqn step num x_step-deep))
              ; -- link eqn0 to proof tree if needed.
              (if* (and (not (null eqn0)) (not (equal eqn eqn0))) then
                    (setf $peek (search_by_id $x_restart_seqno (list $root)))
                    (add_child $peek 
                               (node-label $peek) nil $seq-no 
                               'man    nil eqn0)
                    (setf $seq-no (+ 1 $seq-no))
                    (if* (endp num) (setf $leaf $xnode)
		                    nil)
              )       
              (setf eqn eqn0)
          )
          ( t  nil )
   )
   ; ---- auto proof ----
   (cond ((and (not (endp eqn)) (not $x_hint))
            ; -- ported from auto_induc --
            (if* (= $trace_flag 3) then 
                (terpri) (princ (uconcat "Down " (- $step-deep step) ": ")) (terpri)
                (princ "Proving") (write-seq-eqn num eqn))

            (if norm (setq eqn (reduction-proof eqn num)))
            ; ---- XH begin ----
            (if* (and (not (equal eqn x_eqn)) 
		      (not (equal eqn eqn0))
		      (not (null eqn)))       
		 then
		 ;; -- link eqn to proof tree
		 (cond ((endp num) 
			(add_child $leaf
                                   (node-label $leaf) nil
                                   $seq-no  'nor  nil  eqn )
			(setf $leaf   $xnode))
		       (t (setf $peek (search-tree num  $root))
			  (add_child $peek
				     num  nil
				     $seq-no  'nor nil eqn ))
		       )
		 (setf $seq-no (+ 1 $seq-no))
		 )
             ; ---- XH end ----		    
	    (if* (null eqn) then
                 (setf result t)      
		 else
                 (setf result (x_auto_induc eqn step num norm))))
            
	 ;; ---- eqn is reduced to nil ----
         ((endp eqn)
	  (setf result t))
         
         (t nil)
	 )

   ;; ---- post processing ----
   (cond
         ; success proof
         ( result  (setf x_exit t))  
         ; tracing the restarting eqn
         ((equal $x_fail 'none)
                   (if* $x_hint (if* (or (equal eqn   $x_restart_eqn)
                                       (equal eqn0  $x_restart_eqn)
                                       (equal x_eqn $x_restart_eqn))
                                                              (setf x_exit nil)
                                                              (setf x_exit t))
                               (setf x_exit t)))
 
         ; current proof failure
	 ( t       (if* (and (null $x_hint) (< 1 $cover-auto-level)) then
                        (setf x_exit (x_failure_handler eqn num)))
                   (cond ( x_exit (setf $x_fail 'none
					result  nil))
			 ;; current node is the restarting node
                         ( t   (setf $x_fail 'none
			             result  nil)
         	              (setf x_exit (not (or (equal eqn $x_restart_eqn)
                                              (equal x_eqn $x_restart_eqn)))))))
   )
  )
)

;; from prove.lsp
(defun succ-end-induc ()
   (terpri)
   (princ "Following equation") (terpri)
   (princ "    ") (write-eqn $prove-eqn)
   (princ "    is an inductive theorem in the current system.") (terpri)
   (cond ($induc 

	  (when (null $x_indhyps)
		(if (eq (op-of (lhs $induc)) 'cond)
		    (query-add-eqn $prove-eqn)
		  (*catch 'refuted (*catch 'prove (*catch 'kb-top (*catch 'reset
  	 	      (add-time $proc_time 
				(order-one-norm-others $induc))))))))

	  (setq $x_indhyps (reverse $x_indhyps))
	  (when (> $trace_flag 1)
		(terpri) 
		(sloop for xa in $x_indhyps do (princ "Adding rule:") (write-rule xa))
		(terpri))
	  (setq $rule-set (append $rule-set $x_indhyps)
		$x_indhyps nil)

	  (setq $prove-eqn nil
		$guest-eqn nil
		$succ-eqns nil)
	  )
	 ; >>>> 1/30/89
	 (t (terpri)
	    (if* (not (ok-to-continue
		      "Do you want to keep the theorem in the system ? "))
		then (if* $no-history
			 then (setq $prove-eqn nil)
			 else (sloop while $prove-eqn do (undo1)))
		(princ "The previous system is restored.") (terpri)
		else
		(setq $prove-eqn nil
		      $confluent t)))))

;; --- 8/13/91 ---

(defun x_cover-proof-process2 (eqn num step &aux l2)
  ;; -- this is a modified version of cover-proof-process2 --
  (if (not $strong-induc)
      (cover-proof-process2 eqn num step)
    (let ()
      (setq $x_indeqn eqn) ; save the eqn to do induction on
      (if* (null eqn) then t
	   elseif (and $case-cond (setq l2 (build-premises-from-cond-term eqn)))
	   then (proof-under-new-premises l2 eqn num step)
	   elseif (and $case-bool (setq l2 (build-premises-from-bool-term eqn)))
	   then (proof-under-new-premises l2 eqn num step t)
	   elseif (building eqn num (sub1 step))
	   then t
	   elseif (abstract-proof eqn num (sub1 step))
	   then t
	   elseif (and (< step 3) (> (length (ctx eqn)) 9))
	   then (if* (> $trace_flag 1) then 
		     (terpri) (princ "We won't prove it by induction because it has too many premises:")
		     (terpri) (princ "   ") (write-seq-eqn num eqn))
	   ;;-- XH begin --
           (setf $x_fail 'ctx-size) 
	   (setf $xnode (search-tree num $root))
	   (setf (node-status $xnode) 'fail)
	   (setf (node-source $xnode) $x_fail)
	   ;; -- XH end --
           (push eqn $failed-eqns) nil
      elseif (< step 1) then
            (if* (> $trace_flag 1) then
		(terpri) (princ (uconcat "Proof failed at Step " $step-deep ":"))
		(terpri) (princ "   ") (write-seq-eqn num eqn))
           ;-- XH begin --
           (setf $x_fail 'too-deep) 
	   (setf $xnode (search-tree num $root))
	   (setf (node-status $xnode) 'fail)
	   (setf (node-source $xnode) $x_fail)
	   ; -- XH end --
	    (push eqn $failed-eqns)
	    nil
      elseif (setq l2 (cover-set-scheme eqn num)) 
      then (strong-subgoal-proofs eqn num l2 step)      ;; -- new -- strong induction
      else 
      (if* (null num) (setq $first-induc-op nil))
      (if* (> $trace_flag 1) then 
	  (terpri) (princ "No induction schemes are possible for:")
	  (terpri) (princ "   ") (write-seq-eqn num eqn))
      ;-- XH begin --
      (setf $x_fail 'no-scheme) 
      (setf $xnode (search-tree num $root))
      (setf (node-status $xnode) 'fail)
      (setf (node-source $xnode) $x_fail)
      ; -- XH end --
      (push eqn $failed-eqns) nil)
      )))

(defun x_remove_hyp (conjs &aux result)
; conjs -- given conjectures ((var1 var2 ...) pat1 pat2 ...)
;          where pattern is ((term1 term2 ...) cond (hyp1 hyp2 ...) (...) ...)
; x_remove_hyp replace (hyp1 hyp2 ...) (...) ... by nil in each pattern of conjs
  (setf result (cons (first conjs) 
                     (sloop for pat in (rest conjs)
		          collect (cons (first pat) (cons (second pat)  nil))))))

(defun strong-subgoal-proofs (eqn num l2 step)
  ;; -- if eqn is proven, return T; otherwise returns nil --
  (push (cons (cons (eqn-as-rule-info) $induc-vars) eqn) $induc-eqns)
  (if* (x_math_ind 
	  (sloop for n from 1 for e1 in (cdr l2) 
		 collect (cons (append1 num n) 
			       (car (form-subgoals-from-patterns 
				     e1 (car l2) eqn (append1 num n)))))
	  (sub1 step))
	then
	(if* (> $trace_flag 1) then (trace-succ-prove eqn num))
	(push eqn $succ-eqns)
	(if* num then 
	    (push eqn $eqn-set)
	    (order-eqns))
	(pop $induc-eqns)
	else
	; -- strong induction fail --
        (setf $x_fail 'reduc-less) 
        (setf $xnode (search-tree num $root))
	(setf (node-status $xnode) 'fail)
	(setf (node-source $xnode) $x_fail)
	(pop $induc-eqns)
	(push eqn $failed-eqns)
	nil
     ))

(defvar $x_avoid-terms nil)
(defun x_math_ind (num-eqns step &aux leqns)
  ;; apply strong induction on eqns, return T if success, nil otherwise.

  ;; normalize each eqn once
  (setf $x_avoid-terms nil)
  (sloop with neweqn
	 for num-oldeqn in num-eqns
	 for oldeqn = (cdr num-oldeqn) do
	 (setf oldeqn (flatten-eqn oldeqn))
	 (setf neweqn (reduction-proof oldeqn (car num-oldeqn)))
	 (when neweqn
	       (if (equal (lhs oldeqn) (lhs neweqn)) 
		   (push (lhs oldeqn) $x_avoid-terms))
	       (push (cons (car num-oldeqn) neweqn) leqns)
	       ))

  ;; try to rewrite eqns by ind-hyp once
  (if leqns (setq leqns (rewrite-once-by-hypo leqns)))

  ;; and then resume proving procedure
  (sloop for xa in leqns
	 always (cover-proof-process (cdr xa) step (car xa) nil))
  )

(defun rewrite-once-by-hypo (leqns &aux rule leqns2)
  (setf rule (orient-induc-hypo $x_indeqn))
  (if* rule then
       (setq leqns (nreverse leqns))
       (when (> $trace_flag 1)
	     (terpri) (princ "Apply the induction hypothesis:")(terpri)
	     (princ "    ") (write-rule rule) 
	     (princ "     to the following equation(s):") (terpri)
	     (sloop for xa in leqns do 
		    (princ "    ") (write-seq-eqn (car xa) (cdr xa))))

       ;; try one-rule-reduction using hypo.
       (sloop for xa in leqns 
	      for eqn = (cdr xa) do
	      (if* (and (null (ref-extra-pre-variables rule))
			(setq eqn (reduce-eqn-by-one-rule eqn rule)))
		  then 
		  (setf (eqn-source eqn) (nconc (eqn-source eqn) $used-rule-nums))
		  (setq $used-rule-nums nil)
		  (setq eqn (reduction-proof eqn (car xa)))
		  else 
		  (setq eqn (cdr xa))
		  (terpri) 
		  (princ "Warning: The induction hypothesis cannot apply to ") 
		  (terpri) (princ "    ") (write-seq-eqn (car xa) eqn)
		  )
	      (if eqn (push (cons (car xa) eqn) leqns2))
	      )
       (setq leqns leqns2)
       else
       (terpri) (princ "The induction hypothesis is not available !") (terpri)
       )
  leqns)

(defun orient-induc-hypo (rule)
  ;; return a rule iff the eqn can be oriented into a terminating rule.
  ;; otherwise, nil.
  (setq rule (*catch 'reset (orient-rule rule)))
  (cond ((eq rule '*reset*) nil)
        ((memq rule '(nil *kb-top*)) nil)
        (rule (enable-rule rule)
	      (push rule $x_indhyps)
	      rule)
	))

(defun clean-indhyp ()
    (sloop for xa in $x_indhyps do (disable-rule xa))
    (setq $x_indhyps nil))

(defun peqns (junk)
  (sloop for xa in junk for i from 1 do
	 (write-seq-eqn (ncons i) xa)))
