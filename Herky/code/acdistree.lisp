(in-package "USER")

;;; Discrimination trees for AC terms. 
(defmacro ac-make-nodes () `(make-array $max-num-ac-args))

(defmacro make-triple (t1 t2 t3) `(list ,t1  ,t2, t3))
(defmacro ac-distree-reduce-at-root-by-one (rule term)
  `(setq $distree-sigma
	 (ac-match (ncons (make-triple (lhs ,rule) ,term (null $ac))) nil nil)))

(defmacro ac-insert-lhs-to-distree (rule)
  ;; Insert all nonvar subterms of the lhs of rule into the distree.
  `(dolist (arg (args-of (lhs ,rule)))
	   (if (nonvarp arg) 
	       (ac-insert-subs-to-distree 2 arg ,rule $distree))))

(defmacro ac-insert-rhs-to-distree (rule)
  ;; Insert all nonvar subterms of the rhs of rule into the distree.
  `(if (and (nonvarp (rhs ,rule))
	    (not (member (op-of (rhs ,rule)) *true*false*)))
       (ac-insert-subs-to-distree 3 (rhs ,rule) ,rule $distree)))

(defun ac-insert-whole-rule-to-distree (rule)
  ;; Insert the rule and its nonvar subterms to the distree.
  (if (neq (op-of (lhs rule)) *=*) (ac-insert-rule-to-distree rule))
  (if (> $reduce-system 0) (ac-insert-lhs-to-distree rule))
  (if (> $reduce-system 2) (ac-insert-rhs-to-distree rule))
  )

(defun ac-insert-rule-to-distree (rule &aux rose)
  ;; Insert the rule into the distree.
  (setq rose (ac-find-create-rose (lhs rule) $distree t))
  ;(update-num-of-roses (rose-parent rose) 1)
  (insert-to-rose 1 rule rose rule)
  )

(defun ac-insert-subs-to-distree (type term eqn distree 
				    &aux rose (terms (list term)))
  ;; Insert all the nonvar subterms of "term" into the distree. 
  (while terms 
    (setq term (pop terms))
    (setq rose (ac-find-create-rose term distree))
    ;(update-num-of-roses (rose-parent rose) 1)
    (insert-to-rose type (cons term eqn) rose eqn)
    (if (nonvarp term)
	(dolist (xa (args-of term)) (if (nonvarp xa) (push xa terms))))
    ))

(defun ac-find-create-rose (term distree &optional is-rule)
  ;; Return the rose of "distree" along the path indicated by "term".
  ;; If the path is incomplete, create necessary new nodes and/or
  ;; a rose in "distree".
  (setq $current-node distree)
  (if is-rule (incf (dtnode-num-of-rules $current-node)))

  (ac-find-end-node term is-rule)

  (if (rose-p (dtnode-children $current-node))
      (dtnode-children $current-node)
    (setf (dtnode-children $current-node) 
	  (make-rose :parent $current-node))
    ))

(defmacro ac-replace-current-node-by-nth-child ()
  ;; If there is an nth-child, replace $current-node by it.
  ;; If not, create a new node, and assign it as the nth-child
  ;; of $current-node and replace $current-node by the node.
  `(let ()

     ;; First Level ac-node: id = id-of-ac-op
     (cond ((dtnode-p (nth-child id $current-node))
	    (setq $current-node (nth-child id $current-node))
	    (if is-rule (incf (dtnode-num-of-rules $current-node)))
	    )

	   (t ;; if not, create a new node.
	    (let ((node (make-dtnode :parent $current-node :id id
				     :num-of-child 0
				     :num-of-rules (if is-rule 1 0)
				     :children (ac-make-nodes)
				     )))
	      (setf (nth-child id $current-node) node)
	      (incf (dtnode-num-of-child $current-node))
	      (setq $current-node node)
	      )))

     ;; Second Level ac-node: id = arity i.e., |args(term)|.
     (setq id (length (args-of term)))
     (if (>= id $max-num-ac-args) (setq id (1- $max-num-ac-args)))
     ; (break "too many args of an ac op")
     (cond ((dtnode-p (nth-child id $current-node))
	    (setq $current-node (nth-child id $current-node))
	    (if is-rule (incf (dtnode-num-of-rules $current-node)))
	    )

	   (t ;; if not, create a new node.
	    (let ((node (make-dtnode :parent $current-node :id id
				     :num-of-child 0
				     :num-of-rules (if is-rule 1 0)
				     :children (ac-make-nodes)
				     )))
	      (setf (nth-child id $current-node) node)
	      (incf (dtnode-num-of-child $current-node))
	      (setq $current-node node)
	      )))

     ;; Third Level ac-node: id = nv-arity i.e., the number of nonvars in args(term).
     (setq id 0) 
     (sloop for arg in (args-of term) do (if (nonvarp arg) (incf id)))
     (if (>= id $max-num-ac-args) (setq id (1- $max-num-ac-args)))
     (cond ((dtnode-p (nth-child id $current-node))
	    (setq $current-node (nth-child id $current-node))
	    (if is-rule (incf (dtnode-num-of-rules $current-node)))
	    )

	   (t ;; if not, create a new node.
	    (let ((node (make-dtnode :parent $current-node :id id
				     :num-of-child 0
				     :num-of-rules (if is-rule 1 0)
				     :children (make-nodes)
				     )))
	      (setf (nth-child id $current-node) node)
	      (incf (dtnode-num-of-child $current-node))
	      (setq $current-node node)
	      )))
     ))

(defun ac-find-end-node (term is-rule &aux id (terms (list term)))
  ;; This is a recursive procedure which visits the term
  ;; in the outer-left-most order. During the visiting,
  ;; $current-node goes down along a path.
  ;; When the last call to "find-end-node" ends,
  ;; $current-end is the end node of the path.
  (while terms
    (setq term (pop terms))
    (setq id (if (variablep term) 0 (op-of term)))

    ;; Does the current node have children?
    (find-children-of-current-node)

    ;; Is there a node at the place of that child?
    (if* (ac-op-p id) 
	 then
	(ac-replace-current-node-by-nth-child)
	;; Are there more terms to visit?
	(sloop for arg in (reverse (args-of term))
	       if (nonvarp arg) do (push arg terms))
	else
	(replace-current-node-by-nth-child id)
	;; Are there more terms to visit?
	(cond ((= id 0) nil)
	      (t (setq terms (append (args-of term) terms))))
	)))

(defun ac-insert-args-to-distree (args is-rule &aux (id (length args)))
  ;; ARGS are the arguments of an AC operator.
  ;; $current-node contains that AC operator.
  ;; Store only the outmost symbol of each argument along 
  ;; one path in the discrimination tree.
  
  ;; ID cannot be greater than $chidren-size.
  ;; That's a termporary solution.
  (if (>= id $children-size) (setq id 1))

  ;; Does the current node have children?
  (find-children-of-current-node)
  ;; Is there a node at the place of that child?
  ;; This node tells us how many arguments.
  (replace-current-node-by-nth-child id)

  (dolist (term args)
	  (setq id (if (variablep term) 0 (op-of term)))
	  ;; Does the current node have children?
	  (find-children-of-current-node)

	  ;; Is there a node at the place of that child?
	  (replace-current-node-by-nth-child id)
	  ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Find a rule for rewriting.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ac-find-rule-in-distree (term)
  ;; Find a rule in "distree", the left side of which "term" is likely an
  ;; instance.  Used to find rules to reduce "term".  
  ;; Return the rule if there is any, in this case,
  ;; substitution is in $var-bindings.
  (ac-find-rule-in-distree-aux $distree (ncons term) term t))

(defun ac-find-rule-in-distree-aux (node args term &optional have-extra)
  ;; Auxiliary function of ac-find-rule-in-distree.
  ;; Note that we don't build substitutions as we walk down the distree 
  ;; -- we ignore variable bindings until we get to an rose, and then 
  ;; do a check for variable binding consistency.
  ;;
  ;; Note: args is a list of mixed terms and term-lists.
  ;; term-lists is represented by (n t1 ... tn) where n is negative.
  ;;
  (let (children result first)
    (when (> (dtnode-num-of-rules node) 0)
	  (setq children (dtnode-children node))

	  (cond ((rose-p children)
		 ;; We are at the end of the path; check the variable bindings.
		 (if (and args (not have-extra))
		     (break "Nonempty args in ac-find-rule-in-distree-aux")
		     ;;nil
		   (dolist (rule (rose-rules children))
			   (if (ac-distree-reduce-at-root-by-one rule term)
			       (return-from ac-find-rule-in-distree-aux rule))
			   )))

	      ;; Are children an array?
	      ((not (nodes-p children)) nil)

	      ;; More arguments to search?
	      ((null args) nil)

	      ;; Is the variable node null?
	      ((and (aref children 0)
		    (setq result (ac-find-rule-in-distree-aux 
				  (aref children 0)
				  (cdr args) term)))
	       result)

	      ;; Is the first term in args a variable?
	      ((variablep (car args)) nil)

	      ;; Can the path pass through this node?
	      (t
	       (setq first (pop args))
	       (if* (< (car first) 0)
		    ;; Are there some nonvariable terms to skip?
		   then
		   (setq result (+ 1 (car first)))
		   (if (< result 0) (push (cons result (cdr first)) args))
		   (sloop for arg in (cdr first)
			  if (and (nonvarp arg)
				  (aref children (op-of arg))
				  (setq result 
					(ac-find-rule-in-distree-aux 
					 node
					 (cons arg args)
					 term)))
			  return result)
		   elseif (aref children (op-of first))
		   then
		   (if (ac-root first)
		       ;; First is an AC-root term.
		       (ac-find-rule-acnode1
			(aref children (op-of first))
			first have-extra args term)
		     (ac-find-rule-in-distree-aux 
		      (aref children (op-of first)) 
		      (append (args-of first) args)
		      term)
		     )))
	      ))))
  
(defun ac-find-rule-acnode1 (node term have-extra rest-args old-term)
  ;; Term is an AC-rooted term.
  ;; node is the first level acnode.
  (let ((length (length (args-of term))) (nvlength 0) term-args result)
    (sloop for arg in (args-of term)
	   if (nonvarp arg) do
	   (incf nvlength)
	   (if (not (member0 arg term-args)) (push arg term-args)))

    (sloop for arity from 2 to (min length (1- $max-num-ac-args))
	   if (and (nth-child arity node) 
		   (setq result (ac-find-rule-arity 
				 (nth-child arity node) 
				 arity
				 nvlength
				 length
				 term-args
				 have-extra
				 rest-args
				 old-term)))
	   return result
	   finally (return nil)
	   )))

(defun ac-find-rule-arity (node arity nvlength length term-args have-extra rest-args old-term)
  ;; node is the second level acnode.
  (when (> (dtnode-num-of-rules node) 0)
	  (sloop with result = nil
		 for nvarity from 0 to (min nvlength arity)
		 if (and (nth-child nvarity node)
			 (or have-extra  ;; the ac op is the outmost of the lhs 
			     (<  nvarity arity) ;; there is a variable.
			     (= nvarity length)) ;; there is no variable.
			 (setq result (ac-find-rule-nvarity 
				       (nth-child nvarity node) 
				       rest-args
				       old-term
				       nvarity
				       term-args
				       have-extra)))
		 return result
		 finally (return nil)
		 )))

(defun ac-find-rule-nvarity (node rest-args old-term nvarity term-args have-extra)
  ;; node is the third level acnode.
  (if (= nvarity 0)
      (ac-find-rule-in-distree-aux node rest-args old-term have-extra)
    (ac-find-rule-in-distree-aux node (cons (cons (- nvarity) term-args) rest-args)
				 old-term have-extra)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Normalizing terms using acdistree
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun ac-distree-norm-term (old &aux new)
  ;; Ensure that the returned term is flattened.
  (if (variablep old) 
      old 
    (if (equal (setq new (make-flat (ac-distree-norm-outermost old))) old)
	old
      (ac-distree-norm-term new))))

(defmacro ac-distree-rewrite-root (term)
  `(let (rule)
     (cond ((eq (op-of term) *=*)
	    (setq rule (reduce-at-eq-root term)))
	   ((eq (op-of term) *false*) nil)
	   ((eq (op-of term) *true*) nil)
	   ((setq rule (ac-find-rule-in-distree ,term))
	    (loop-check ,term) 
	    (remember-used-rule-num (ruleno rule))
	    (add-to-args rule $distree-sigma)
;	    (setq ,term (add-to-args rule $distree-sigma))
;	    (if (variablep ,term) ,term
;	      (compress-flat (op-of ,term) (args-of ,term)))
	    ))))

(defmacro ac-distree-norm-term-sigma (term sigma)
  ;  Apply mixed-strategy normalization on TERM.
  `(ac-distree-norm-term (applysigma ,sigma ,term))
  )

(defun ac-distree-reducible (term)
  (or (ac-find-rule-in-distree term)
      (sloop for arg in (args-of term)
	     thereis (and (nonvarp arg) (ac-distree-reducible arg)))
      ))

(defun ac-distree-norm-outermost (term)
  ; Does left-most outermost normalization on TERM.
  ;(if (nequal term (make-flat term)) (break "BAD"))
  (sloop while (nonvarp term) 
	 for term2 = (or (ac-distree-rewrite-root term)
			 (ac-distree-outred1 term))
	 if term2 do
	 (setq term term2)
	 else return nil)
  term)

(defun ac-distree-outred1 (term &aux margs)
  ; Called when term cannot be rewritten at root.  Try to rewrite
  ; the children in leftmost-outermost order.
  ;(write-term term) (mark "!" "TERM")
  (cond 
    ((ac-root term)
     (setq margs (mult-form (args-of term)))
     (cond 
      ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (ac-distree-rewrite-root xa)))
	      return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			    (removen (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil)))
      ((sloop for mxa in margs as xa = (car mxa)
	      if (and (nonvarp xa) (setq xa (ac-distree-outred1 xa)))
	      return (nconc (ncons (op-of term)) (ntimes (cdr mxa) xa)
			    (removen (car mxa) (args-of term) (cdr mxa)))
	      finally (return nil))))
     )
    ((sloop for xa in (args-of term) for i from 1
	    if (and (nonvarp xa) (setq xa (ac-distree-rewrite-root xa)))
	    return (replace-nth-arg i term xa)
	    finally (return nil)))
    ((sloop for xa in (args-of term) for i from 1
	   if (and (nonvarp xa) (setq xa (ac-distree-outred1 xa)))
	   return (replace-nth-arg i term xa)
	   finally (return nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; ac completion
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro distree-process-ac-critical-pair (uni)
  ; cut from acd-sup-term in critical.lisp.
  (let ((tmp1 (gensym)) (tmp2 (gensym)) (lhs (gensym)) (rhs (gensym))
        (ctx (gensym)) (eqn (gensym)))
    `(let (,tmp1 ,tmp2 ,lhs ,rhs ,ctx ,eqn)
       (caseq flag
         (1 (setq ,tmp1 (or (cdr (assq *xex1* ,uni)) *xex1*)))
         (2 (setq ,tmp1 (or (cdr (assq *xex1* ,uni)) *xex1*)
                  ,tmp2 (or (cdr (assq *xex2* ,uni)) *xex2*))))
       
       (setq $ncritpr (add1 $ncritpr)
             ,lhs (rplat-in-by pos lhs2
                                (add-rest-args 
                                  (rhs r1)
                                  (if ,tmp1 
                                      (make-term (op-of sub)
                                                 (ncons ,tmp1)))))
             ,rhs (add-rest-args (rhs r2)
                                  (if ,tmp2
                                      (make-term (op-of sub) 
                                                 (ncons ,tmp2))))
	     )

       (trace-message 4 "Process "
		      (trace-distree-cp 
		       (applysigma ,uni ,lhs) 
		       (applysigma ,uni ,rhs)
		       source))

       (add-time $norm-time 
          (setq $reduce-times $reduce-max
		,lhs (ac-distree-norm-term (applysigma ,uni ,lhs))
		$reduce-times $reduce-max
		,rhs (ac-distree-norm-term (applysigma ,uni ,rhs))
		))

       (unless (equal ,lhs ,rhs)
	    (setq ,lhs (make-eqn ,lhs ,rhs nil source))
	    (when (not (eqn-is-too-big ,lhs))
	      (if $trace-proof (update-used-rules ,lhs))
	      (when (setq ,lhs (orient-an-eqn ,lhs))
		    (add-time $add-time (ac-distree-add-rule ,lhs))
		    (if $check-unit-conflict
			(pure-unit-conflict-test ,lhs))
		    ))
	    )
       (setq $used-rule-nums nil)
       )))

(defun acd-sup-term (r1 r2 lhs2 sub pos flag &aux source unifs)
  ; sub is a subterm of lhs2, namely, the lhs of r2. 
  ; r1 will visit all subterms of lhs2. 
  ; r2 maybe an extended rule.
  ; If r1 is also an extended rule, in this case, r2 must be extednded, too,
  ; r1 does not need to visit all subterms of lhs2.

  (unless (is-superposed-sub sub)
      (cond ((eq pos 3) (setq pos nil))
            ((same-root (lhs r1) sub)
	     (when (setq unifs (unifiers (lhs r1) sub flag))
		   (setq source (ac-critical-source))
		   (sloop for uni in unifs 
			  if (or (not $polynomial)
				 (and (is-degree-qualified uni (product-degree (lhs r1)) (ref-lhs-vars r1))
				      (is-degree-qualified uni (product-degree (lhs r2)) (ref-lhs-vars r2))))
			  do
			  (setq $superposed-sub sub)
			  (trace-message 4"" 
					 (trace-superpose (ruleno r1) (ruleno r2) sub uni))
			  (if (if $ac-distree
				  (distree-process-ac-critical-pair uni)
				(process-ac-critical-pair uni))
			      (return nil))))))

      (if* (and (not (predicatep (op-of (lhs r1)))) (neq 2 flag)) then
	   (sloop for xa in (args-of sub) as l1 from 1 
		  if (or (is-deleted-rule r1)
			 (is-deleted-rule r2)) return nil 
		  else if (nonvarp xa) 
		  do (acd-sup-term r1 r2 lhs2 xa (append1 pos l1) flag)))))

(defun ac-distree-add-rule (rule)
  ;; Add rule to the distree.
  (if (eq (op-of (lhs rule)) *=*) 
      (push-end rule $subsume-rules)
    (ac-insert-rule-to-distree rule))
  (add-rule-primitive rule)

  ;; Simplify lhss of other rules.
  (cond
   ((eq (op-of (lhs rule)) *=*) 
    (push-end rule $subsume-rules))

   ((order-condition rule)
    (sloop for eqn in $subsume-rules
	   for new = (ac-reduce-by-one-rule (lhs eqn) rule)
	   if new do
	   (setq $subsume-rules (delete1 eqn $subsume-rules))
	   (trace-message 3 "" (trace-reduce-lhs eqn))
	   (ac-distree-clean-rule eqn) 
	   (setq new (make-eqn-from-deleted-rule eqn new (ruleno rule)))
	   (process-del-rule new eqn)
	   ))

   ((and (is-reduction rule)
	 (> $reduce-system 0))
    (reduce-other-rules rule)
    ))

  (when (not (is-scheme-rule rule))
	(if $idem-superpose (add-pairs (rule-x-to-y rule) rule))
	(add-all-pairs (rule-x-to-y rule)))
  )

(defun ac-distree-clean-rule (rule &aux (rose (rule-rose rule)))
  (setq $aux-rules (delete1 rule $aux-rules))
  (incf $num-del-rules)

  (setq $rule-set (delete1 rule $rule-set))
  (if $keep-deleted-rules (push-end rule $del-rules))
  (set-deleted-mark rule)

  (when rose
	(setf (rose-rules rose) (delete1 rule (rose-rules rose)))
	(dec-rule-nums-in-distree (rose-parent rose))
	(if (is-empty-rose rose) (delete-one-rose (rose-parent rose)))
	(setf (rule-rose rule) nil))
  )

#|
(defun ac-find-roses-in-distree (rule)
  ;; Find all roses of which terms are an instance of the left side of
  ;; rule. Store these roses in $roses-found
  (setq $roses-found nil)
  (ac-find-roses 0 (ncons (lhs rule)) $distree t)
  $roses-found)

(defun ac-find-roses (skip-num args node &optional top &aux children)
  ;; Auxilary function of find-roses-in-distree.
  (setq children (dtnode-children node))
  (cond

   ((= skip-num 0)
    (cond
     ((rose-p children)
      (if args (break "Nonempty args in find-roses"))
      (push children $roses-found))

     ;; Are children an array?
     ((not (nodes-p children)) nil)

     ;; Args cannot be empty.
     ((null args) (break "Empty args in find-roses"))

     ;; Is the first term in args nonvariable?
     ((nonvarp (car args))
      (when (aref children (op-of (car args)))
	    (if (ac-root (car args))
		(ac-find-roses-acnode1 (car args) (cdr args) top
					(aref children (op-of (car args))))
	      (ac-find-roses 0
			     (append (args-of (car args)) (cdr args))
			     (aref children (op-of (car args))))
	      )))

     ;; The first term in args must be variable now.
     (t

      ;; If the variable node is in the distree, visit that node first.
      (if (aref children 0)
	  (find-roses 0 (cdr args) (aref children 0)))
      
      ;; For each child-node of distree, skip the term
      ;; corresponding to the variable (car args) and recursively
      ;; handle the remaining terms in (cdr args).
      (sloop for id from 1 below $num-ops 
	     if (aref children id) do
	     (find-roses (get-arity id) (cdr args) (aref children id))))
     )) ;; (= skip-num 0)

   ;; The case when skip-num > 0.
   (t 
     ;; If the variable node is in the distree, visit that node first.
    (if (aref children 0)
	(find-roses (1- skip-num) args (aref children 0)))
     
    (sloop for id from 1 below $num-ops 
	   if (aref children id) do
	   (find-roses (1- (+ skip-num (get-arity id)))
			args (aref children id))))
    ))

(defun ac-find-roses-acnode1 (term rest-args top node)
  ;;
  (if (or top (variablep (car (last term))))
      (ac-find-roses-ac-hard (args-of term) rest-args node)
    (ac-find-roses-ac-easy (args-of term) rest-args node)))

(defun ac-find-roses-ac-easy (args rest-args node)
  ;; 
  (let ((id (length args)))
    (if (>= id $children-size) (break "ac-find-roses-ac-easy"))

    (when (setq node (nth-child node id))
	  (dolist (arg args)
		  (setq id (op-of arg))
		  ;; Does the current node have children?
		  (setq node (nth-child node id))
		  (if (not (dtnode-p node)) 
		      (return-from ac-find-roses-ac-easy nil)
		    ))

	  (if rest-args
	      (ac-find-roses 0 rest-args node)
	    (if (rose-p (dtnode-children node))
		(push (dtnode-children node) $roses-found))
	    ))
    ))

(defun ac-find-roses-ac-hard (args rest-args node)
  (let ((ln (length args)))
    (if (>= ln $children-size) (break "ac-find-roses-ac-hard"))

    (sloop for id from ln below $children-size do
	   (ac-find-roses-hard-aux id args rest-args (nth-child node id)))))

(defun ac-find-roses-ac-hard (n args rest-args node)
  (when node
	(cond 
	 ((= n 0)
	  (if rest-args
	      (ac-find-roses 0 rest-args node)
	    (if (rose-p (dtnode-children node))
		(push (dtnode-children node) $roses-found))))

	 ((null args) nil)

	 ((variablep (car args))
	  (sloop for id2 from 0 under $children-size do
		 (ac-find-roses-ac-hard 
		  (1- n) args rest-args (nth-child node id2))))

	 (t
	  (sloop with id = (op-of (car args))
		 for id2 from 1 under $children-size 
		 for node2 = (nth-child node id2)
		 if (dtnode-p node2)
		 do (if (= id id2)
			(ac-find-roses-ac-hard (1- n) (cdr args) rest-args node2)
		      (ac-find-roses-ac-hard (1- n) args rest-args nodes))
		 ))
	 )))
|#

(defun print-distree-aux-too (n &optional (leader "") (addition "") (arrow "") (ac 0))
  (format t "~a~a" leader arrow)
  (cond ((null n))
	((dtnode-p n)
	 (case (dtnode-id n) 
	       (*root* (princ "[root]"))
	       (t (case ac
		   (0 (if (eq (dtnode-id n) 0) (princ "[var]")
			(princ (op-name (dtnode-id n))))
		      (if (ac-op-p (dtnode-id n)) (setq ac 1)))
		   (1 (princ "arity=")  (princ (dtnode-id n)) (setq ac 2))
		   (2 (princ "nvarity=") (princ (dtnode-id n)) (setq ac 0))
		   )))
		    
	 (princ " rules=") (princ (dtnode-num-of-rules n))
	 (princ " succs=") (princ (dtnode-num-of-child n))
	 (terpri)
	 (cond 
	  ((rose-p (dtnode-children n))
	   (print-rose (dtnode-children n) 
			     (concatenate 'string leader addition)))
	  ((nodes-p (dtnode-children n))
	   (let ((num 0) (num2 0))
	   (dotimes (i $children-size) (if (nth-child i n) (incf num)))
	   (dotimes (i $children-size)
		    (when (nth-child i n) 
			  (incf num2)
			  (if (< num2 num)
			      (print-distree-aux-too 
			       (nth-child i n)
			       (concatenate 'string leader addition)
			       "|  "
			       "|--"
			       ac
			       )
			    (print-distree-aux-too 
			     (nth-child i n)
			     (concatenate 'string leader addition)
			     "   "
			     "`--"
			     ac
			     )
			    )))
	   ))
	  ))
	))

(defun act ()
  (sloop for rule in $rule-set do 
	 (ac-insert-rule-to-distree rule)
	 ;(ac-insert-lhs-to-distree rule)
	 ))

(defun act2 ()
  (sloop for rule in $rule-set do
	 (if (ac-find-rule-in-distree (lhs rule))
	     (princ (ruleno rule))
	   (princ rule))
	 (terpri)))

(defun actt () (setq $ac-distree t))
(defun acff () (setq $ac-distree nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun try-mixed-reduce (term &aux reduced new)
  ; Recursive function called by norm-mixed.
  ; Return nil if TERM is in normal form.
  (when (nonvarp term) 

	;; normalize root:
	(sloop with t2 = nil
	       if (and (nonvarp term) (setq t2 (rewrite-at-root term)))
	       do (setq term t2 reduced t)
	       else return nil
	       )

	(cond ((nonvarp term) 
	       ;; normalize arguments.
	       (setq new (cond 
			 ((ac-root term)
			  (sloop with margs = (mult-form (args-of term))
				 with newargs
				 with xb
				 for mxa in margs as xa = (car mxa) do
				 (if (and (nonvarp xa) (setq xb (try-mixed-reduce xa)))
				     (setq newargs (nconc newargs (ntimes (cdr mxa) xb))
					   new t)
				   (setq newargs (nconc newargs (ntimes (cdr mxa) xa))))
				 finally (if new 
					     (return 
					      (make-term (op-of term) (nreverse newargs))))))
			 ((sloop with newargs
				 with xb
				 for xa in (args-of term) do 
				 (if (and (nonvarp xa) (setq xb (try-mixed-reduce xa)))
				     (setq newargs (cons xb newargs)
					   new t)
				   (push xa newargs))
				 finally (if new 
					     (return 
					      (make-term (op-of term) (nreverse newargs))))))
			 ))
	      
	       (if new 
		   (if (and (nonvarp new) (setq term (rewrite-at-root new)))
		       ;; if the arguments are reduced, normalize the term again.
		       (or (try-mixed-reduce term) term)
		     new)
		 (if reduced term)
		 ))

	      ;; term is a variable.
	      (reduced term))))

