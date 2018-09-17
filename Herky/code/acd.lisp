(in-package "USER")

;;; Discrimination trees for AC terms. 
(defmacro ac-make-nodes () `(make-array $max-num-ac-args))

(defmacro ac-distree-reduce-at-root-by-one (rule term)
  `(setq $distree-sigma
	 (ac-match (ncons (list (lhs ,rule) ,term (null $ac))) nil nil)))

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
     (if (>= id $max-num-ac-args) (break "too many args of an ac op"))
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

(defun ac-find-rule-in-distree (term)
  ;; Find a rule in "distree", the left side of which "term" is likely an
  ;; instance.  Used to find rules to reduce "term".  
  ;; Return the rule if there is any, in this case,
  ;; substitution is in $var-bindings.
  (ac-find-rule-in-distree-aux $distree (ncons term) term 0 nil t))

(defun ac-find-rule-in-distree-aux (node args term &optional (nv-num 0) nv-args have-extra)
  ;; Auxiliary function of ac-find-rule-in-distree.
  ;; Note that we don't build substitutions as we walk down the distree 
  ;; -- we ignore variable bindings until we get to an rose, and then 
  ;; do a check for variable binding consistency.
  (let (children result first)
    (when (> (dtnode-num-of-rules node) 0)
	(setq children (dtnode-children node))

	(cond ((rose-p children)
	       ;; We are at the end of the path; check the variable bindings.
	       (if (or (> nv-num 0) (and args (not have-extra)))
		   (break "Nonempty args in ac-find-rule-in-distree-aux"))
	       (dolist (rule (rose-rules children))
		       (if (ac-distree-reduce-at-root-by-one rule term)
			   (return-from ac-find-rule-in-distree-aux rule))
		       ))

	      ;; Are children an array?
	      ((not (nodes-p children)) nil)

	      ;; Are there some nonvariable terms to skip?
	      ((> nv-num 0) 
	       (sloop for arg in nv-args 
		      if (and (nonvarp arg)
			      (aref children (op-of arg))
			      (setq result 
				    (ac-find-rule-in-distree-aux 
				     (aref children (op-of arg))
				     args term (1- nv-num) nv-args)))
		      return result))

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
	      ((aref children (op-of (setq first (car args))))

	       (if (ac-root first)
		   ;; First is an AC-root term.
		   (ac-find-rule-at-ac-op
		    (aref children (op-of first))
		    first have-extra (cdr args) term)

		 (ac-find-rule-in-distree-aux 
		  (aref children (op-of first)) 
		  (append (args-of first) (cdr args))
		  term)
		 ))

	       (t nil)
	      )))
  )

(defun ac-find-rule-at-ac-op (node term have-extra rest-args old-term)
  ;; Term is an AC-rooted term.
  ;; node is the first level acnode.
  (let ((length (length (args-of term))) (term-args (args-of term)) result)

    (sloop for arity from 2 to length 
	   if (and (nth-child arity node) 
		   (setq result (ac-find-one-rule-arity 
				 (nth-child arity node) 
				 arity
				 length
				 term-args
				 have-extra
				 rest-args
				 old-term)))
	   return result
	   finally (return nil)
	   )))

(defun ac-find-one-rule-arity (node arity length term-args have-extra rest-args old-term)
  ;; node is the second level acnode.
  (when (> (dtnode-num-of-rules node) 0)
	(let ((nv-num 0)
	      result)
	  (sloop for ab in term-args if (nonvarp ab) do (incf nv-num))
	  
	  (sloop for nvarity from 0 to (max nv-num arity)
		 if (and (nth-child nvarity node)
			 (or have-extra  ;; the ac op is the outmost of the lhs 
			     (neq arity nvarity) ;; there is a variable.
			     (= nvarity length)) ;; there is no variable.
			 (setq result (ac-find-one-rule-nvarity 
				       (nth-child arity node) 
				       rest-args
				       old-term
				       nvarity
				       term-args
				       have-extra)))
		 return result
		 finally (return nil)
		 ))))

(defun ac-find-one-rule-nvarity (node rest-args old-term nvarity term-args have-extra)
  ;; node is the third level acnode.
  (ac-find-rule-in-distree-aux node 
			       rest-args
			       old-term
			       nvarity
			       term-args
			       have-extra
			       ))

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
		(ac-find-roses-at-ac-op (car args) (cdr args) top
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

(defun ac-find-roses-at-ac-op (term rest-args top node)
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

(defun print-distree-aux (n &optional (leader "") (addition "") (arrow "") (ac 0))
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
			      (print-distree-aux 
			       (nth-child i n)
			       (concatenate 'string leader addition)
			       "|  "
			       "|--"
			       ac
			       )
			    (print-distree-aux 
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
