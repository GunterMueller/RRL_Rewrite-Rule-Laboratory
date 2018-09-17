(in-package "USER")

;;; Discrimination trees. 

(defmacro make-nodes () `(make-array $children-size))
(defmacro nth-child (id node) `(aref (dtnode-children ,node) ,id))
(defmacro nodes-p (children) `(arrayp ,children))

(defun re-init-distree ()
  (when (not (= $children-size $num-ops))
	(setq $children-size $num-ops)
	(setf (dtnode-children $distree) nil)
	(setf (dtnode-num-of-rules $distree) 0)
	(setf (dtnode-num-of-child $distree) 0)

	(when (eq $kb '*distree*) 
	      (dolist (rule $rule-set) 
		      (setf (rule-rose rule) nil)
		      (setf (rule-lhs-roses rule) nil)
		      (setf (rule-rhs-roses rule) nil)

		      ;; Add rule to the distree.
		      (insert-whole-rule-to-distree rule)
		      ))))

(defmacro insert-to-rose (type something rose eqn)
  ;; Insert eqn into a rose
  `(case ,type
	 (1 (push-end ,something (rose-rules ,rose))
	    ;; We need to find this rose from the rule.
	    (setf (rule-rose ,eqn) ,rose))

	 (2 (push-end ,something (rose-lhs-terms ,rose))
	    (push-end ,rose (rule-lhs-roses ,eqn)))

	 (3 (push-end ,something (rose-rhs-terms ,rose))
	    (push-end ,rose (rule-rhs-roses ,eqn)))

;	 (4 (push-end ,something (rose-eqn-terms ,rose)))
	 (t (break "insert-to-rose"))
	 ))

(defun insert-lhs-to-distree (rule)
  (dolist (arg (args-of (lhs rule)))
	   (if (nonvarp arg) (insert-subs-to-distree 2 arg rule $distree))))

(defun insert-rhs-to-distree (rule)
  (if (and (nonvarp (rhs rule)) (not (member (op-of (rhs rule)) *true*false*)))
       (insert-subs-to-distree 3 (rhs rule) rule $distree)))

(defun insert-whole-rule-to-distree (rule)
   ;; Add rule to the distree.
   (if (neq (op-of (lhs rule)) *=*) (insert-rule-to-distree rule))
   (if (> $reduce-system 0) (insert-lhs-to-distree rule))
   (if (> $reduce-system 2) (insert-rhs-to-distree rule))
   )

(defun insert-rule-to-distree (rule &aux rose)
  (setq rose (find-create-rose (lhs rule) $distree t))
  ;;(update-num-of-child (rose-parent rose) 1)
  (insert-to-rose 1 rule rose rule)
  rule
  )

(defun insert-eqn-to-distree (eqn)
  (insert-subs-to-distree 4 (lhs eqn) eqn $distree)
  (if (nonvarp (rhs eqn)) (insert-subs-to-distree 4 (rhs eqn) eqn $distree))
  )

(defun insert-subs-to-distree (type term eqn distree 
				    &aux rose (terms (list term)))
  (while terms 
    (setq term (pop terms))
    (setq rose (find-create-rose term distree))
    ;;(update-num-of-child (rose-parent rose) 1)
    (insert-to-rose type (cons term eqn) rose eqn)
    (if (nonvarp term)
	(dolist (xa (args-of term)) (if (nonvarp xa) (push xa terms))))
    ))

;; $current-node contains the current node in a distree.
;; Used only in the next two routines.

(defun find-create-rose (term distree &optional is-rule)
  ;; Return the rose of "distree" along the path indicated by "term".
  ;; If the path is incomplete, create necessary new nodes and/or
  ;; a rose in "distree".
  (setq $current-node distree)
  (if is-rule (incf (dtnode-num-of-rules $current-node)))

  (find-end-node term is-rule)

  (if (rose-p (dtnode-children $current-node))
      (dtnode-children $current-node)

    (setf (dtnode-children $current-node) (make-rose :parent $current-node))
    ; (dtnode-num-of-child $current-node) (1+ (dtnode-num-of-child $current-node))
    ))
    
(defmacro find-children-of-current-node ()
  `(if (dtnode-children $current-node)
	;; DUBUG INFO.
	(if (not (nodes-p (dtnode-children $current-node)))
	    (break "find-children-of-current-node"))
     (setf (dtnode-children $current-node) (make-nodes))))

(defmacro replace-current-node-by-nth-child (id)
  ;; If there is an nth-child, replace $current-node by it.
  ;; If not, create a new node, and assign it as the nth-child
  ;; of $current-node and replace $current-node by the node.
  `(cond ((dtnode-p (nth-child ,id $current-node))
	  (setq $current-node (nth-child ,id $current-node))
	  (if is-rule (incf (dtnode-num-of-rules $current-node)))
	  )

	 (t ;; if not, create a new node.
	  (let ((node (make-dtnode :parent $current-node :id ,id
				   :num-of-child 0
				   :num-of-rules (if is-rule 1 0))))
	    (setf (nth-child ,id $current-node) node)
	    (incf (dtnode-num-of-child $current-node))
	    (setq $current-node node)))
	 ))

(defun find-end-node (term is-rule &aux id (terms (list term)))
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
    (replace-current-node-by-nth-child id)

    ;; Are there more terms to visit?
    (if (> id 0) (setq terms (append (args-of term) terms)))
    )
  )

(defun dec-rule-nums-in-distree (node)
  ;; Decrease the rule number by 1 in the path from node to the root.
  (repeat (null node)
	  (decf (dtnode-num-of-rules node))
	  (setq node (dtnode-parent node))))

(defun delete-one-rose (node &aux (parent (dtnode-parent node)))
  ;; Update the rose number by -1 in the path from node to the root.
  (repeat (null parent)
	  (setf (nth-child (dtnode-id node) parent) nil)
	  (decf (dtnode-num-of-child parent))
	  (if (= (dtnode-num-of-child parent) 0)
	      (setq node parent
		    parent (dtnode-parent node))
	    (return nil))))

(defun update-num-of-child (node delta)
  ;; Update the term number by delta in the path from node to the root.
  (if (> delta 0)
      (repeat (null node)
	      (incf (dtnode-num-of-child node) delta)
	      (setq node (dtnode-parent node)))
      (repeat (null node)
	      (incf (dtnode-num-of-child node) delta)
	      (let ((parent (dtnode-parent node)))
		;; Delete a node if it contains nothing.
		(if (and parent (= (dtnode-num-of-child node) 0))
		    (setf (nth-child (dtnode-id node) parent) nil))
		(setq node parent)))))

;;; ****************

(defmacro find-rule-in-distree (term)
  ;; Find a rule in "distree", the left side of which "term" is an
  ;; instance.  Used to find rules to reduce "term".  
  ;; Return the rule if there is any, in this case,
  ;; substitution is in $var-bindings.
  `(find-rule-in-distree-aux (ncons ,term) $distree ,term))

(defmacro distree-reduce-at-root-by-one (rule term)
  `(when (setq $distree-sigma 
	       (if (is-linear-rule rule)
		   (linear-clash-free-match (lhs ,rule) ,term)
		 (clash-free-match (lhs ,rule) ,term)))
	 (or (is-reduction ,rule) 
	     (satisfy-order-condition ,rule $distree-sigma))
	 ))

(defun find-rule-in-distree-aux (args node term &aux children result)
  ;; Auxiliary function of find-rule-in-distree.
  ;; Note that we do build substitutions as we walk down the distree 
  ;; -- we ignore variable binding consistency check until we get to
  ;; an rose, and then do a consistency check.
  (when (> (dtnode-num-of-rules node) 0)
	(setq children (dtnode-children node))

	;; If we are at the end of the path, check the variable bindings.
	(cond ((rose-p children)
	       (if args (break "Nonempty args in find-rule-in-distree-aux"))
	       (dolist (rule (rose-rules children))
		       (if (distree-reduce-at-root-by-one rule term)
			   (return-from find-rule-in-distree-aux rule))
		       ))

	      ;; Are children an array?
	      ((not (nodes-p children)) nil)

	      ;; Is the variable node null?
	      ((and (aref children 0)
		    (setq result (find-rule-in-distree-aux 
				  (cdr args) (aref children 0) term)))
	       (return-from find-rule-in-distree-aux result))

	      ;; Is the first term in args a varialbe?
	      ((variablep (car args)) nil)

	      ;; Can the path pass through this node?
	      ((and (< (op-of (car args)) $children-size)
		    (aref children (op-of (car args))))
	       (find-rule-in-distree-aux 
		;; How to avoid this "append"?
		;; Using a global array will do!
		(append (args-of (car args)) (cdr args))
		(aref children (op-of (car args))) 
		term))
	      
	      (t nil)
	      )))

(defun find-roses-in-distree (rule)
  ;; Find all roses of which terms are an instance of the left side of
  ;; rule. Store these roses in $roses-found
  (setq $roses-found nil)
  (find-roses 0 (ncons (lhs rule)) $distree)
  $roses-found)

(defun find-roses (skip-num args node &aux children rose-num)
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
      (if (aref children (op-of (car args)))
	  (find-roses 0
		       ;; How to avoid this "append"?
		       ;; Using a global array will do!
		       (append (args-of (car args)) (cdr args))
		       (aref children (op-of (car args))))
	)) 

     ;; The first term in args must be variable now.
     (t

      ;; If the variable node is in the distree, visit that node first.
      (if (aref children 0)
	  (find-roses 0 (cdr args) (aref children 0)))
      
      ;; For each child-node of distree, skip the term
      ;; corresponding to the variable (car args) and recursively
      ;; handle the remaining terms in (cdr args).
      (setq rose-num (dtnode-num-of-child node))
      (sloop for id from 1 below $num-ops 
	     if (aref children id) do
	     (if (= rose-num 0) (return) (decf rose-num))
	     (find-roses (get-arity id) (cdr args) (aref children id))))
     )) ;; (= skip-num 0)

   ;; The case when skip-num > 0.
   (t 
     ;; If the variable node is in the distree, visit that node first.
    (if (aref children 0)
	(find-roses (1- skip-num) args (aref children 0)))

    (setq rose-num (dtnode-num-of-child node))     
    (sloop for id from 1 below $num-ops 
	   if (aref children id) do
	   (if (= rose-num 0) (return) (decf rose-num))
	   (find-roses (1- (+ skip-num (get-arity id)))
			args (aref children id))))
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; The following functions are used for debugging purpose.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun print-dtnode (node)
  (terpri) (princ "NODE: id=") (princ (dtnode-id node))
  (princ " rules=") (princ (dtnode-num-of-rules node))
  (princ " roses=") (princ (dtnode-num-of-child node))
  (princ " children=") 
  (princ 
   (cond ((nodes-p (dtnode-children node)) "array")
	 ((rose-p (dtnode-children node)) "rose")
	 (t "empty")))
  (terpri)
  )

(defun print-distree (tree)
  (terpri) (princ ";;; Discrimination Tree:") (terpri)
  (print-distree-aux tree))

(defun print-distree-aux (n &optional (leader "") (addition "") (arrow "") ac)
  (format t "~a~a" leader arrow)
  (cond ((null n))
	((dtnode-p n)
	 (case (dtnode-id n) 
	       (*root* (princ "[root]"))
	       (0 (princ "[var]"))
	       (t (if ac (princ (dtnode-id n)) 
		    (princ (op-name (dtnode-id n))))))
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
			       (if ac nil (ac-op-p (dtnode-id n)))
			       )
			    (print-distree-aux 
			     (nth-child i n)
			     (concatenate 'string leader addition)
			     "   "
			     "`--"
			     (if ac nil (ac-op-p (dtnode-id n)))
			     )
			    )))
	   ))
	  ))
	))

(defun print-rose2 (f) (print-rose f))
(defun print-rose (f &optional (leader "   "))
  (when (rose-rules f)
	(princ leader) (princ ">> Rules: ") 
	(dolist (rule (rose-rules f)) 
		(princ "[") (princ (ruleno rule)) (princ "],"))
	(terpri))

  (when (rose-lhs-terms f)
	(princ leader) (princ ">> LHS subs: ") 
	(dolist (term (rose-lhs-terms f))
		(princ "[") (write-term (car term)) (princ "],"))
	(terpri))

  (when (rose-rhs-terms f)
	(princ leader) (princ ">> RHS subs: ") 
	(dolist (term (rose-rhs-terms f))
		(princ "[") (write-term (car term)) (princ "],"))
	(terpri))

;  (when (rose-eqn-terms f)
;	(princ leader) (princ ">> EQN subs: ") 
;	(dolist (term (rose-eqn-terms f))
;		(princ "[") (write-term (car term)) (princ "],"))
;	(terpri))

  (princ leader) (terpri)
  )
  
(defun prtree () (print-distree $distree))


