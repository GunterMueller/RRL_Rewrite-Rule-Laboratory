(in-package "USER")

(defmacro make-eqn (lhs rhs ctx source &optional info)
  (let ((e (gensym)))
    (if info
	`(let ((,e (make-ax)))
	   (setf (ax-lhs ,e) ,lhs)
	   (setf (ax-rhs ,e) ,rhs)
	   (setf (ax-ctx ,e) ,ctx)
	   (setf (ax-lvars ,e) 1)
	   (setf (ax-rvars ,e) 1)
	   (setf (ax-eqn-info ,e) (make-einfo))
	   (setf (eqn-source ,e) ,source)
	   (setf (eqn-info ,e) ,info)
	   ,e)
      `(let ((,e (make-ax)))
	 (setf (ax-lhs ,e) ,lhs)
	 (setf (ax-rhs ,e) ,rhs)
	 (setf (ax-ctx ,e) ,ctx)
	 (setf (ax-lvars ,e) 1)
	 (setf (ax-rvars ,e) 1)
	 (setf (ax-eqn-info ,e) (make-einfo))
	 (setf (eqn-source ,e) ,source)
	 (setf (eqn-info ,e) $superposed-sub)
	 ,e)
      )))

(defmacro is-eqn (eqn) `(typed ,eqn 'ax))
(defmacro lhs (eqn) `(ax-lhs ,eqn))
(defmacro rhs (eqn) `(ax-rhs ,eqn))
(defmacro ctx (eqn) `(if $condi (ax-ctx ,eqn)))
(defmacro abs-ctx (eqn) `(ax-ctx ,eqn))
(defmacro order-condition (eqn) `(abs-ctx ,eqn))
(defmacro is-condi-eqn (eqn) `(ctx ,eqn))
(defmacro eqn-rule-info (eqn) `(einfo-rule-info (ax-eqn-info ,eqn)))
(defmacro eqn-info (eqn) `(einfo-info (ax-eqn-info ,eqn)))

;;; Info related to distree nets.
(defmacro rule-rose (rule) `(einfo-rule-rose (ax-eqn-info ,rule)))
(defmacro rule-lhs-roses (rule) `(einfo-lhs-roses (ax-eqn-info ,rule)))
(defmacro rule-rhs-roses (rule) `(einfo-rhs-roses (ax-eqn-info ,rule)))
(defmacro eqn-pointers (eqn) `(rule-rose ,eqn))

;; Info related to the source of equations.
(defmacro eqn-source (eqn) `(einfo-source (ax-eqn-info ,eqn)))
(defmacro eqn-source-type (eqn) `(car (eqn-source ,eqn)))
(defmacro is-source-type (eqn type) `(equal ,type (eqn-source-type ,eqn)))
(defmacro change-source (eqn so) `(setf (eqn-source ,eqn) ,so))

(defmacro eqn-used-rules (eqn) `(einfo-used-rules (ax-eqn-info ,eqn)))
(defmacro remember-used-rule-num (num) 
  `(if $trace-proof (query-insert ,num $used-rule-nums)))
(defmacro update-used-rules (eqn) 
  `(if $trace-proof
       (setf (eqn-used-rules ,eqn) (append (eqn-used-rules ,eqn) $used-rule-nums)
	     $used-rule-nums nil)))

(defmacro change-lhs (eqn lhs) `(progn (setf (lhs ,eqn) ,lhs) ,eqn))
(defmacro change-rhs (eqn rhs) `(progn (setf (rhs ,eqn) ,rhs) ,eqn))
(defmacro change-ctx (eqn ctx) `(progn (setf (abs-ctx ,eqn) ,ctx) ,eqn))
(defmacro change-lhs-rhs (eqn lhs rhs) 
  `(progn (psetf (lhs ,eqn) ,lhs
		 (rhs ,eqn) ,rhs)
	  ,eqn))
(defmacro change-lhs-rhs-ctx (eqn lhs rhs ctx)
  `(progn (psetf (lhs ,eqn) ,lhs
		 (rhs ,eqn) ,rhs
		 (abs-ctx ,eqn) ,ctx)
	  ,eqn))
(defmacro exchange-lr (eqn) 
  `(progn (psetf (lhs ,eqn) (rhs ,eqn)
		 (rhs ,eqn) (lhs ,eqn))
	  (psetf (ax-lvars ,eqn) (ax-rvars ,eqn)
		 (ax-rvars ,eqn) (ax-lvars ,eqn))
	  ,eqn))

(defmacro is-prop-eqn (eqn)
  `(and (nonvarp (lhs ,eqn)) (nonvarp (rhs ,eqn))
	(predicatep (op-of (lhs ,eqn)))
	(or (neq (op-of (lhs ,eqn)) *=*) 
	    (and (not (truep (rhs ,eqn)))
		 (not (falsep (rhs ,eqn)))))))

(defmacro ass2eqn (ass source &optional first) 
   `(make-eqn ,ass nil nil ,source ,first))
(defmacro eqn2ass (eqn) `(list *eq* (lhs ,eqn) (rhs ,eqn)))
(defmacro is-assertion (eqn) `(truep (rhs ,eqn)))
(defmacro assertionp (eqn) `(or (is-assertion ,eqn) (is-prop-eqn ,eqn)))
(defmacro is-oneway (eqn) 
  `(or (eq (eqn-info ,eqn) 'oneway) (is-source-type ,eqn 'def)))
(defmacro is-input-ass (eqn) `(member (eqn-info ,eqn) '(oneway input)))
(defmacro set-input-ass (eqn) `(setf (eqn-info ,eqn) 'input))

;; operations performed on (ax-lvars ax):
(defmacro set-lhs-vars (eqn vars) `(setf (ax-lvars ,eqn) ,vars))
(defmacro ref-lhs-vars (rule) `(ax-lvars ,rule))
(defmacro get-lhs-vars (eqn)
  `(if (equal (ax-lvars ,eqn) 1)
      (setf (ax-lvars ,eqn) (var-list (lhs ,eqn)))
      (ax-lvars ,eqn)))
(defmacro has-lhs-vars (eqn) `(not (member (ax-lvars ,eqn) '(nil 1))))

;; operations performed on (ax-lvars ax):
(defmacro set-rhs-vars (eqn vars) `(setf (ax-rvars ,eqn) ,vars))
(defmacro get-rhs-vars (eqn)
  `(if (equal (ax-rvars ,eqn) 1)
      (setf (ax-rvars ,eqn) (var-list (rhs ,eqn)))
      (ax-rvars ,eqn)))
(defmacro has-rhs-vars (eqn) `(not (member (ax-rvars ,eqn) '(nil 1))))
;; if (ax) is a rule and $ac is nonempty, then (ax-rvars) contains 
;; info about symmetry terms and top-only-vars of lhs.
(defmacro ref-symmetry-vars (rule) `(car (ax-rvars ,rule)))
(defmacro ref-symmetry-terms (rule) `(cadr (ax-rvars ,rule)))
(defmacro ref-top-vars (rule) `(caddr (ax-rvars ,rule)))

;; operations performed on (ax-cvars ax):
(defmacro set-ctx-vars (eqn vars) `(setf (ax-cvars ,eqn) ,vars))
(defmacro get-ctx-vars (eqn) `(ax-cvars ,eqn))
(defmacro set-linear-flag (eqn flag) `(setf (ax-cvars ,eqn) ,flag))
(defmacro is-linear-rule (eqn) `(ax-cvars ,eqn))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Rewrite rules.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro make-rule (eqn number size type)
  `(let ((rinfo (if (rinfo-p (eqn-rule-info ,eqn))
		    (eqn-rule-info ,eqn)
		  (make-rinfo))))
     (setf (rinfo-ruleno rinfo) ,number)
     (setf (rinfo-size rinfo) ,size)
     (setf (rinfo-type rinfo) ,type)
     (if (eqn-rule-info ,eqn)
	 (setf (rinfo-picked (eqn-rule-info ,eqn)) nil)
       (setf (eqn-rule-info ,eqn) rinfo))
     (if $ac (setf (ax-rvars ,eqn) (list nil nil nil)))
     ,eqn))

(defmacro pred-rulep (rule) `(predicatep (op-of (lhs ,rule))))
(defmacro is-condi-rule (rule) `(ctx ,rule))
(defmacro rule-source (rule)  `(eqn-source ,rule))
(defmacro lhsize (rule)  `(rinfo-size (eqn-rule-info ,rule)))
(defmacro pairswith (rule) `(rinfo-pair-with (eqn-rule-info ,rule)))
(defmacro ruleno (rule) `(rinfo-ruleno (eqn-rule-info ,rule)))
(defmacro ref-y-rule (rule) `(ax-y-rule ,rule))

;; operations performed on (eqn-rinfo-picked rule)
(defmacro set-crit-mark (rule)
  `(progn (setf (rinfo-picked (eqn-rule-info ,rule)) 'm) ,rule))
(defmacro crit-unmarked (rule) 
  `(null (rinfo-picked (eqn-rule-info ,rule))))
(defmacro set-deleted-mark (rule) 
  `(setf (rinfo-picked (eqn-rule-info ,rule)) 'd))
(defmacro is-deleted-rule (rule) 
  `(eql 'd (rinfo-picked (eqn-rule-info ,rule))))

;; operations performed on (ax-cvars ax):
(defmacro ref-condi-vars (rule) `(ax-cvars ,rule))
(defmacro set-condi-vars (rule stuff) 
  `(setf (ref-condi-vars ,rule) ,stuff))

(defmacro set-reduction-type (rule type) 
  `(setf (rinfo-type (eqn-rule-info ,rule)) ,type))
(defmacro is-reduction (rule) 
  `(= (rinfo-type (eqn-rule-info ,rule)) 1))
(defmacro is-condi-reduction (rule) 
  `(= (rinfo-type (eqn-rule-info ,rule)) 3))
(defmacro is-dummy-rule (rule) 
  `(> (rinfo-type (eqn-rule-info ,rule)) 4))

(defmacro is-general-rule (rule) `(ref-lhs-vars ,rule))
(defmacro is-ground-rule (rule) `(null (is-general-rule ,rule)))
(defmacro ref-rule-vars (rule)
  `(if (is-reduction ,rule) (get-lhs-vars ,rule)
     (append (ref-lhs-vars ,rule)  
	     (ref-condi-vars ,rule))))
(defmacro rules-with-op (op op-list) `(cdr (assq ,op ,op-list)))
(defmacro get-rules-with-op (op op-rules)
  `(cdr (assq ,op
	      (if* ,op-rules
		  then ,op-rules
		  else $op-rules))))

(defmacro unitp (rule)
   `(if $fopc 
	(if* $condi then (not (ctx ,rule))
	    elseif (predicatep (op-of (lhs ,rule)))
	    then (not (memq (op-of (lhs ,rule)) *xor*and*))
	    else t)
	t))

(setq $rule-x-to-y (make-ax :lvars 1))
(defmacro rename-x-to-y-list (list) `(mapcar 'rename-x-to-y ,list))

(defun rule-x-to-y (old &aux rule)
  (cond 
   ((is-ground-rule old) old)
   ((ref-y-rule old))
   (t (setq rule (if $save-y-rule (make-ax) $rule-x-to-y))
      (setf (lhs rule) (rename-x-to-y (lhs old)))
      (setf (rhs rule) (rename-x-to-y (rhs old)))
      (if (ctx old) 
	  (setf (abs-ctx rule) (rename-x-to-y (ctx old)))
	(setf (abs-ctx rule) (abs-ctx old)))
;      (when $guha 
;	  (setf (abs-ctx rule)
;		(sloop for tri in (abs-ctx old)
;		       collect (sloop for xyz in tri 
;				      collect (rename-x-to-y xyz)))))
      (when $save-y-rule
	    (set-lhs-vars rule (rename-x-to-y-list (ref-lhs-vars old)))
	    (set-rhs-vars rule (if $ac (list nil nil nil)))
	    (adjust-cvars rule old)
	    (setf (ref-y-rule old) rule)
	    )
      (setf (ax-eqn-info rule) (ax-eqn-info old))
      rule)
   ))

(defun eqn-subsumed (eqn eqns)
  ;; Return t iff one of equation in "eqns" subsumes "eqn".
  (sloop with lhs = (lhs eqn)
	 for e in eqns 
	 thereis (and (pure-match (lhs e) lhs)
		      (pure-match (rhs e) (rhs eqn)))))


(defun adjust-cvars (rule old)
  (if (listp (ref-condi-vars old))
      (set-condi-vars rule (rename-x-to-y-list (ref-condi-vars old))))

  (when $ac 
	(when (ref-symmetry-vars old)
	      (setf (ref-symmetry-vars rule)
		    (sloop for l in (ref-symmetry-vars old)
			   collect (rename-x-to-y-list l)))
	      (setf (ref-symmetry-terms rule)
		    (sloop for l in (ref-symmetry-terms old)
			   collect (rename-x-to-y-list l))))
	(if (ref-top-vars old)
	    (setf (ref-top-vars rule) 
		  (rename-x-to-y-list (ref-top-vars old)))))
  )

(defun lhsize-lessp (r1 r2) (< (lhsize r1) (lhsize r2)))

(defun r2e (eqn) 
  (setf (einfo-rule-info eqn) nil)
  eqn)

(defun similar-eqn (e1 e2)
  ; return t iff "e1" and "e2" are the same after renmaing the variables.
  (similar-term (list *=* (lhs e1) (rhs e1)) (list *=* (lhs e2) (rhs e2))))

(defun similar-term (t1 t2)
  ; return t iff "t1" and "t2" are the same after renmaing the variables.
  (and (applies t1 t2) (applies t2 t1)))

(defun eqn-is-too-big (eqn &aux (lhs-size 0))
  ;; return t iff eqn is too big.
  (cond
   ((member (car (eqn-source eqn)) '(user sos)) nil)

   ((and $instant-seeds (falsep (rhs eqn)) (eq (op-of (lhs eqn)) *=*))
    (if (setq lhs-size (all-ground3-terms (lhs eqn)))
	(add-shorthand-ops lhs-size)
      (when (> (w-size (lhs eqn)) $discard-eqn-max-size)
	    (trace-message 4 "  Discard a big equation: " (write-eqn eqn))
	    (setq $used-rule-nums nil)
	    (setq $discarded t)
	    )))

   ((or (if (not $polynomial)
	    (or (> (progn (setq lhs-size (w-size (lhs eqn)))) $discard-eqn-max-size)
		(> (w-size (rhs eqn)) $discard-eqn-max-size)))
	(if (> $discard-eqn-max-depth 0)
	    (> (depth (lhs eqn)) $discard-eqn-max-depth))
	(and $polynomial 
	     $check-homogenous
	     (> (eqn-product-degree eqn) $discard-eqn-max-degree))
	)
    (if* (and (> lhs-size $discard-eqn-max-size)
	     (< lhs-size $discard-eqn-2max-size))
;	 then (mark "lhs-size" lhs-size)
	 (push eqn $post-set)
;	else
	(setq $discarded t))
    (trace-message 4 "  Discard a big equation: " (write-eqn eqn))
    (setq $used-rule-nums nil)
    t)
   ))

(defun add-shorthand-ops (terms)
  (sloop with new 
	 for term in terms 
	 if ; (and  (not (member (op-of (first-arg term)) $newops))
		 (not (member (op-of (second-arg term)) $newops))
		 ;)
	 do
	 (setq new (new-term nil nil t))
	 (if (or (member (op-of (first-arg term)) $newops)
		 (member (op-of (second-arg term)) $newops))
	     (push (op-of new) $skolem-ops))

	 (setq new (make-eqn term new nil (list 'def (incf $nusereqn))))
	 (push new $eqn-set)
	 (trace-message 2 "Introduce a new operator: " (write-eqn new))
	 )
  (if (eq $kb '*distree*) (re-init-distree))
  ;(reset-kb '*newop*)
  t
  )

#|
(defvar $fix-point-prob nil)
(defconstant *junk* (list *=* *false* *true*))
(defun eqn-is-fix-pointable (eqn)
  (or (not $fix-point-prob)
      (member (car (eqn-source eqn)) '(user sos deleted))
      (memq (op-of (lhs eqn)) *junk*)
      (variablep (first-arg (lhs eqn)))
      (variablep (first-arg (rhs eqn)))
      ))
|#

(defun eqn-product-degree (eqn)
  (let ((d (product-degree (lhs eqn))))
    (if (eq d 0)
	(product-degree (rhs eqn))
	d)))

(defun product-degree (term)
  (cond 
    ((variablep term) 1)
    ((eq (op-of term) *0*) 0)
    ((eq (op-of term) *-*) (product-degree (first-arg term)))
    ((eq (op-of term) *+*) 
     (apply #'max (mapcar #'product-degree (args-of term))))
    ((eq (op-of term) $*$)
     (sloop with sum = 0
	    for xa in (args-of term) 
	    for xb = (product-degree xa) do
	    (if (eq xb 0) (return 0))
	    (setq sum (+ sum xb))
	    finally (return sum)))
    (t 1)))

(defun print-ax (ax &optional out-stream print-level)
   (terpri) 
   (princ "AX:    lhs : ") (princ (ax-lhs ax)) (terpri)
   (princ "       rhs : ") (princ (ax-rhs ax)) (terpri)
   (when (ax-ctx ax) (princ "       ctx : ") (princ (ax-ctx ax)) (terpri))
   (princ "     lvars : ") (princ (ax-lvars ax)) 
   (princ ",  rvars : ") (princ (ax-rvars ax)) 
   (princ ",  cvars : ") (princ (ax-cvars ax)) (terpri)
   (when (typep (ax-eqn-info ax) 'einfo)
	 (princ "    source : ") (princ (eqn-source ax)) 
	 (princ ", used-rules : ") (princ (eqn-used-rules ax)) 
	 (princ ", info : ") (princ (eqn-info ax)) (terpri)
	 ;; (princ "pointers : ") (princ (eqn-pointers ax)) (terpri)
	 (princ " rule-info : ")
	 (princ (eqn-rule-info ax)) 
	 (terpri))
   (princ "    y-rule : ") (print-y-rule (ax-y-rule ax))
   (and out-stream print-level)
   )

(defun print-y-rule (ax)
   (if* (typep ax 'ax) then
	(terpri)
	(princ "      lhs : ") (princ (ax-lhs ax)) (terpri)
	(princ "      rhs : ") (princ (ax-rhs ax)) (terpri)
	(when (ax-ctx ax) (princ "      ctx : ") (princ (ax-ctx ax)) (terpri))
	(princ "     lvars : ") (princ (ax-lvars ax)) 
	(princ ",  rvars : ") (princ (ax-rvars ax)) 
	(princ ",  cvars : ") (princ (ax-cvars ax)) 
	else
	(princ ax))
   (terpri))

