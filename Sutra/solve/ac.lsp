
(in-package "RRL")
;; This file has all the functions related to the equation
;; solver for completely defined AC functions.

(defmacro s-make-n-rule (rule)
  `(make-new-rule (lhs ,rule) (rhs ,rule)
                  (ctx ,rule) (rule-source ,rule)))


(defun s-ac-restr (eqn  ans)
;; This function is called whenever a left hand side with
;; an AC operator at the top.
  (let* ((lhs-e    (s-get-eqn-lhs   eqn))
         (rhs-e    (s-get-eqn-rhs   eqn))
         (oper     (operator        lhs-e))
         (temp     (del-non-two-arg 
                      (delete-unwanted (get-rules-with-op oper nil)))))
    (do* ((lst     temp      (cdr lst))
          (n-rule  (s-make-n-rule (car lst)) (s-make-n-rule (car lst)))
          (soln    (one-ac-restr eqn ans n-rule)
                   (append   (one-ac-restr eqn ans n-rule)  soln)))
         ((null (cdr lst)) soln))))


(defun del-non-two-arg (r-lst)
;; This function is used to remove all the AC rules which have
;; more than two arguments in R-LST.
    (do*  ((lst   r-lst   (cdr lst))
           (nlst  nil))
          ((null lst) nlst)
          (if (number-of-args (car lst) 2)
              (setq nlst (cons (car lst) nlst)))))

(defun number-of-args (rule num)
;; Returns TRUE if the number of arguments on LHS of
;; RULE equals NUM, else returns NIL.
  (let* ((args   (arguments   (flat-term (get-rule-lhs  rule)))))
     (=  (length args) num)))


(defun one-ac-restr (eqn  ans  rule)
;; This function is used to restructure EQN using RULE.
;; ANS is the partial answer obtained upto this point,
;; and is used to get the new set of equations.
  (let  ((one    (one-ac-restr1  eqn ans rule 1 2))
         (two    (one-ac-restr1  eqn ans rule 2 1)))
    (cond ((and one two) (list one two))
          ( one          (list one))
          ( two          (list two)))))


(defun one-ac-restr1 (eqn ans rule n1 n2)
;; This is the main function for AC-restructuring. This
;; function  takes EQN and restructures  it using a two
;; argument AC  rule,  treating the  arguments  in  the 
;; order N1, N2, which is a permutation of (1,2).
  (if (number-of-args-e eqn 2)
      (one-ac-restr1-2 eqn ans rule n1 n2)
      (let*  ((r-lhs    (get-rule-lhs  rule))
              (r-rhs    (get-rule-rhs  rule))
              (cond1    (get-rule-cond rule))
              (l1       (nthelem  n1   (arguments r-lhs)))
              (l2       (nthelem  n2   (arguments r-lhs)))
              (e-lhs    (s-get-eqn-lhs eqn))
              (e-rhs    (s-get-eqn-rhs eqn))
              (oper     (operator  e-lhs))
              (s1       (car   (arguments  e-lhs)))
              (s-rest   (make-term oper  (cdr (arguments e-lhs))))
              (eqn-rest (make-eqn     s-rest l2))
              (temp1    (try-forces   s1 l1 ans)))
          (if temp1 
              (let*  ((eqns1   (car  temp1))
                      (ans1    (cdr  temp1))
                      (temp2  (try-forces  r-rhs  e-rhs  ans1)))
                (if temp2
                    (let*  ((eqns2   (car   temp2))
                            (ans2    (cdr   temp2))
                            (eqn-cnd (make-cond-eqn  cond1))
                            (all-eqn (cons eqn-rest 
                                           (append  eqns1 eqns2 eqn-cnd))))
                        (cons all-eqn ans2))))))) )

(defun number-of-args-e (eqn n)
  (let  ((args  (arguments  (s-get-eqn-lhs  eqn))))
    (= (length args) n)))

(defun one-ac-restr1-2 (eqn ans rule n1 n2)
;; This function is called when the eqn has exactly two
;; subterms in its lhs.
  (let*  ((r-lhs    (get-rule-lhs  rule))
          (r-rhs    (get-rule-rhs  rule))
          (cond1    (get-rule-cond rule))
          (e-lhs    (s-get-eqn-lhs eqn))
          (e-rhs    (s-get-eqn-rhs eqn))
          (l1       (nthelem  n1   (arguments r-lhs)))
          (l2       (nthelem  n2   (arguments r-lhs)))
          (oper     (operator  e-lhs))
          (n-rule   (make-term oper (list l1 l2)))
          (temp     (one-rule-res   e-lhs  n-rule  ans  cond1)))
    (if temp
       (let*  ((eqns1  (car  temp))
               (ans1   (cdr  temp))
               (temp1  (try-forces r-rhs e-rhs ans1)))
          (if temp1
             (let  ((eqns2  (car  temp1))
                    (ans2   (cdr  temp1)))
               (cons  (append  eqns1  eqns2) ans2))))) ) )


(defun make-cond-eqn (condition)
;; This function returns a list of the equation CONDITION --?--> TRUE,
;; if there is a condition, else returns NIL.
  (if condition
      (list  (make-eqn  condition  '(true)))))
