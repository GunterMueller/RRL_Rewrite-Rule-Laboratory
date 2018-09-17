(in-package "RRL")
;; This file contains all the functions that are used to
;; compile a set of rules such that the operator reachability
;; graph is set up.

;; There are also functions which reinstates proper terminal
;; values to all the global variables at the end of execution.

;; only reachabiity may need to be compiled.

 
(defun compile-all-rules ()
    (init-all-globals)
    (set-conditional)
    (compile-rules $op_rules)
    (setq *reachable* (closure *reachable* nil)) )
 

(defun init-all-globals()
    (setq *reachable*   nil
          *all-lhs-ops* nil
          *all-ops*     nil
    )
)

(defun set-conditional ()
;; Sets the variable *S-CONDITIONAL* to TRUE if the system has
;; any conditional rule, else sets it to FALSE.
    (setq *s-conditional*
          (loop for rule in $rule-set
                if (ctx rule) do (return t)
                finally (return nil) ) ) )


(defun push-lhs-op (op)
   (if (member op *all-lhs-ops*) t (push op *all-lhs-ops*)))



(defun print-ops (op_rules)
   (cond ((null op_rules) ())
          (t  (print-op (car op_rules))
              (terpri)
              (print-ops (cdr op_rules)))))

(defun print-op (ops)
   (princ "Operator : ")
   (print (car ops))
   (princ " has ")
   (terpri)
   (show-rules (cdr ops)))

(defun get-operator (term)
    (if (var? term) nil
        (operator term)))


;; This file has some of the functions used in the compilation
;; stage. (i.e. functions related to setup of the reachability
;; graph etc).



(defun get-rhs-operator(rule)
  (get-operator (rhs rule)))

(defun compile-rules(op-rules)
;; This function has to be given a data structure like OP_RULES
;; as  defined by  INITIALIZE.LSP in  RRL. It goes over all the 
;; rules in this data structure to find the operator graph  for
;; the set of rules.
    (do*   ((lst     op-rules        (cdr lst))
            (one     (car lst)       (car lst))
            (oper    (car one)       (car one))
            (rules   (cdr one)       (cdr one))
            (o-lst   (mapcar 'get-rhs-operator rules)
                     (mapcar 'get-rhs-operator rules) ))
           ((null lst))
           (push-lhs-op oper)
           (push-ops    (cons oper o-lst))
           (push (cons oper o-lst) *reachable*)))


(defun push-ops (o-lst)
;; Stores all the operator names in the list *ALL-OPS*.
    (loop for ops in o-lst do
        (if (not (member ops *all-ops*))
            (push ops *all-ops*))))


;; **************************************************************** ;;
;; **************************************************************** ;;
;; This part of  the file contains functions that are used to
;; find the closure of the reachability graph (i.e. if f -> g,
;; and g -> h then  we must  have f -> h  in the reachability 
;; matrix  too). If  there is any  variable that is reachable
;; from a  particular operator,  then all other operators can
;; be reached from it.
;; **************************************************************** ;;
;; **************************************************************** ;;


(defun closure (a-lst temp)
    (setq  *repeat*  nil)
    (do*  ((lst   a-lst     (cdr lst))
           (pair  (car lst) (car lst))
           (npair (obtain-new-pair pair a-lst *repeat*)
                  (obtain-new-pair pair a-lst *repeat*))
           (ttt))
          ((null lst) (if *repeat* (closure ttt  nil) ttt  ))
          (setq ttt (cons npair ttt))))


(defun obtain-new-pair (pair lst stop)
;; This function  goes over all the operators that are
;; currently reachable from a particular operator, and
;; checks whether  new operators can be reached in one
;; more step.
    (let* ((oper   (car pair))
           (bind   (cdr pair))
           (nlst   (get-all-binds bind lst)))
        (do* ((oplst  nlst        (cdr oplst))
              (ops    (car oplst) (car oplst)))
             ((null oplst) (cons oper bind))
             (if (not (member ops bind))
                 (progn (push ops bind)
                        (setq *repeat* t))))))



(defun get-all-binds (oplst a-lst)
;; This function returns a list of all the operators
;; reachable in one step from the operators in OPLST.
    (cond ((null oplst) nil)
          ( t    (append (get-one-bind  (car oplst) a-lst)
                         (get-all-binds (cdr oplst) a-lst)))))


(defun get-one-bind  (oper a-lst)
;; As above, but for one operator.
    (cond ((null oper) *all-ops*) ; When a variable is reachable.
          ( t (s-get-binding oper a-lst))))




