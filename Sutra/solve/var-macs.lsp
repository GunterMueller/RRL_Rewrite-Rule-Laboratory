(in-package "RRL")
;; These are the global variables used in this file.

(defvar *rule-list*    nil  "The list of rules in the system")
(defvar *max-depth*     15  "The maximum depth for IDFS")
(defvar *prv-depth*      0  "Gives the previous depth solved")
(defvar *cur-depth*      0  "Gives current depth of exploration")
(defvar *increment*      4  "Used to INCREMENT depth bound for IDFS")

(defvar *reachable*    nil  "List of symbols reachable from each symbol")
(defvar *list-of-vars* nil  "List of variables present in the eqn")
(defvar *all-lhs-ops*  nil  "All the lhs operators for rules")
(defvar *all-ops*      nil  "List of all operators in the rule set")
(defvar *debug*        nil  "Gives the level of debug to be used ")
(defvar *repeat*       nil  "Global var for stopping closure")

(defvar *time-debug*   nil  "List with time debug constants")
(defvar *run-time*       0  "Used to get the time for one solution")
(defvar *time*           0  "Number used to generate *time-debug*")

(defvar *MAX-LIM*       50  "If search doesn't stop then ask-user")

(defvar *s-conditional*  t  "Set to T if system is CONDITIONAL")

(defvar *unwanted*     nil  "Rules not used for restructuring")

(defvar *eager-rewrite*  t  "Whether Eager Rew. should be used")

(defmacro operator (term) `(car ,term))
(defmacro arguments (term) `(cdr ,term))
(defmacro constant? (term) `(null (cdr ,term)))


(defmacro make-eqn  (s t1)
;; This macro takes the two terms and makes an equation
;; out of them, with the following meaning :-
;;    1.. S      The lhs term.
;;    2.. T1     The rhs term.
    `(list ,s ,t1))

(defmacro s-get-eqn-lhs (eqn)
    `(nthelem 1 ,eqn))

(defmacro s-get-eqn-rhs (eqn)
    `(nthelem 2 ,eqn))

(defmacro make-node (depth lst ans)
;; This macro takes the individual components and makes
;; a node out of it. The node has the following :-
;;    1.. depth  For IDFS.
;;    2.. LST    Is a list as defined by the macro 
;;               MAKE-EQN-LST.
;;    3.. ANS    A list of current substitutions.
    `(list ,depth ,lst ,ans))

(defmacro s-get-depth (node)
;; This macro returns the depth of a node.
    `(car ,node))

(defmacro s-get-elist (node)
    `(nthelem 2 ,node))

(defmacro s-get-ans (node)
    `(nthelem 3 ,node))

(defmacro make-eqn-lst (List1 Eqn List2)
;; This macro makes a list such that the first element of it has
;; all the equations with a larger depth, the second is such that
;; it has a smaller depth, and also is the next equation to be
;; expanded for successors. The last part contains the other eqns
;; with smaller depth.
    `(list ,List1 ,Eqn ,List2))

(defmacro s-get-list1 (e-list)
;; Gets the first list out of a list of equations.
    `(nthelem 1 ,e-list))

(defmacro s-get-curr (e-list)
    `(nthelem 2 ,e-list))

(defmacro s-get-list2 (e-list)
    `(nthelem 3 ,e-list))



(defmacro get-first-eqs (e-ans-lst)
;; When SUCCESSORS function is called, it returns a list of pairs,
;; such that for each pair, the first component is the set of new
;; equations, while the second is the new ANS. This function extracts
;; the first such list of equations from E-ANS-LST.
    `(caar ,e-ans-lst))

(defmacro get-first-ans (e-ans-lst)
;; As above, but gets the first ANS.
    `(cdar ,e-ans-lst))


(defmacro compile-information()
;; This function is called to begin with to look at all the available
;; rules to build up some data structures which can be used later to
;; eliminate infeasible paths.
    `(compile-all-rules))

;; *************************************************************** ;;
;;  Functions about rules have been taken from RRL.
;; *************************************************************** ;;
(defmacro get-rule-lhs (rule)
    `(lhs ,rule))
(defmacro get-rule-rhs (rule)
    `(rhs ,rule))
(defmacro get-rule-cond (rule)
    `(ctx ,rule))
;; *************************************************************** ;;

(defmacro s-get-binding (t1 a-list)
;; This macro gets a binding for "t" from the association list.
    `(cdr (assoc ,t1 ,a-list)))

(defmacro s-add-binding (lhs rhs a-list)
;; This macro adds the pair (lhs . rhs) as the first element of "a-list"
    `(cons (cons ,lhs ,rhs) ,a-list))

(defmacro s-new-var()
    `(gensym))

(defmacro get-rest-succ (lst)
    `(cdr ,lst))

(defmacro s-all-null (lst)
;; This macro marks the stopping condition for recursive
;; calls.
    `(and (null (s-get-list1 ,lst))
          (null (s-get-curr ,lst))
          (null (s-get-list2 ,lst))))

(defmacro s-null-curr (lst)
    `(null (s-get-curr ,lst)))

(defmacro forced-unify (t1 t2 binds) `(nonac-unify ,t1 ,t2 , binds))




;; ***************************************************************** ;;
;; A SET OF USEFUL FUNCTIONS
;; ***************************************************************** ;;

(defun s-get-rest (lst)
;; This function takes as input a list of three parts :-
;;   LIST1, EQN, LIST2.
;; The function makes another list removing EQN from the
;; previous one, with the following restriction :-
;;   If LIST2 = NIL, then make LIST2 = LIST1 & LIST1 = NIL.
;;   EQN = (CAR LIST2).
;;   LIST2 = (CDR LIST2).
    (let  ((lst1 (s-new-list1 lst))
           (lst2 (s-new-list2 lst)))
       (make-eqn-lst lst1 (car lst2) (cdr lst2))))


(defun s-new-list1 (lst)
    (let  ((lst1 (s-get-list1 lst))
           (lst2 (s-get-list2 lst)))
       (if lst2
           lst1
           nil)))


(defun s-new-list2 (lst)
    (let  ((lst1 (s-get-list1 lst))
           (lst2 (s-get-list2 lst)))
       (if lst2
           lst2
           lst1)))


(defun s-a-lists1 (e-lst lst)
;; This function forms a new equation list after incorporating
;; E-LST into the original list LST.
    (let* ((lst1  (s-get-list1 lst))
           (eqn   (s-get-curr  lst))
           (lst2  (s-get-list2 lst))
           (llst  (make-eqn-lst (append e-lst lst1) eqn lst2)))
       (if (s-null-curr llst)
           (s-get-rest llst)
           llst)))

(defun interpret (lst)
;; If all the successors returned NIL, then IDFS at a node
;; should  also return NIL. Else, if  there is atleast one
;; CONT  (depth  bound  exceeded) then  IDFS should return 
;; CONT, else it should return FAIL.
    (cond 
          ((member 'cont lst) 'cont)
          ((member 'fail lst) 'fail)
          (t                 nil)))

(defun is-unreachable (lhs rhs)
    (cond  ((or (var? lhs) (var? rhs)) nil)
           ((equal (operator lhs) (operator rhs)) nil)
           ( t (not (member (op-of rhs) (assoc (op-of lhs) *reachable*))))))

(defun s-append-list (var term lst1 lst2)
;; This function unifies the two substitutions LST1 and LST2.
;; If the operation is successful, the function the makes a
;; binding for VAR and TERM.
    (let   ((lst   (append-list  lst1  lst2)))
      (cond ((null  lst) nil)
            ((equal lst '(nil))
                 (s-add-binding  var  term  nil))
            ((equal var term) lst)
            ( t  (s-add-binding  var  term  lst)))))

(defun append-list (lst1 lst2)
;; This function checks the length of the two lists, and
;; then calls APPND-LISTS.
    (if (> (length lst1) (length lst2))
        (appnd-lists lst2  lst1)
        (appnd-lists lst1  lst2) ) )

(defun appnd-lists(lst1 lst2)
;; This function is used to append two lists of substitutions,
;; LST1  and LST2. The criterion here is to check whether the
;; same variable has a binding in both, and if so, the values
;; in the two substitutions must be unifiable, else the net
;; substitution is invalid.
    (cond  ((and (null lst1) (null lst2))
              (list nil))
           ((null lst1) lst2)
           ( t (let ((bind1  (s-get-binding (caar lst1) lst2))
                     (rest   (appnd-lists (cdr  lst1) lst2)))
                 (if bind1
                     (let  ((unifier  (nonac-unify (cdar lst1)
                                                    bind1)))
                        (cond ((equal unifier '(nil))
                                   rest)
                              ((null unifier) nil)
                              ( t (appnd-lists unifier rest))))
                     (cons (car lst1) rest))))))



(defun same-oper? (lhs rhs)
    (cond ((and (var? lhs) (var? rhs))
              (eq lhs rhs))
          ((or  (var? lhs) (var? rhs)) nil)
          ( t  (same-op? lhs rhs))))


