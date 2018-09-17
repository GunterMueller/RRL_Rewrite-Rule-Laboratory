(in-package "USER")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFCONSTANTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconstant piport (make-synonym-stream '*standard-input*))
(defconstant poport (make-synonym-stream '*standard-output*))

(defconstant *herky-banner* '(
"****************************************************************************"
"****                                                                    ****"
"****         WELCOME  TO  HERKY (0.3) ----- A Descendent of RRL         ****"
;"****      WELCOME  TO  RRL (3.0) ----- A Rewrite Rule Laboratory        ****"
"****                                                                    ****"
;"****         A High-Performance Rewriting/Completion Laboratory         ****"
;"****               written by Hantao Zhang, 1989 -- 1991.               ****"
;"****                                                                    ****"
"****************************************************************************"
))

(defconstant *help-herky* 
'(
"Currently you can do the following:"
""
"  Add     - Input equations from the terminal."
;"  Akb     - Run the automatic Knuth-Bendix completion procedure."
"  Auto    - Automatically execute a sequence of commands in a cmd file."
"  Break   - Talk to lisp directly."
"  Cmd     - Registry all the commands in a file (to be used by auto)."
;"  Close   - Close the file opened by Cmd (the default is herky.cmd)."
"  Delete  - Delete a list of equations or rules of HERKY."
"  Gc      - Garbage collection."
"  Grammer - Display the input grammer of HERKY."
;"  Hiper   - Run HIPER from HERKY."
"  Init    - Initialize HERKY."
"  Kb      - Run the Knuth-Bendix completion procedure."
"  List    - List equations and rules in current system."
;"  Load    - Load a system saved in a file by the save command."
"  Makerule- Orient equations into rewrite rules without superposition."
"  Option  - Set HERKY flags and parameters."
"  Operator- Set properties of operators (precedence, constructors, etc.)."
"  Prove   - Prove an equation by rewriting or by induction."
"  Quit    - Quit HERKY."
"  Read    - Input equations from a file."
"  Refute  - Read a set of equations and negate the last one for refutation."
"  Runbg   - Run a set of commands from a file in the background."
;"  Save    - Save the current status of HERKY into a file."
"  Stats   - List the current statistics of HERKY."
"  Test    - Test HERKY by a sequence of examples."
"  Write   - Write equations and/or rules to a file."
"  Help    - Print this message."
""
"Note: You do not need to type whole command, a substring will suffice except"
"      that the first letter must be given. If what you type matches more than"
"      one command, the first one is chosen. For example, when you give 'o' or"
"      'or', HERKY takes it for 'operator'. When you give 'od', HERKY takes it"
"      for 'order'. Arguments to commands may be typed on the same line."
"      There is no distinction between uppercase and lowercase characters."
))

(defconstant *help-grammar*
  ;; Put a description of the new grammar on the screen.
  '(
   "                     HERKY'S    INPUT    SYNTAX "
   " "
;   " <arity> ::= [<op> : <type>, <type>, ..., <type> -> <type>]"
;   "              |  [<type> < <type>]"
;   " <type> ::= Any sequence of alphanumeric characters"
   " <equation> ::= <term> | <term> == <rhs> | <term> ---> <rhs>"
   " <rhs> ::= <term> | <term> if <term>"
   " <term> ::= <item> | <item> <infix-op-term>"
   " <item> ::= <variable> | <constant> | (<term>) "
   "            | <function> <term-args>"
   "            | all <varlist> <assertion-item> "
   "            | exist <varlist> <assertion-item> "
   "            | not <assertion-item> "
   "            | true | false "
   " <infix-op-term> ::= <bi-operator> <term>"
   " <bi-operator> ::= and | & | or | xor | -> | equ | = | <function>"
   " <term-args> ::= <nothing> | ( <term> <comma-args> )"
   " <comma-args> ::= <nothing> | , <term> <comma-args>"
   " <varlist> ::= ( <variable> <comma-varlist> ) | <variable>"
   " <comma-varlist> ::= <nothing> | , <variable> <comma-varlist>"
   " <function> ::= A letter in [a .. t] or any upper case letter followed"
   "                by a sequence of alphanumeric characters or a word of"
   "                {+ - & ^ $ # @ ! : . =}, except --->, ==, :=, if"
   " <constant> ::= A number"
   " <variable> ::= A letter in [u .. z] followed by a sequence of "
   "                alphanumeric characters"
   " <nothing> ::= "
   " "
   " All functions must be used with the same number of arguments."
   " All free variables are considered as universally quantified variables."
   " "
   " Pre-defined precedence: "
   "  {<function>} > {not} > {and} > {->} > {all, exists} > {equ} > {or, xor}"
   " "
   " Note that all infix binary operators associate to the left if no "
   " parentheses or no precedence are given."
   " "
   ))

(defconstant *help-order*  
  ;; >>>>>>>> 1/7/89   Help message for ordering rules.
'(
"  Abort     - Quit to the top of HERKY."
"  Display   - Display equivalence, precedence, and status of operators. "
"  Drop      - Throw it away."
"  Equiv     - Make two operators equivalent. "
"  Lrule     - Hand orient equation left-to-right. "
"  Left      - Hand orient equation left-to-right (not for reduction)."
"  MakeEq    - Make a rule as (lhs = rhs) ---> true ."
"  Operator  - Introduce new operator. "
"  Postpone  - Postpone orienting this equation."
"  Quit      - Interrupt and go to top level. "
"  Right     - Orient equation right-to-left (not for reduction). "
"  Rrule     - Orient equation right-to-left. "
"  Status    - Set lexicographic status of an operator. "
"  Twoway    - Make two superposition-only rewrite rules."
"  Undo      - Undo previous operation. "
"  Help      - Print this message."
""
))

(defconstant *max-ops*       300) ; operators.lisp
(defconstant *predef-ops*  (- *max-ops* 11)) ; related to *max-ops*.
(defconstant *=*           (+ *predef-ops* 0))  ; operators.lisp
(defconstant *false*       (+ *predef-ops* 1)) ; operators.lisp
(defconstant *true*        (+ *predef-ops* 2)) ; operators.lisp
(defconstant *and*         (+ *predef-ops* 3))  ; operators.lisp
(defconstant *or*          (+ *predef-ops* 5))  ; operators.lisp
(defconstant *not*         (+ *predef-ops* 6))  ; operators.lisp
(defconstant *->*          (+ *predef-ops* 7))  ; operators.lisp
(defconstant *exist*       (+ *predef-ops* 8))  ; operators.lisp
(defconstant *all*         (+ *predef-ops* 9))  ; operators.lisp
(defconstant *equ*         (+ *predef-ops* 10))  ; operators.lisp
(defconstant *avoid-cmds* '("init" "cmd" "close" "quit" "help" "auto" "break" "gc"))
(defconstant *char-code-limit* 192) ; Parameter ; symbols.lisp
(defconstant *dim1*          100) ; diophantine.lisp
(defconstant *dim2*            8) ; diophantine.lisp
(defconstant *dim3*            4) ; diophantine.lisp
(defconstant *dim4*        (list *dim3* *dim3*)) ; diophantine.lisp
(defconstant *empty-sub*       t) ; match.lisp
(defconstant *eof-list* '(*eof*)) ; symbols.lisp 
(defconstant *eq*            *=*)
(defconstant *exist*all*    (list *all* *exist*)) ; operators.lisp
(defconstant *falseterm*    (list *false*)) ; operators.lisp
(defconstant *first-user-op*   1) ; operators.lisp(
(defconstant *max-vars*       90) ;Number of variables; variables.lisp
(defconstant *max-vars-all* (* 2 *max-vars*)) ; Total number of vars.
(defconstant *max-vars-half* (/ *max-vars* 2)) ;Number of variables; variables.lisp
(defconstant *multiple-first*  1) ;Find the first of rules ; disnet.lisp
(defconstant *multiple-resume* 2);Find the next rule ; disnet.lisp
(defconstant *single*          0) ; Find at most one rule ; disnet.lisp
(defconstant *stack-size*    256) ; 
(defconstant *true*false*  (list *true* *false*)) ; operators.lisp
(defconstant *trueterm*    (list *true*)) ; operators.lisp
(defconstant *var-letters*  (list #\u #\v #\w #\x #\y #\z)) 
;; (#\U #\V #\W #\X #\Y #\Z)
(defconstant *xex1*        (- 2 *max-vars*)) ; unify.lisp
(defconstant *xex2*        (- 1 *max-vars*)) ; unify.lisp
(defconstant *xor*         (+ *predef-ops* 4))  ; operators.lisp
(defconstant *xor*and*     (list *and* *xor*)) ; operators.lisp
(defconstant *xor*and*or*  (list *and* *xor* *or*)) ; operators.lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFVARS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defvar $*$                nil) ; polynomial.lisp
(defvar $Q                 nil) ; diophantine.lisp
(defvar $a                 nil) ; diophantine.lisp
(defvar $ac                nil) 
(defvar $ac-distree nil)
(defvar $aclrpo              t) ; aclrpo.lisp
(defvar $add-crit-rule     nil) ; order.lisp
(defvar $add-time            0) ; time spent while adding rules
(defvar $akb-flag          nil) ; automatic knuth-bendix
(defvar $args              nil) ; diophantine.lisp
(defvar $array-in-use      nil) ; acdio.lisp
(defvar $associative       nil) 
(defvar $auto-sugg         nil) ; autoorder.lisp.
(defvar $automatic         nil) ; automatic mode
(defvar $aux-rules         nil) ; auxiliary rule set
(defvar $avoid-rules       nil) ; condinorm.lisp
(defvar $b                 nil) ; diophantine.lisp
(defvar $basis             nil) ; diophantine.lisp
(defvar $big-unifier       nil) ; acdio.lisp
(defvar $block-cps         nil) ; count of unblocked critical pairs.

(defvar $bound-vars
  #+kcl (make-array *max-ops* :element-type 'fixnum :static t)
  #-kcl (make-array *max-ops* :element-type 'fixnum)
  )

(defvar $brt-time            0) ; time spent in brt.
(defvar $char-buffer (make-string 250)) ; symbols.lisp
(defvar $char-read         nil) ; last character read by "read-one-char".
(defvar $char-type     '*eoln*) ; symbols.lisp ;; the type of $char-read.
(defvar $char-type-table (make-array (list *char-code-limit*))) ; symbols.lisp
(defvar $check-homogenous    t)   ;; effective when $polynomial is on.
(defvar $check-unit-conflict t) 
(defvar $chiang            nil)   ;; Chiang's implementation of the boolean method.
(defvar $children-size 0)  ;; number of children of a node (equal to $num-ops).
(defvar $ckb-flag          nil) ; t iff the system is conditional.
(defvar $combination nil) ; diophantine.lisp
(defvar $commutative       nil) 
(defvar $condi             nil) ;; explicit induction flag.
(defvar $confluent         nil) ;; t iff the system is confluent.
(defvar $constructors      nil) 
(defvar $crit-with-str      'm)
(defvar $current-node nil) ;; current node in a distree.
(defvar $d                 nil) ; diophantine.lisp
(defvar $deep-condi          2)
(defvar $defaults          nil)  ;; default flags.
(defvar $del-eqns          nil) ; equations from deleted rules.
(defvar $del-new-rules     nil)
(defvar $del-rules         nil)
(defvar $del-rule-str        2)
(defvar $detachment-ops    nil) ; fopcsuper.lisp
(defvar $discard-eqn-max-degree 4)
(defvar $discard-eqn-max-depth 0)
(defvar $discard-eqn-max-size 30)
(defvar $discard-eqn-2max-size 60)
(defvar $discard-poly-max-size 200)
(defvar $discarded         nil) ; t iff some equations are discarded or deleted.
(defvar $distree           nil) ;; A discrimination tree is just a tree node.
(defvar $distree-sigma nil)
(defvar $distributive      nil)
(defvar $divisible         nil) 
(defvar $e                 nil) ; diophantine.lisp
(defvar $eq-arity            t) ; autoorder.lisp
(defvar $eq-length         nil) ; match.lisp 
(defvar $eqn-set           nil)        ; equation set
(defvar $eqop-list         nil) 
(defvar $ex1                 3)
(defvar $ex2                 6)
(defvar $f-weights         nil) 
(defvar $false-rhs         nil) ;;
(defvar $falsed-pre        nil) ; premises.lisp
(defvar $fast-match          1)   ;;
(defvar $fopc              nil) ;; t iff boolean ring method is used.
(defvar $fopc-lrpo         nil) ;;
(defvar $free-constructors nil)
(defvar $func-name         "a") ;; substitution function names. ; globals.lisp
(defvar $guha              nil) ;; t iff boolean ring method is used.
(defvar $hyper-superpose   nil)
(defvar $idem-superpose    nil)
(defvar $immediate         nil)
(defvar $in-port           nil) ;; input file stream
(defvar $infix-ops  (list *=* *and* *xor* *or* *->* *equ*)) ; operators.lisp
(defvar $init-ac-arrays    nil) ; diophantine.lisp
(defvar $input-superpose   nil) ; input-superposition strategy.
(defvar $instant           nil) ;; flag to use instantions of rules.
(defvar $instant-seeds     nil) ;; list of terms for instantiation.
(defvar $inter-range       nil) ; match.lisp
(defvar $inverse-ops       nil) 
(defvar $kb                nil) ;; Which Knuth-Bendix completion to run?
(defvar $keep-deleted-rules nil) ;; Keep deleted rule for displaying proofs
(defvar $l-st-list         nil)  ;; operators with lr-status
(defvar $last-soln         nil) ; acdio.lisp
(defvar $left-cps          nil) ;
(defvar $limited-ops       nil) ; local variabled used in terms.lisp
(defvar $log-flag          nil) ; 
(defvar $log-port          nil) ; command registry file stream
(defvar $lrpo                t)   ;;
(defvar $many-args           4) ;
(defvar $mark-rule-str      'l)
(defvar $max-num-ac-args    16)
(defvar $maxd              nil) ; diophantine.lisp
(defvar $maxe              nil) ; diophantine.lisp
(defvar $more-break        nil)
(defvar $mt                nil) ; ac.lisp,  all ac arguments are in multisets.
(defvar $ncritpr             0)
(defvar $new-ax              0) ; pairs.lisp
(defvar $new-sym-num         0) ; symbols.lisp
(defvar $new-variable        0) ; variables.lisp
(defvar $newop-first         1) ; autoorder.lisp
(defvar $newop-terms       nil) ; autoorder.lisp
(defvar $newops            nil)  ;; used in reader.lisp
(defvar $newpoly             t) ;;
(defvar $newrule-max        50)
(defvar $nilpotent-rules   nil) ; of form n x ---> a.
(defvar $no-0-basis        nil) ; diophantine.lisp
(defvar $non-comm-cover-sets nil) ; recursive definition cover sets.
(defvar $norm-str           'o)
(defvar $norm-time           0) ; time spent in normalization
(defvar $nrules              0) ; number of generated rules
(defvar $num-del-rules       0) ; number of deleted rules
(defvar $num-of-bound-vars   0) ; from match.lisp
(defvar $num-ops             *first-user-op*) ; operators.lisp 
(defvar $num-trans         nil) ; aclrpo.lisp
(defvar $num-type        'univ) ; parser.lisp
(defvar $num-vars            0) ; the number of variables in the current unit.
(defvar $nusereqn            0)              ; number of user's equation.
(defvar $old-nrules          0)
(defvar $one-superpose     nil)
(defvar $op-rules          nil) ; a-list of form: ((op . (rules))...)

(defvar $op-names			;Print names
  #+kcl (make-array *max-ops* :static t)
  #-kcl (make-array *max-ops*)
  )
(defvar $op-arities			;Arities
  #+kcl (make-array *max-ops* :element-type 'fixnum :static t)
  #-kcl (make-array *max-ops* :element-type 'fixnum)
  )
(defvar $op-arities2			;Arities2
  #+kcl (make-array *max-ops* :static t)
  #-kcl (make-array *max-ops*)
  )
(defvar $op-lex-weights		;Lex weights for KB ordering
  #+kcl (make-array *max-ops* :element-type 'fixnum :static t)
  #-kcl (make-array *max-ops* :element-type 'fixnum)
  )
(defvar $op-pred			;
  ;; 0: not predicate, 1: predicate.
  #+kcl (make-array *max-ops* :element-type 'bit :static t)
  #-kcl (make-array *max-ops* :element-type 'bit)
  )
(defvar $op-weights			;Symbol weights for KB ordering
  #+kcl (make-array *max-ops* :element-type 'fixnum :static t)
  #-kcl (make-array *max-ops* :element-type 'fixnum)
  )

(defvar $ord-time            0) ; time spent in ordering
(defvar $order-condition   nil)
(defvar $ordering           'l)  ;;
(defvar $out-port          nil)  ;;
(defvar $other-side-of-eqn nil)
(defvar $over-rewrite        2) ;; depth of conditional rewriting.
(defvar $p-commut-rules    nil) ; pseudo-commutativity rules.
(defvar $pair-set          nil)    ; for ac-completion only
(defvar $paramodulate       'n)  ;;
(defvar $pick-rule-str      'l)
(defvar $polished-premises nil) ; condinorm.lisp
(defvar $poly-*-asso         t) ; polynomial.lisp
(defvar $poly-multi-1p-rules nil)    ;
(defvar $poly-rules        nil)    ; lhs or rhs is a polynomial.
(defvar $polynomial        nil) ;;
(defvar $post-ass-list     nil)
(defvar $post-ass-set      nil)        ; postponed propositions
(defvar $post-max          100) 
(defvar $post-posi           2) ; autoorder.lisp
(defvar $post-set          nil)        ; postponed equations
(defvar $pre-first           1) ; autoorder.lisp
(defvar $precedence         nil) 
(defvar $premises-set      nil) ; premisenorm.lisp
(defvar $prime-acu           t) ; flag
(defvar $prime-cps         nil) ; flag
(defvar $proc-time           0) ; total time by processor
(defvar $prove-eqn         nil) ; containing proving equation.
(defvar $prove-eqns        nil) ; containing proving equations.
(defvar $prove-method       's)
(defvar $pure              nil)
(defvar $r-st-list         nil) ; operators with rl-status
(defvar $reduce-max       1000)
(defvar $reduce-system       3)
(defvar $reduce-times     1000) ; normalize.lisp
(defvar $reduced-premises  nil) ; condinorm.lisp
(defvar $refutation        nil) ;;
(defvar $roses-found       nil)
(defvar $rl-first            2) ; autoorder.lisp
(defvar $rule-set          nil) ; rule set
(defvar $rule-size          's)
(defvar $rule-x-to-y       nil) ; pairs.lisp ;; rule being renamed x's to y's.
(defvar $rules-to-pair     nil)     ; big rules to be paired.
(defvar $runtime-max         0) ; clocks.lisp ;; 0 means no bound.
(defvar $save-y-rule       nil) ;; t iff every y-rule will be saved.
(defvar $sigma             nil) ; diophantine.lisp
(defvar $skolem-ops        nil)  ;; ops introduced as skolem functions.
(defvar $step-deep           3)
(defvar $superposed-sub    nil) ; critical.lisp
(defvar $superposed-subs   nil) ; critical.lisp
(defvar $subs2             nil) ; acdio.lisp
(defvar $subsume-rules     nil) ; non-terminating rules.
(defvar $sumx              nil) ; diophantine.lisp
(defvar $sumy              nil) ; diophantine.lisp
(defvar $support           nil) 
(defvar $symbnum             0)
(defvar $symmetry-arg-positions nil) ; symmetry.lisp
(defvar $symmetry-check      t)   ;; flag to use symmetry check.
(defvar $symmetry-dels       0) ; number of unifiers deleted by symm.
(defvar $symmetry-good-terms nil) ; symmetry.lisp
(defvar $symmetry-terms    nil) ; symmetry.lisp
(defvar $test-in-process   nil) ; t iff the test is in process.
(defvar $theory-eqns       nil) ; equations built in the system.
(defvar $theory-rules      nil) ; equations built in the system.
(defvar $top-only-var-check  t)   ;; flag to use ..
(defvar $top-only-vars     nil)   ;; flag to use ..
(defvar $total-time          0) 
(defvar $trace-proof       nil) ;; trace refutational proof.
(defvar $trace-flag          3)   ;; trace strategy
(defvar $try               nil) ;; debugging flag.
(defvar $type-constructors nil)
(defvar $type-of-num   '(univ))    ; the default type for "num".
(defvar $type-rela         nil)    ; 
(defvar $unit-ops          nil)    ;
(defvar $unit-superpose    nil)    ;
(defvar $unmark-rule-str    'l)    ; use $pair-set to organize the unmarked rules.
(defvar $used-rule-nums    nil)    ;
(defvar $used-rule-nums-old nil)   ; a copy of $used-rule-nums.
(defvar $var-bindings    (make-array *max-vars-all*)) 
(defvar $var-premises      nil)    ; premises of (var = terms)
(defvar $var-print-names (make-array *max-vars-all*))
(defvar $write-to-file     nil) ; output.lisp
(defvar $x                 nil) ; diophantine.lisp
(defvar $xnx                 5) ; polynomial.lisp
(defvar $y                 nil) ; diophantine.lisp
(defvar $ymax              nil) ; diophantine.lisp
(defvar *+*                nil) ; polynomial.lisp
(defvar *-*                nil) ; polynomial.lisp
(defvar *0*                nil) ; polynomial.lisp
(defvar *0term*            nil) ; polynomial.lisp


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; DEFSTRUCTS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Moved from axioms.lisp
;; The basic equation.
(defstruct (ax (:print-function print-ax))
  lhs		;Left side                               = lhs
  rhs		;Right side                              = rhs
  lvars         ;Varibales in lhs of eqn.                = next
  rvars         ;Varibales in rhs of eqn.                = prev
  ctx           ;Context or conditions                   = fsym-def-p
  cvars         ;Varibales in ctx of eqn.                = queue
  eqn-info      ;Information when ax as equation         =
  y-rule        ;Rule with x being renamed to y
  )

(defstruct einfo
  source	;Source of the equation                  = parents
  used-rules    ;Rules used to simplify this equation
  rule-info     ;Information as a rule                   = (id type)
  info          ;Special Information                     = supported
  rule-rose	;                                        = backpointers
  lhs-roses    ;                                        = priority1
  rhs-roses    ;                                        = priority2
  )

(defstruct rinfo
  ruleno      ;Rule number, a unique id                  = id
  size        ;Size of the rule                         
  picked      ;Critical pairs been computed?            
  type        ;                                          = type
  ;; 1: reduction; 2: permutation; 4: subsumption 5: dummy 
  pair-with   ;Rules which have CPs.         
  )

;; Moved from distree.lisp
;; Discrimination tree node.
(defstruct (dtnode (:print-function print-dtnode))
  id    	;The operator id (when variable, id = 0) leading to this node.
  num-of-rules  ;How many rules below this tree node.
  num-of-child  ;How many children this tree node has.
  parent	;Parent node in tree
  children	;Either an Array of tree nodes or an rose.
  )

;; At the end of a path in a discrimination tree,
;; there is an rose which contains all the subterms
;; whose linear representation is the path.

(defstruct (rose (:print-function print-rose2))
  parent         ;Parent node of the rose.
  rules          ;Rules whose lhs leads to this rose.
  lhs-terms      ;Subterms of lhs of rules.
  rhs-terms      ;Subterms of rhs of rules 
; eqn-terms      ;Subterms in eqns.
  )
    

