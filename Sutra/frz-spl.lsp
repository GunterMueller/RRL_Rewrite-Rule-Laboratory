;; Global variables used in RRL .
;; Remember: When you introduce new globals, you should add it 
;; either into history.l or into saveload.l.
#+franz
(declare (special
       $total-time $helpfile     ; from toplevel

        v_binds ; from term.l
        $inter-range $eq-length
	;; Global data structure
	$separators $history1 $history $no-history $max-history 
 	$eqn-set $rule-set $operlist $op_rules 
	$invalid-rules
 	$test $in-port $save-in-port $example-dir $nusereqn $ac
 	$defaults $log-port $nrules $bool-ops 
	$f-weights $ex1 $ex2

	;; typing
	$type-rela $strong-type $num-type $var-type-list

	;;Time Statistics
	$add_time $norm_time $unif_time $ord_time $proc_time 
	$block_time $brt_time $reduce_time $runtime-max

	;; Status of kb
	$confluent $nrules $ncritpr 
	$newrule-num $akb_flag $ckb_flag $no-rule-del $symbnum 
	$reduce-times $reduce-bound
	$unblocked $aux-rset $pair-set $post-set $del-rules $del-rule-nums 
	$reduce-right $symmetry-dels $prime-acu $del-eqns

	;; KB strategies.
	$pick-rule-str $crit-with-str $rule-size 
	$mark_rule_str $del_rule_str $trace_flag $resume-rule 
	$norm_str $blocking-on $reduce-system $support $check-symmetry

	;; Precedence.
	$lrpo $ordering $glob_prec $st_list $eqop_list
	$divisible $translist $commutative $associative $constructors

	;; Auto Ordering.
       	$auto-sugg $resume-rule $newop-terms $max-arity
	$newop-first $pre-first $post-posi $rl-first $eq-arity 
	$post-max $newrule-max $newrule-num $max-history 
	$post-bound

	;; Proof system and Sufficient Completeness Test System.
	$sufficient $prove-eqn $witness-eqn $guest-eqn
	$cons-of-ts $newops $quasis
 	$type-constructors $free-constructors $type-testset
 	$testset $def-domains $prove-method $induc-vars $
	$instant $instant-seeds

	;; FOPC system.
	$post-ass-set $post-ass-list $more-break $immediate $idem 
 	$func-name $small-depth $set_pred $fopc-lrpo
	$fast-match $paramodulate $in-fopc $false-rhs 

	;; Narrowing
	$narrow $goal-set $ans-rule $op_goal_rules $goal-reduce 
	$one-way $anspred

	;; Manual ordering history frequency
	$manual-history-frequency $manual-history-number

	;; Conditional Rewriting
	$deep-condi $cycle-rule $cycle-op-rules $step-deep $falsed-pre

	;; explicit induction
	$induc $cover-sets $premises-set $var-premises $succ-eqns $build-rules 
	$defin-depend $non-comm-cover-sets
	$failed-eqns $induc-eqns $first-induc-op $gene-num

	$try
	  
	sharp-backslash-end 
	user-top-level 
	
	$trace-proof $used-rule-nums $over-rewrite 
	$symmetry-terms $symmetry-check $many-args $character-rules 
	$polynomial $p-commut-rules $poly-homo-rules

	$new-ac
))


#+franz
(defmacro aset (value array &rest indices)
   `(funcall ,array ,value ,@indices))

#+franz
(defmacro aref (array &rest indices)		
   `(funcall ,array ,@indices))

;;; Functions used to be in franz-array.l
#+franz
(defun make-array (dims)
   (eval (cons 'array
          (append '(nil t)
                  (if (listp dims) dims (list dims))))))

