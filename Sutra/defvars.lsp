;;; -*- Mode: LISP; Syntax: Common-lisp; Package: RRL; Base: 10; -*-

#-franz (in-package "RRL")

;;
;;
;; all global variables used by RRL are defvar-ed here. -- siva.
;;
;;
;;

(defvar v_binds nil)

(defvar $separators nil)
(defvar $history1 nil)
(defvar $history nil)
(defvar $no-history nil)
(defvar $max-history nil)
(defvar $eqn-set nil)
(defvar $rule-set nil)
(defvar $op_rules nil)
(defvar $invalid-rules nil)

(defvar $test nil)
(defvar $in-port nil)
(defvar $save-in-port nil)
(defvar $example-dir (concatenate 'string user:*rrl-directory* "examples/"))
(defvar $nusereqn nil)
(defvar $defaults nil)
(defvar $log-port nil)
(defvar $bool-ops nil)

(defvar $type-rela nil)
(defvar $strong-type nil)
(defvar $num-type nil)
(defvar $var-type-list nil)
(defvar $add_time nil)
(defvar $norm_time nil)

(defvar $ord_time nil)
(defvar $proc_time nil)
(defvar $block_time nil)
(defvar $brt_time nil)
(defvar $reduce_time nil)
(defvar $runtime-max nil)
(defvar $confluent nil)
(defvar $nrules nil)
(defvar $ncritpr nil)
(defvar $akb_flag nil)
(defvar $ckb_flag nil)
(defvar $no-rule-del nil)
(defvar $symbnum nil)
(defvar $reduce-times nil)
(defvar $reduce-bound nil)
(defvar	$unblocked nil)
(defvar $aux-rset nil)
(defvar $pair-set nil)
(defvar $post-set nil)
(defvar $del-rules nil)
(defvar $del-rule-nums nil)

(defvar $reduce-right nil)
(defvar $symmetry-dels nil)
(defvar $prime-acu nil)
(defvar $del-eqns nil)
(defvar $pick-rule-str nil)
(defvar $crit-with-str nil)
(defvar $rule-size nil)
(defvar $mark_rule_str nil)
(defvar $del_rule_str nil)
(defvar $trace_flag 1)
(defvar $norm_str nil)
(defvar $reduce-system nil)
(defvar $support nil)
(defvar $check-symmetry nil)
(defvar	$f-weights nil)
(defvar $ex1 nil)
(defvar $ex2 nil)

(defvar $ac nil)
(defvar $blocking-on nil)
(defvar $unif_time 0)
(defvar $symmetry-terms nil)
(defvar $operlist nil)
(defvar $manual-history-frequency nil)
(defvar $manual-history-number nil)
(defvar $deep-condi 3)
(defvar $cycle-rule nil)
(defvar $cycle-op-rules nil)
(defvar $step-deep nil)
(defvar $falsed-pre nil)

(defvar $induc nil)
(defvar $cover-sets nil)
(defvar $premises-set nil)
(defvar $var-premises nil)
(defvar $succ-eqns nil)
(defvar $build-rules nil)
(defvar $defin-depend nil)
(defvar $non-comm-cover-sets nil)
(defvar	$failed-eqns nil)
(defvar $induc-eqns nil)
(defvar $first-induc-op nil)
(defvar $gene-num nil)

; must fix these
(defvar	sharp-backslash-end nil)
(defvar	user-top-level nil)

(defvar $trace-proof nil)
(defvar $used-rule-nums nil)
(defvar $over-rewrite nil)
(defvar $symmetry-check nil)
(defvar $many-args 4)
(defvar $character-rules nil)
(defvar $polynomial nil)
(defvar $poly-homo-rules nil)
(defvar	$new-ac nil)

(defvar $lrpo nil)
(defvar $ordering nil)
(defvar $glob_prec nil)
(defvar $st_list nil)
(defvar $eqop_list nil)
(defvar	$divisible nil)
(defvar $translist nil)
(defvar $commutative nil)
(defvar $associative nil)
(defvar $constructors nil)
(defvar $auto-sugg nil)
(defvar $resume-rule nil)
(defvar $newop-terms nil)
(defvar $max-arity nil)
(defvar	$newop-first nil)
(defvar $pre-first nil)
(defvar $post-posi nil)
(defvar $rl-first nil)
(defvar $eq-arity nil)
(defvar $post-max nil)
(defvar $newrule-max nil)
(defvar $newrule-num nil)
(defvar $post-bound nil)
(defvar $sufficient nil)
(defvar $prove-eqn nil)
(defvar $witness-eqn nil)
(defvar $guest-eqn nil)
(defvar	$cons-of-ts nil)
(defvar $newops nil)
(defvar $quasis nil)
(defvar $type-constructors nil)
(defvar $free-constructors nil)
(defvar $type-testset nil)
(defvar $testset nil)
(defvar $def-domains nil)
(defvar $prove-method nil)
(defvar $induc-vars nil)
(defvar $instant nil)
(defvar $instant-seeds nil)
(defvar $post-ass-set nil)
(defvar $post-ass-list nil)
(defvar $more-break nil)
(defvar $immediate nil)
(defvar $idem nil)
(defvar $func-name nil)
(defvar $small-depth nil)
(defvar $set_pred nil)
(defvar $fopc-lrpo nil)
(defvar	$fast-match nil)
(defvar $paramodulate nil)
(defvar $in-fopc nil)
(defvar $false-rhs nil)
(defvar $narrow nil)
(defvar $goal-set nil)
(defvar $ans-rule nil)
(defvar $op_goal_rules nil)
(defvar $goal-reduce nil)
(defvar $one-way nil)
(defvar $anspred nil)


(defvar $avoid-rules nil) ; from normalize.l

(defvar $add-crit-rule nil)  ; from order.l

(defvar $orderhelp nil)
(defvar $order-help nil)

(defvar $try nil)  ; from consistency.l

(defvar $p-commut-rules nil) ; from commutative.l

(defvar l__2 nil)  ; from output.l
(defvar l__3 nil)
(defvar l__ctr nil) 

(defvar $subs nil) ; from polynomial.l
(defvar $xnx 5)

(defvar $induc-terms nil) ; from coverrule.l

(defvar $inter-range nil) ; from match.l
(defvar $eq-length nil) 

(defvar $combination nil) ; from diophantine.l
(defvar $subs2 nil)
(defvar $last-soln nil)
(defvar $good-symmetry-terms nil)
(defvar $sym-arg-positions nil)

(defvar $helpfile nil) ; from toplevel.l
(defvar $total-time 0)

(defvar $grammar nil)

(defvar *rrl-readtable*
  (copy-readtable nil))

(defvar *errset-flag* (list 'errset))
(defvar piport (make-synonym-stream '*standard-input*))
(defvar poport (make-synonym-stream #-allegro '*standard-output*
				    #+allegro '*terminal-io*
	       ))
(defvar *rrl-package* (find-package "RRL"))

(defvar $reduced-premises nil)
(defvar num-trans 0)
(defvar $detachment-ops nil)
(defvar $possi-num 0)
(defvar $irredu-num 0)

(defvar *starting-cl-readtable* *readtable*)
