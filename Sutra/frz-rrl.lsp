#+franz
(progn
 
 (setq *rrl-files*
     '(term miscel match unify ac orderpc dioph 
	subst operators boolean initialize critical 
	kb history normalize normstrat lrpo order 
	precedence cancel makerules consist commut 
	set pickrules output suggprec normbool 
	aclrpo polynomial cyclerule coverrule typing 
	statistics toplevel syntax help
	frz-input options autoorder 
	condit building premises prem-norm 
	prove induc suffic narrow abstract 
	quasired paramod skolem pccrit assertion 
	refut conject testset equality structure saveload
	frz-only))
 (loop for file in *rrl-files* do (load file))
 (start-up)
)
