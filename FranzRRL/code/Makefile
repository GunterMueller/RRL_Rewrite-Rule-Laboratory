.SUFFIXES: .l.o

.l.o:
	${Liszt} -q $*

Liszt = liszt

ReqSrc = ac.l aclrpo.l assertion.l autoorder.l \
	 abstraction.l \
	 boolean.l building.l \
	 cancellation.l commutative.l coverrule.l consistency.l critical.l \
	 cyclerule.l diophantine.l equality.l history.l \
	 induction.l initialize.l input.l kb.l \
	 lrpo.l makerules.l match.l miscel.l \
	 narrow.l normalize.l normbool.l normstrategy.l \
	 premises.l conditionals.l conjectures.l \
	 operators.l options.l order.l orderpc.l output.l \
	 paramodulation.l pccritical.l precedence.l prove.l \
	 pickrules.l polynomial.l premisenorm.l refutation.l \
	 quasireduce.l saveload.l set.l skolem.l statistics.l substitution.l \
	 structure.l sufficient.l suggprec.l syntax.l \
	 term.l testset.l toplevel.l typing.l unify.l


ReqObj = ac.o aclrpo.o assertion.o autoorder.o \
	 abstraction.o \
	 boolean.o building.o \
	 cancellation.o commutative.o coverrule.o consistency.o critical.o \
	 cyclerule.o diophantine.o equality.o history.o \
	 induction.o initialize.o input.o kb.o \
	 lrpo.o makerules.o match.o miscel.o \
	 narrow.o normalize.o normbool.o normstrategy.o \
	 premises.o conditionals.o conjectures.o \
	 operators.o options.o order.o orderpc.o output.o \
	 paramodulation.o pccritical.o precedence.o prove.o \
	 pickrules.o polynomial.o premisenorm.o refutation.o \
	 quasireduce.o saveload.o set.o skolem.o statistics.o substitution.o \
	 structure.o sufficient.o suggprec.o syntax.o \
	 term.o testset.o toplevel.o typing.o unify.o

AllSrc = Makefile ${ReqSrc}

all: ${ReqObj}

required: ${ReqObj}

sources: ${AllSrc}


