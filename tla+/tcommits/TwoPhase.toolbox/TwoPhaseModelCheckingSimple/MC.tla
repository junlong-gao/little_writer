---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_154078245908623000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_154078245908624000 == 
Permutations(const_154078245908623000)
----

\* INIT definition @modelBehaviorInit:0
init_154078245908625000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_154078245908626000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154078245908627000 ==
TPTypeOK
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:07:39 PDT 2018 by junlongg
