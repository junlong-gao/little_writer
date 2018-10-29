---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
r1, r2, r3
----

\* MV CONSTANT definitions RM
const_154078527605393000 == 
{r1, r2, r3}
----

\* SYMMETRY definition
symm_154078527605394000 == 
Permutations(const_154078527605393000)
----

\* INIT definition @modelBehaviorInit:0
init_154078527605395000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_154078527605396000 ==
TPNext
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154078527605397000 ==
[]TPTypeOK
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:54:36 PDT 2018 by junlongg
