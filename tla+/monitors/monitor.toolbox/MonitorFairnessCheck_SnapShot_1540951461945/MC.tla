---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_154095145488430000 == 
{t1, t2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095145488431000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095145488432000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:04:14 PDT 2018 by junlongg
