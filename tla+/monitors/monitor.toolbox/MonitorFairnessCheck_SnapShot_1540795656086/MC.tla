---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540795648041234000 == 
{t1, t2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540795648041235000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540795648041236000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 23:47:28 PDT 2018 by junlongg
