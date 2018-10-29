---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540802614808349000 == 
{t1, t2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802614808350000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540802614808351000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:43:34 PDT 2018 by junlongg
