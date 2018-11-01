---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4, t5
----

\* MV CONSTANT definitions THREADS
const_154105527637314000 == 
{t1, t2, t3, t4, t5}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105527637315000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105527637316000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154105527637317000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Wed Oct 31 23:54:36 PDT 2018 by junlongg
