---- MODULE MC ----
EXTENDS monitor, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095147146433000 == 
{"t1", "t2", "t3"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095147146434000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095147146435000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:04:31 PDT 2018 by junlongg
