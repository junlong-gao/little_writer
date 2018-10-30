---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540903751068224000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540903751068225000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540903751068226000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540903751068227000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 05:49:11 PDT 2018 by junlongg
