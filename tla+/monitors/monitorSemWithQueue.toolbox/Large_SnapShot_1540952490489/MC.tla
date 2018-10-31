---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095227684380000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095227684381000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095227684382000 ==
CVSignalFairness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154095227684383000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:17:56 PDT 2018 by junlongg
