---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540905314105252000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540905314105253000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540905314105254000 ==
CVSignalFairness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540905314105255000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 06:15:14 PDT 2018 by junlongg
