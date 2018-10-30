---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540905300724248000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540905300724249000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540905300724250000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540905300724251000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 06:15:00 PDT 2018 by junlongg
