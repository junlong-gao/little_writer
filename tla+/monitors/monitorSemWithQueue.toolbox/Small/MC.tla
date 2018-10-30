---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540867713962176000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540867713963177000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540867713963178000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540867713963179000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 19:48:33 PDT 2018 by junlongg
