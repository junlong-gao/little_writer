---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540867357043172000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540867357043173000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540867357043174000 ==
CVSignalFairness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540867357043175000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 19:42:37 PDT 2018 by junlongg
