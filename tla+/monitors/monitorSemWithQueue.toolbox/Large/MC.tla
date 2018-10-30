---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540903782546228000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540903782546229000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540903782546230000 ==
CVSignalFairness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1540903782546231000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 05:49:42 PDT 2018 by junlongg
