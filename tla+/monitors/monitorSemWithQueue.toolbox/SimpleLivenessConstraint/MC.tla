---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540858065160151000 == 
{"t1", "t2", "t3"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858065160152000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540858065160153000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:07:45 PDT 2018 by junlongg
