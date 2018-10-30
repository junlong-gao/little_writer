---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540858445981165000 == 
{"t1", "t2", "t3", "t4"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858445981166000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540858445981167000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:14:05 PDT 2018 by junlongg
