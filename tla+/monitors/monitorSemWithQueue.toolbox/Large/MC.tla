---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095111746826000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095111746827000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095111746828000 ==
CVSignalFairness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154095111746829000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 18:58:37 PDT 2018 by junlongg
