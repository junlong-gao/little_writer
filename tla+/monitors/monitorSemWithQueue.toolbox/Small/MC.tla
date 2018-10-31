---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095110510322000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095110510323000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095110510324000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154095110510325000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 18:58:25 PDT 2018 by junlongg
