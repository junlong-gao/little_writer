---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095191386848000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095191386849000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095191386850000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154095191386851000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:11:53 PDT 2018 by junlongg
