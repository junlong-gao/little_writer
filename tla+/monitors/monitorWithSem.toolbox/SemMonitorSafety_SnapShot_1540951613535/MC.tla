---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095160548536000 == 
{"t1", "t2"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_154095160548537000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095160548538000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095160548539000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:06:45 PDT 2018 by junlongg
