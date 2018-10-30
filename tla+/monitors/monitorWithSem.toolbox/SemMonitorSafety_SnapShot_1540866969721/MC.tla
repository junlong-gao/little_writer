---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540866961674114000 == 
{"t1", "t2", "t3"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540866961674115000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540866961674116000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540866961674117000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 19:36:01 PDT 2018 by junlongg
