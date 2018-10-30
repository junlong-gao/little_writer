---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540928316139378000 == 
{"t1", "t2", "t3"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540928316139379000 == 
5
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540928316140380000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540928316140381000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 12:38:36 PDT 2018 by junlongg
