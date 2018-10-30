---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540905155717240000 == 
{"t1", "t2", "t3"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540905155717241000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540905155717242000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540905155717243000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 06:12:35 PDT 2018 by junlongg
