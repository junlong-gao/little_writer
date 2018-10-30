---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540928305913374000 == 
{"t1", "t2"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540928305913375000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540928305913376000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540928305913377000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 12:38:25 PDT 2018 by junlongg
