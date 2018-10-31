---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095161720340000 == 
{"t1", "t2", "t3"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_154095161720341000 == 
5
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095161720342000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095161720343000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:06:57 PDT 2018 by junlongg
