---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095222884868000 == 
{"t1", "t2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154095222884869000 ==
Sem.counter < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095222884870000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095222884871000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:17:08 PDT 2018 by junlongg
