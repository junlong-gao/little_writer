---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095224482272000 == 
{"t1", "t2", "t3"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154095224482273000 ==
Sem.counter < 5
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095224482274000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095224482275000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:17:24 PDT 2018 by junlongg
