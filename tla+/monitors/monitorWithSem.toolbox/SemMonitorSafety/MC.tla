---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105777870918000 == 
{"t1", "t2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154105777870919000 ==
Sem.counter < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105777870920000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105777870921000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:36:18 PDT 2018 by junlongg
