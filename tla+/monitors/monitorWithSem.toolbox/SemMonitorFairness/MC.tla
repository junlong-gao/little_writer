---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105779300022000 == 
{"t1", "t2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154105779300023000 ==
Sem.counter < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105779300024000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105779300025000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:36:33 PDT 2018 by junlongg
