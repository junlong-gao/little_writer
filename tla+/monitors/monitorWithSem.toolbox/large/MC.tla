---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105832390878000 == 
{"t1", "t2", "t3"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154105832390979000 ==
Sem.counter < 5
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105832390980000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154105832390981000 ==
MSemSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105832390982000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154105832390983000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:45:23 PDT 2018 by junlongg
