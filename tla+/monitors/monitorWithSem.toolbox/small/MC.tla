---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105829822972000 == 
{"t1", "t2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154105829822973000 ==
Sem.counter < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105829822974000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154105829822975000 ==
MSemSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105829822976000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154105829822977000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:44:58 PDT 2018 by junlongg
