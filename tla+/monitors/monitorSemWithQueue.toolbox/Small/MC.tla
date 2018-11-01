---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1541059426694114000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541059426694115000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541059426694116000 ==
MSemQSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1541059426694117000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1541059426694118000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 01:03:46 PDT 2018 by junlongg
