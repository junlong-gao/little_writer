---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1541059438589119000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541059438589120000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541059438589121000 ==
MSemQSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1541059438589122000 ==
MonitorLiveness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1541059438589123000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 01:03:58 PDT 2018 by junlongg
