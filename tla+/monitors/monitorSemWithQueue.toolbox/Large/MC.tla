---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105846770299000 == 
{"t1", "t2", "t3", "t4", "t5", "t6"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1541058467702100000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1541058467702101000 ==
MSemQSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1541058467702102000 ==
MonitorLiveness
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_1541058467702103000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:47:47 PDT 2018 by junlongg
