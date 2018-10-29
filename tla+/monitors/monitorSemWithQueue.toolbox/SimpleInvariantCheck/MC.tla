---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085369496541000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085369496542000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154085369496543000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 15:54:54 PDT 2018 by junlongg
