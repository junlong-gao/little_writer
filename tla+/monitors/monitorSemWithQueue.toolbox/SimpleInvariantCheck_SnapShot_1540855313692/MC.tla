---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085530364165000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085530364166000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154085530364167000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 16:21:43 PDT 2018 by junlongg
