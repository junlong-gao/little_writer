---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085367413438000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085367413539000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154085367413540000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 15:54:34 PDT 2018 by junlongg
