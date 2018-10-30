---- MODULE MC ----
EXTENDS monitor, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154086670842899000 == 
{"t1", "t2", "t3"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540866708428100000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540866708428101000 ==
MonitorSafety
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 19:31:48 PDT 2018 by junlongg
