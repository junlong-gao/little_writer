---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085379067947000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085379067948000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154085379067949000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 15:56:30 PDT 2018 by junlongg
