---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085383520053000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085383520054000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154085383520055000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 15:57:15 PDT 2018 by junlongg
