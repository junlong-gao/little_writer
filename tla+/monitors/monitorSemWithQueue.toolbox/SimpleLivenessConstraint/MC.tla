---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154085538717468000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154085538717469000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154085538717470000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 16:23:07 PDT 2018 by junlongg
