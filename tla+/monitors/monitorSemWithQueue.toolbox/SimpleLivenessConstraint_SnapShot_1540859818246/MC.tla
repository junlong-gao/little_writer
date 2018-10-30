---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540859810205246000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859810205247000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540859810205248000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:36:50 PDT 2018 by junlongg
