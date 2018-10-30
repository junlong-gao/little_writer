---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540859379894224000 == 
{"t1", "t2", "t3", "t4"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859379894225000 ==
MSemQSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540859379894226000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:29:39 PDT 2018 by junlongg
