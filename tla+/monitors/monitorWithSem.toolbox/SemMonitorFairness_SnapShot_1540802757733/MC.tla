---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540802753719356000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540802753719357000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802753719358000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540802753719359000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:45:53 PDT 2018 by junlongg
