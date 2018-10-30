---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540859134949216000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540859134949217000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859134949218000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540859134949219000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:25:34 PDT 2018 by junlongg
