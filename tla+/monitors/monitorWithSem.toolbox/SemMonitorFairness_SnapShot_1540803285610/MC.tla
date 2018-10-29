---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540803282083366000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540803282083367000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540803282083368000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540803282083369000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:54:42 PDT 2018 by junlongg
