---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540804931173396000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540804931173397000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540804931173398000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540804931173399000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 02:22:11 PDT 2018 by junlongg
