---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540804405243386000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540804405243387000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540804405243388000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540804405243389000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 02:13:25 PDT 2018 by junlongg
