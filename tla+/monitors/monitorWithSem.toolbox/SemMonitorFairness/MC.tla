---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540928326703382000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540928326703383000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540928326703384000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540928326703385000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 12:38:46 PDT 2018 by junlongg
