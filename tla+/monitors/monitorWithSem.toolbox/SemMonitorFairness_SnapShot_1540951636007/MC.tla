---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_154095163397144000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_154095163397145000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095163397146000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095163397147000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:07:13 PDT 2018 by junlongg
