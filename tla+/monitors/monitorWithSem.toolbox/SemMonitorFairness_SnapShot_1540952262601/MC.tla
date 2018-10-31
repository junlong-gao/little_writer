---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154095225881976000 == 
{"t1", "t2"}
----

\* CONSTRAINT definition @modelParameterContraint:0
constr_154095225881977000 ==
Sem.counter < 2
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154095225881978000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154095225881979000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 19:17:38 PDT 2018 by junlongg
