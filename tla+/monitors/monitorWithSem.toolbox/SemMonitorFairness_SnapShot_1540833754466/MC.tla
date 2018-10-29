---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_15408337512482000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_15408337512483000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15408337512494000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15408337512495000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 10:22:31 PDT 2018 by junlongg
