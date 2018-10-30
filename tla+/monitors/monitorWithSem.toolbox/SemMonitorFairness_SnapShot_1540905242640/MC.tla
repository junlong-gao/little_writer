---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0SEMCOUNT
const_1540905237140244000 == 
2
----

\* CONSTANT definitions @modelParameterConstants:1THREADS
const_1540905237140245000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540905237141246000 ==
MSemSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540905237141247000 ==
CVSignalFairness
----
=============================================================================
\* Modification History
\* Created Tue Oct 30 06:13:57 PDT 2018 by junlongg
