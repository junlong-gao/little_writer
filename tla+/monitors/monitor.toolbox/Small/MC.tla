---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_15410552330316000 == 
{t1, t2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_15410552330317000 ==
MSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_15410552330318000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_15410552330319000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Wed Oct 31 23:53:53 PDT 2018 by junlongg
