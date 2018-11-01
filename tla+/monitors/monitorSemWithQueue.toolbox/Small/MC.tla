---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154105843461289000 == 
{"t1", "t2"}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_154105843461290000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154105843461291000 ==
MSemQSpecInv
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_154105843461292000 ==
MonitorSafety
----
\* PROPERTY definition @modelCorrectnessProperties:1
prop_154105843461293000 ==
MonitorLiveness
----
=============================================================================
\* Modification History
\* Created Thu Nov 01 00:47:14 PDT 2018 by junlongg
