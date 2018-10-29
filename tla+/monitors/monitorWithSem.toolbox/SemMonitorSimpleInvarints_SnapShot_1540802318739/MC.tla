---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_1540802310693308000 == 
{"t1"}
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540802310693309000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802310693310000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540802310693311000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540802310693312000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:38:30 PDT 2018 by junlongg
