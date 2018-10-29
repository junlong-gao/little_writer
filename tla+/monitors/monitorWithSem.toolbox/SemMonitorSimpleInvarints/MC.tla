---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540802458889343000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540802458889344000 == 
Permutations(const_1540802458889343000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540802458889345000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802458889346000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540802458889347000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540802458889348000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:40:58 PDT 2018 by junlongg
