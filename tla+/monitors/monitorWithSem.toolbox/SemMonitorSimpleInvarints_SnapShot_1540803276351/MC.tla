---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540803268298360000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540803268298361000 == 
Permutations(const_1540803268298360000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540803268298362000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540803268298363000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540803268298364000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540803268298365000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:54:28 PDT 2018 by junlongg
