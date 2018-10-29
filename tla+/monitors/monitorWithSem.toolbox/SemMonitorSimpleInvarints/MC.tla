---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540804382644380000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540804382644381000 == 
Permutations(const_1540804382644380000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540804382644382000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540804382644383000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540804382644384000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540804382644385000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 02:13:02 PDT 2018 by junlongg
