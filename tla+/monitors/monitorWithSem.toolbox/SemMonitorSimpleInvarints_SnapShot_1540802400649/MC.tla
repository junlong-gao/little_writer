---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540802393609319000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540802393609320000 == 
Permutations(const_1540802393609319000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540802393609321000 == 
1
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802393609322000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540802393609323000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540802393609324000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:39:53 PDT 2018 by junlongg
