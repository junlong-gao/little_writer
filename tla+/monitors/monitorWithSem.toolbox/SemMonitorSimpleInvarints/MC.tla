---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540803940693374000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540803940693375000 == 
Permutations(const_1540803940693374000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540803940693376000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540803940693377000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540803940693378000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540803940693379000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 02:05:40 PDT 2018 by junlongg
