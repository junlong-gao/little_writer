---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540802430107331000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540802430107332000 == 
Permutations(const_1540802430107331000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540802430107333000 == 
2
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540802430107334000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540802430107335000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540802430107336000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 01:40:30 PDT 2018 by junlongg
