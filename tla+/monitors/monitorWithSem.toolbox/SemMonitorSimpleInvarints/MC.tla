---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540804904862390000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540804904862391000 == 
Permutations(const_1540804904862390000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540804904862392000 == 
3
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540804904862393000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540804904862394000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540804904862395000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 02:21:44 PDT 2018 by junlongg
