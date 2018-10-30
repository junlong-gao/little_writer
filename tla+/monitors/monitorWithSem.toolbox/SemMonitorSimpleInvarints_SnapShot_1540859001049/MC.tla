---- MODULE MC ----
EXTENDS monitorWithSem, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4
----

\* MV CONSTANT definitions THREADS
const_1540858993007210000 == 
{t1, t2, t3, t4}
----

\* SYMMETRY definition
symm_1540858993007211000 == 
Permutations(const_1540858993007210000)
----

\* CONSTANT definitions @modelParameterConstants:1SEMCOUNT
const_1540858993007212000 == 
5
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858993007213000 ==
MSemSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540858993007214000 ==
MonitorTypeInv
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_1540858993007215000 ==
SemWaitAfterCVWaitReg
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:23:13 PDT 2018 by junlongg
