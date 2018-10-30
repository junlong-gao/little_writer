---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4, t5
----

\* MV CONSTANT definitions THREADS
const_1540858314244158000 == 
{t1, t2, t3, t4, t5}
----

\* SYMMETRY definition
symm_1540858314244159000 == 
Permutations(const_1540858314244158000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858314244160000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540858314244161000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:11:54 PDT 2018 by junlongg
