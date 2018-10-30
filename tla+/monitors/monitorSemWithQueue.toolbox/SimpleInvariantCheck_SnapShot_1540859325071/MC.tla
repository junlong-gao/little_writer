---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4, t5
----

\* MV CONSTANT definitions THREADS
const_1540859316025220000 == 
{t1, t2, t3, t4, t5}
----

\* SYMMETRY definition
symm_1540859316025221000 == 
Permutations(const_1540859316025220000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859316025222000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540859316025223000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:28:36 PDT 2018 by junlongg
