---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2
----

\* MV CONSTANT definitions THREADS
const_1540859760796231000 == 
{t1, t2}
----

\* SYMMETRY definition
symm_1540859760796232000 == 
Permutations(const_1540859760796231000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859760796233000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540859760796234000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:36:00 PDT 2018 by junlongg
