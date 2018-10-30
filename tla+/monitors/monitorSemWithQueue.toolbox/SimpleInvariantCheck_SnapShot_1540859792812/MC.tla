---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4
----

\* MV CONSTANT definitions THREADS
const_1540859783766239000 == 
{t1, t2, t3, t4}
----

\* SYMMETRY definition
symm_1540859783766240000 == 
Permutations(const_1540859783766239000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540859783766241000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540859783766242000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:36:23 PDT 2018 by junlongg
