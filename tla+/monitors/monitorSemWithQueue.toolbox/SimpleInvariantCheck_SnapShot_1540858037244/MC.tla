---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3
----

\* MV CONSTANT definitions THREADS
const_1540858029206139000 == 
{t1, t2, t3}
----

\* SYMMETRY definition
symm_1540858029206140000 == 
Permutations(const_1540858029206139000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858029206141000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540858029206142000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:07:09 PDT 2018 by junlongg
