---- MODULE MC ----
EXTENDS monitorSemWithQueue, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t1, t2, t3, t4
----

\* MV CONSTANT definitions THREADS
const_1540858048529147000 == 
{t1, t2, t3, t4}
----

\* SYMMETRY definition
symm_1540858048529148000 == 
Permutations(const_1540858048529147000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540858048529149000 ==
MSemQSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540858048529150000 ==
MonitorInv
----
=============================================================================
\* Modification History
\* Created Mon Oct 29 17:07:28 PDT 2018 by junlongg
