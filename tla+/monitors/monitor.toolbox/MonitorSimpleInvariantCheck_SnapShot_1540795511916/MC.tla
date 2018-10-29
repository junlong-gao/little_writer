---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t2, t1
----

\* MV CONSTANT definitions THREADS
const_1540795499862223000 == 
{t2, t1}
----

\* SYMMETRY definition
symm_1540795499862224000 == 
Permutations(const_1540795499862223000)
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540795499862225000 ==
MSpec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540795499862226000 ==
MonitorTypeInv
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 23:44:59 PDT 2018 by junlongg
