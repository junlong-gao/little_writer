---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t2, t1
----

\* MV CONSTANT definitions THREADS
const_1540793834429199000 == 
{t2, t1}
----

\* SYMMETRY definition
symm_1540793834429200000 == 
Permutations(const_1540793834429199000)
----

\* INIT definition @modelBehaviorInit:0
init_1540793834429201000 ==
MInit
----
\* NEXT definition @modelBehaviorNext:0
next_1540793834429202000 ==
MNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540793834429203000 ==
MonitorTypeInv
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 23:17:14 PDT 2018 by junlongg
