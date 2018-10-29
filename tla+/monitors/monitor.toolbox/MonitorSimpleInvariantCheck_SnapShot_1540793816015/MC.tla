---- MODULE MC ----
EXTENDS monitor, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
t2, t1
----

\* MV CONSTANT definitions THREADS
const_1540793807973190000 == 
{t2, t1}
----

\* INIT definition @modelBehaviorInit:0
init_1540793807973191000 ==
MInit
----
\* NEXT definition @modelBehaviorNext:0
next_1540793807973192000 ==
MNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_1540793807973193000 ==
MonitorTypeInv
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 23:16:47 PDT 2018 by junlongg
