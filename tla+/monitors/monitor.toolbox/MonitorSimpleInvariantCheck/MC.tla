---- MODULE MC ----
EXTENDS monitor, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154078416618284000 == 
{"t1", "t2"}
----

\* INIT definition @modelBehaviorInit:0
init_154078416618285000 ==
MInit
----
\* NEXT definition @modelBehaviorNext:0
next_154078416618286000 ==
MNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154078416618287000 ==
MonitorTypeInv
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:36:06 PDT 2018 by junlongg
