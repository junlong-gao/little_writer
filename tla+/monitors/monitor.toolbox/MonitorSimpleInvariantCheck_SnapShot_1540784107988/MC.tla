---- MODULE MC ----
EXTENDS monitor, TLC

\* CONSTANT definitions @modelParameterConstants:0THREADS
const_154078409995080000 == 
{"t1", "t2"}
----

\* INIT definition @modelBehaviorInit:0
init_154078409995081000 ==
MInit
----
\* NEXT definition @modelBehaviorNext:0
next_154078409995082000 ==
MNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154078409995083000 ==
MonitorTypeInv
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:34:59 PDT 2018 by junlongg
