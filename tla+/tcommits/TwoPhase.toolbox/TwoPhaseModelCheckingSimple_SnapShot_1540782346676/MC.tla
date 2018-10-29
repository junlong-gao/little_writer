---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_154078233962114000 == 
{"r1", "r2", "r3"}
----

\* INIT definition @modelBehaviorInit:0
init_154078233962115000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_154078233962116000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_154078233962117000 ==
TPTypeOK
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:05:39 PDT 2018 by junlongg
