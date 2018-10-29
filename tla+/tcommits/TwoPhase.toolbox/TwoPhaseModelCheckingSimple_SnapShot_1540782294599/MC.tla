---- MODULE MC ----
EXTENDS TwoPhase, TLC

\* CONSTANT definitions @modelParameterConstants:0RM
const_15407822843946000 == 
{"r1", "r2", "r3"}
----

\* INIT definition @modelBehaviorInit:0
init_15407822843947000 ==
TPInit
----
\* NEXT definition @modelBehaviorNext:0
next_15407822843948000 ==
TPNext
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_15407822843949000 ==
TPTypeOK
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 20:04:44 PDT 2018 by junlongg
