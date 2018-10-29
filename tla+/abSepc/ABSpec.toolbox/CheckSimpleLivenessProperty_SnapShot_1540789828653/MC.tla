---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1540789825623107000 == 
{0}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540789825623108000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540789825623109000 ==
\A v \in Data \X {0, 1}: (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 22:10:25 PDT 2018 by junlongg
