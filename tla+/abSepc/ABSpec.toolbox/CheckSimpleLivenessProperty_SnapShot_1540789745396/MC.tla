---- MODULE MC ----
EXTENDS ABSpec, TLC

\* CONSTANT definitions @modelParameterConstants:0Data
const_1540789742365101000 == 
{0, 1}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540789742365102000 ==
Spec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540789742365103000 ==
\A v \in Data \X {0, 1}: (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 22:09:02 PDT 2018 by junlongg
