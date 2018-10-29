---- MODULE MC ----
EXTENDS ABSpec, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
d1, d2, d3
----

\* MV CONSTANT definitions Data
const_1540789938120119000 == 
{d1, d2, d3}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_1540789938120120000 ==
FairSpec
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_1540789938120121000 ==
\A v \in Data \X {0, 1}: (AVar = v) ~> (BVar = v)
----
=============================================================================
\* Modification History
\* Created Sun Oct 28 22:12:18 PDT 2018 by junlongg
