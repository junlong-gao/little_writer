---- MODULE RenameSmall ----
EXTENDS Rename, TLC


InitTreeMV ==
[T |-> {"A", "B"}, A |-> {"C"}, C |-> {}, B |-> {"D"}, D |-> {}]


ThreadsMV ==
{"t1", "t2"}


NodesMV ==
{"T", "A", "B", "C", "D"}


RootMV ==
"T"


Spec ==
RNSpec

Inv ==
   RNLoopFree
/\ RNConserve
/\ RNTypeOK
=============================================================================
