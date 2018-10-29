----------------------------- MODULE seqRemove -----------------------------

EXTENDS Integers, Sequences

Remove(i, seq) == 
  [j \in 1..(Len(seq)-1) |-> IF j < i THEN seq[j] 
                                      ELSE seq[j+1]]
=============================================================================
\* Modification History
\* Last modified Sun Oct 28 21:32:51 PDT 2018 by junlongg
\* Created Sun Oct 28 21:32:41 PDT 2018 by junlongg
