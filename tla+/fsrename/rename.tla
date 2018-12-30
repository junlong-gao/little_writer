------------------------------- MODULE rename -------------------------------
(* Rename: Transplant a subtree.  *)
EXTENDS TLC, Integers, FiniteSets
CONSTANT InitTree, Root, Nodes, Threads
VARIABLE ThreadHoldingLocks, ThreadRequiredLocks, FSTree, Txn

RNTypeOK ==
(* Validate model parameters: *)
       Root \in Nodes
    /\ InitTree \in [Nodes -> SUBSET(Nodes)]
    /\ (\A node \in Nodes : node \notin InitTree[node])
(* Validate runtime variables: *)
    /\ ThreadHoldingLocks \in
         [Threads -> SUBSET(Nodes)]
    /\ ThreadRequiredLocks \in
         [Threads -> SUBSET(Nodes)]
    (* each thread is either try-locking or got all the required locks: *)
    /\ (\A t \in Threads:
       ThreadHoldingLocks[t] \subseteq ThreadRequiredLocks[t])
    /\ FSTree \in [Nodes -> SUBSET(Nodes)]
    /\ (\A node \in Nodes : node \notin FSTree[node])
    /\ (Txn \in [Threads -> ({"null"} \union Nodes) \X
                            ({"null"} \union Nodes) \X
                            ( {"null"} \union Nodes)])
    /\ (\A t \in Threads: ThreadRequiredLocks[t] # {}
                      => Txn[t][1] \in ThreadRequiredLocks[t]
                      /\ Txn[t][2] \in ThreadRequiredLocks[t]
                      /\ Txn[t][3] \in ThreadRequiredLocks[t])

(* Some helper functions *)
(* check the graph is loop free and
there is a path from rootNode to dstNode *)
RECURSIVE ReachableInt(_, _, _)
ReachableInt(rootNode, dstNode, bound) ==
   IF bound = 0 THEN FALSE
   ELSE IF rootNode = dstNode THEN TRUE
   ELSE IF FSTree[rootNode] = {} THEN FALSE
   ELSE \E c \in FSTree[rootNode]:
        c # rootNode
        /\ ReachableInt(c, dstNode, bound - 1)

Reachable(rootNode, dstNode) ==
   ReachableInt(rootNode, dstNode, Cardinality(Nodes))

Transplant(srcParent, src, dstParent) ==
   [node \in Nodes |->
      IF node = srcParent THEN
         (FSTree[srcParent] \ {src} )
      ELSE IF node = dstParent THEN
         (FSTree[dstParent] \union {src})
      ELSE FSTree[node]
   ]

UnlockAll(t) ==
   [ thr \in Threads |->
      IF thr = t THEN {}
      ELSE ThreadHoldingLocks[thr]
   ]

(* Some helper predicates *)
IsChild(p, c) ==
   c \in FSTree[p]

Locked(t, node) ==
   node \in ThreadHoldingLocks[t]

AllLocked(t) ==
   ThreadHoldingLocks[t] =
   ThreadRequiredLocks[t]

ValidRename(srcParent, src, dstParent) ==
   (~(src \in FSTree[dstParent])) (* this limitation constraints the model...*)
 /\ IsChild(srcParent, src)
 /\ (~Reachable(src, dstParent))

CanRename(t, srcParent, src, dstParent) ==
   ThreadRequiredLocks[t] # {}
   /\ AllLocked(t)
   /\ IsChild(srcParent, src)

(* A thread is blocking if non of the next lock to
acquire is free.
*)
Blocking(t) ==
   \A node \in (ThreadRequiredLocks[t] \ ThreadHoldingLocks[t]):
      (\E thr \in Threads:
         (thr # t
         /\ node \in ThreadHoldingLocks[thr]))
(* Return a non-blocked free lock for thread t.
Note this function comes in pairs with the above one.
*)
PickNonBlocked(t) ==
   CHOOSE node \in
      (ThreadRequiredLocks[t] \ ThreadHoldingLocks[t]):
         (\A thr \in Threads:
             ~(node \in ThreadHoldingLocks[thr]))

(* Init states *)
RNInit ==
   ThreadHoldingLocks = [t \in Threads |-> {}]
   /\ ThreadRequiredLocks = [t \in Threads |-> {}]
   /\ FSTree = InitTree
   /\ Txn = [t \in Threads |-> <<"null", "null", "null">>]

(* Next state transitions
There are 3 of them:
1. begin txn for the rename
2. try-lock after transaction begin but not all locks acquired
3. commit txn to mutate the fs tree
*)
BeginRenameTxn(t, srcParent, src, dstParent) ==
   (* Enabling conditions *)
   ThreadHoldingLocks[t] = {}
   /\ ThreadRequiredLocks[t] = {}
   /\ ValidRename(srcParent, src, dstParent)

   (* Next state *)
   /\ FSTree' = FSTree
   /\ ThreadHoldingLocks' = ThreadHoldingLocks
   /\ ThreadRequiredLocks' =
      [ThreadRequiredLocks
         EXCEPT ![t] = {srcParent, src, dstParent}]
   /\ Txn' = [Txn EXCEPT ![t] = <<srcParent, src, dstParent>>]

CommitRenameTxn(t) ==
   (* Enabling conditions *)
   LET srcParent == Txn[t][1] IN
   LET src       == Txn[t][2] IN
   LET dstParent == Txn[t][3] IN
   CanRename(t, srcParent, src, dstParent)

   (* Next state:
      Atomically perform the rename with lock held and release the
      locks.
   *)
   /\ FSTree' = Transplant(srcParent, src, dstParent)
   /\ ThreadHoldingLocks' = UnlockAll(t)
   /\ ThreadRequiredLocks' =
       [ thr \in Threads |->
          IF thr = t THEN {}
          ELSE ThreadRequiredLocks[thr]
       ]
   /\ Txn' = Txn

TryLock(t) ==
   (* Enabling conditions *)
   ~AllLocked(t)
   (* Next state:
      Depending on if it is blocking or not
      If it is blocking, then release all the locks and retry
      else make a progress by picking a non-blocked one.
    *)
    /\ FSTree' = FSTree
    /\ ThreadRequiredLocks' = ThreadRequiredLocks
    /\ ( ThreadHoldingLocks' =
    IF Blocking(t) THEN UnlockAll(t)
    ELSE [ThreadHoldingLocks
            EXCEPT ![t] =
            ({PickNonBlocked(t)} \union ThreadHoldingLocks[t])
         ]
    )
    /\ Txn' = Txn

RNNext ==
  (\E t \in Threads: \E srcParent, src, dstParent \in Nodes:
     BeginRenameTxn(t, srcParent, src, dstParent))
  \/ (\E t \in Threads: TryLock(t))
  \/ (\E t \in Threads: CommitRenameTxn(t))

(* The complete spec *)
State == <<ThreadHoldingLocks, ThreadRequiredLocks, FSTree, Txn>>
RNSpec ==
   RNInit
   /\ [][RNNext]_State
   /\ (\A t \in Threads:
       WF_State(t))

(* Invariants *)
(* The only temporal property we would like to check is a state invariant:
*)
RNConserve ==
   \A node \in Nodes:
     Reachable(Root, node)

RNLoopFree ==
   ~(\E t1 \in Nodes: \E t2 \in Nodes:
        t1 # t2
        /\ (Reachable(t1, t2) /\ Reachable(t2, t1)))

=============================================================================
\* Modification History
\* Last modified Sun Dec 30 00:11:41 PST 2018 by junlongg
\* Created Sat Dec 29 15:04:06 PST 2018 by junlongg
