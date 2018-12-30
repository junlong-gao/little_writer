------------------------------- MODULE rename -------------------------------
(* Rename: Transplant a subtree.
The caller is responsible for making sure the transplant dose not introduce
loops and/or leak objects.

The model only concerns Rename(srcParent, src, dstParent), that is, no new name
in dstParent.

This model demonstrates a wrong implementation.

XXX TODO: Check race-free. Before commit, each thread must have locked all the
nodes used for the transaction.

The problem is thus apparent: by the time the remote file server receives this
request, the tree topology may have changed so that the loop can be introduced
due to this rename.
This is can be easily seen by comparing the ValidRename used in pre-txn phase
and CanRename in the commit phase. Note how CanRename tries its best to verify
"everything is right" after try-lock.
*)


EXTENDS TLC, Integers, FiniteSets
CONSTANT InitTree, Root, Nodes, Threads
VARIABLE
         (* Track the required locks *)
         ThreadHoldingLocks,
         ThreadRequiredLocks,
         (* The fstree *)
         FSTree,
         (* Track each thread's pending txn parameters *)
         Txn

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
    /\ (\A t1 \in Threads: \A t2 \in Threads:
         t1 # t2 =>
         ThreadHoldingLocks[t1]
         \intersect ThreadHoldingLocks[t2] = {})

(* Some helper functions *)
(* Check the graph is loop free and use a bound to limit recursion
depth. For a tree of n nodes, any path cannot be longer than n - 1.
*)
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
   (~(src \in FSTree[dstParent]))
 /\ IsChild(srcParent, src)
 /\ (~Reachable(src, dstParent))

CanRename(t, srcParent, src, dstParent) ==
   ThreadRequiredLocks[t] # {}
   /\ AllLocked(t)
   (* before commit, "make sure everything is right" *)
   /\ IsChild(srcParent, src)

(* A thread is blocking if non of the next lock to acquire is free.
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
RNConserve ==
   \A node \in Nodes:
     Reachable(Root, node)

RNLoopFree ==
   ~(\E n1 \in Nodes: \E n2 \in Nodes:
        n1 # n2
        /\ (Reachable(n1, n2) /\ Reachable(n2, n1)))

=============================================================================
