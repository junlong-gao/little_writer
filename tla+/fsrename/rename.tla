------------------------------- MODULE rename -------------------------------
(*
Rename:
Transplant a subtree.

Consider a rooted tree T:
S1:
    T
   / \
  /   \
A       B
|       |
|       |
C       D
|       |
|       |
E       F

Rename operation takes exactly 3 parameters:
Rename(srcParent, srcObj, dstParent)
Enabling condition:
   srcObj is a child of srcParent,                                   (E1)
/\ srcParent != dstParent
/\ there is no path from srcObj to dstParent (see below)

It transplants srcObj into dstParent if srcParent != dstParent, and remove
the linkage from srcPrent to srcObj and add linkage dstParent to srcObj.

For example,
Rename(A, C, F) transforms S1 into S1':
    T
   / \
  /   \
A       B
        |
        |
        D
        |
        |
        F
        |
        |
        C
        |
        |
        E

This operation is called Rename() because usually the destination name is
different than the original srcObj name. Because in the model we do not
distinguish between the obj name and the obj internal representation(inode
number, for example), so we do not concern with renaming at the dst here. The
file name uniquely identifies the object.

Also, looping is forbidden:
Rename(B, D, E) transforms S1' into S1'':
    T
   / \
  /   \
A       B


        D<-|
        |  |
        |  |
        F  |
        |  |
        |  |
        C  |
        |  |
        |  |
        E  |
        |__|

This will cause objects D F C and E not reachable from root T. This this Rename
will be forbidden.


Concurrency.
If we would like this operation to be thread safe. i.e. we can have many
concurrent Rename. Certain locking is require to keep the tree in sane state:
C1) Conservation.
   There is no object added nor object removed before or after each rename
   operation. Rename only transplants objects.
   (modify the model to allow actual renaming).
C2) Reachability.
   For all object in the tree, there exists a path from root to the tree before
   and after each rename operation. Duration the rename it may not be tree.
C3) Progress.
   If a rename started, it must eventually complete or fail because of the
   enabling condition is invalidated. (do not check it)
C4) Race-free.
   It is impossible to have two threads accessing the same tree node
   concurrently, where at least one of them is write.

To model concurrency, we add additional parameter to Rename() call to identify
which thread is calling Rename()
Therefore, a rename usually consists of multiple state transitions:
S1. Locking phase (srcParent, srcObj, dstParent):
   Enabling condition E1. Note this does not mean the thread is reading these
   file system object without locking. Instead, enabling condition is to filter
   out impossible rename calls in read life.
   Next state: try locking. This could involve more sub-steps and more state
   transitions for try lock. But try lock must succeed (C3).
   the result state is getting 3 locks.                       (E2)
S2. Additional locking phase
   Enabling condition E1 and with all the locks held (E2).
   This is the state where the thread can begin transplant. This may involve
   handling unlink opened file (but all fs objects are unique, so not possible
   in this model), lock more nodes (lowest common ancestor? we do not do that
   now.) and so on.
   Next state: get more locks or some book keeping for the locked nodes.
S3. Transplant phase.
   Enabling condition E1 E2 and the more conditions required from S2.
   This is really the easy part. We modify the linkage in the tree
   representation. C4 is enforced since we only modifying the nodes we have
   already acquired the lock.

...And then we will see C2 is violated.

#States:
## Model Parameters:
- The initial tree
A tree is simply a graph with root:
Root: T
Nodes: {A, B, C, D, E, F, T}
Graph:{
T:{A, B},
A:{C},
C:{E},
B:{D},
D:{F},
}
- The threads
{t1, t2}

##Variables:
- The current tree.
(incidentally, root cannot change.)
init: input graph

- the locks held by each thread
{
t1 -> {A, C, E}
t2 -> {}
}
init: {t1->{}, t2->{}}
- the locks required by each thread:
{
t1 -> {A, C, E}
t2 -> {}
}
init: {t1->{}, t2->{}}
- perhaps more bookkeeping states.
?

#Helpers
Reachability(node):
  rec if node is T, true
      else if there exists p such that
           p is a parent of node and Reachability(p), then true
           else false

Transplant(srcParent, srcObj, dstParent):
   # modify the current tree and return a new tree

How to model try lock?
Enabling condition: t.held != t.required.
next state:
if any of the lock in t.required \ t.held is in some other t's held, release
all locks
else acquire t.held = t.required
Note this modeling will result in liveness issue in (C3). But it will not have
any correctness issue.

Then the enabling condition for rename is simple
1. all required locks are held
2. the source dst follows the constraint
the use Transplant to update the tree.

Start simple, and refine the model.
*)

CONSTANT InitTree, Root, Nodes, Threads
VARIABLE ThreadHoldingLocks, ThreadRequiredLocks, FSTree

RNTypeOK ==
(* Validate model parameters: *)
       Root \in Nodes
    /\ InitTree \in [Nodes -> SUBSET(Nodes)]
(* Validate runtime variables: *)
    /\ ThreadHoldingLocks \in
         [Threads -> SUBSET(Nodes)]
    /\ ThreadRequiredLocks \in
         [Threads -> SUBSET(Nodes)]
    (* each thread is either try-locking or got all the required locks: *)
    /\ (\A t \in Threads:
       ThreadHoldingLocks[t] \subseteq ThreadRequiredLocks[t])
    /\ FSTree \in [Nodes -> SUBSET(Nodes)]

(* Some helper functions *)
RECURSIVE Reachable(_, _)
Reachable(rootNode, dstNode) ==
   IF rootNode = dstNode THEN TRUE
   ELSE IF (\E p \in Nodes: dstNode \in FSTree[p]
            /\  Reachable(rootNode, p))
   THEN TRUE
   ELSE FALSE

Transplant(srcParent, src, dstParent) ==
   [node \in Nodes |->
      IF node = srcParent
      THEN FSTree[node] \ {src}
      ELSE IF node = dstParent
      THEN FSTree[node] \union {src}
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

CanFormCycle(src, dstParent) ==
   Reachable(src, dstParent)

AllLocked(t) ==
   ThreadHoldingLocks[t] =
   ThreadRequiredLocks[t]

ValidRename(srcParent, src, dstParent) ==
   IsChild(srcParent, src)
 /\ \lnot CanFormCycle(src, dstParent)

CanRename(t, srcParent, src, dstParent) ==
   AllLocked(t)
   /\ srcParent \in ThreadHoldingLocks[t]
   /\ src \in ThreadHoldingLocks[t]
   /\ dstParent \in ThreadHoldingLocks[t]

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
            \lnot (node \in ThreadHoldingLocks[thr]))

(* Init states *)
RNInit ==
   ThreadHoldingLocks = [t \in Threads |-> {}]
   /\ ThreadRequiredLocks = [t \in Threads |-> {}]
   /\ FSTree = InitTree

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

CommitRenameTxn(t, srcParent, src, dstParent) ==
   (* Enabling conditions *)
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

TryLock(t) ==
   (* Enabling conditions *)
   \lnot AllLocked(t)
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
            PickNonBlocked(t) \union ThreadHoldingLocks[t]
         ]
    )

RNNext ==
  (\E t \in Threads: \E srcParent, src, dstParent \in Nodes:
     BeginRenameTxn(t, srcParent, src, dstParent))
  \/ (\E t \in Threads: TryLock(t))
  \/ (\E t \in Threads: \E srcParent, src, dstParent \in Nodes:
     CommitRenameTxn(t, srcParent, src, dstParent))

(* The complete spec *)
RNSpec ==
   RNInit
   /\ [][RNNext]_<<ThreadHoldingLocks, ThreadRequiredLocks, FSTree>>
   /\ (\A t \in Threads:
       WF_<<ThreadHoldingLocks, ThreadRequiredLocks, FSTree>>(t))

(* Invariants *)
(* The only temporal property we would like to check is a state invariant:
*)
RNSafe ==
   \A node \in Nodes:
     Reachable(Root, node)
=============================================================================
\* Modification History
\* Last modified Sat Dec 29 20:00:18 PST 2018 by junlongg
\* Created Sat Dec 29 15:04:06 PST 2018 by junlongg
