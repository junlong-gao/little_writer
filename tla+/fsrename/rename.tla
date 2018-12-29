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
   enabling condition is invalidated.
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

*)
=============================================================================
\* Modification History
\* Last modified Sat Dec 29 15:11:37 PST 2018 by junlongg
\* Created Sat Dec 29 15:04:06 PST 2018 by junlongg
