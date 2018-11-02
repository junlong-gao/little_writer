------------------------------ MODULE monitor ------------------------------

CONSTANT THREADS (* a set of running threads *)

(*
Spec of Mutex and CV.

Mutex is modeled as two sets, first being the holder set and the second
being the waiter set.

CV is also modeled as two sets, first being the waiters and the second
being the signaled.
*)

VARIABLE Mutex
MutexDomain ==
   DOMAIN Mutex = {"holder", "waiters"}

MutexTypeOK ==
   DOMAIN Mutex = {"holder", "waiters"}
   /\ Mutex.holder \subseteq THREADS
   /\ Mutex.waiters \subseteq THREADS

MutualExclusion ==
      Mutex.holder = {}
   \/ \E t \in THREADS : Mutex.holder = {t}

VARIABLE CV
CVTypeOK ==
    DOMAIN CV = {"waiters", "signaled"}
    /\ CV.waiters \subseteq THREADS
    /\ CV.signaled \subseteq THREADS

CVDomain ==
    DOMAIN CV = {"waiters", "signaled"}

(*
Conditional variables are memoryless.  If a thread appears in CV.signaled, it
must have called CV.Wait() before.  If a thread is not in the wait set, it must
not appear in the signaled set. i.e. Signalling a not waiting thread has no
effects for future wait.
*)

CVMemoryLess ==
   CV.signaled \subseteq CV.waiters

(*
Monitors only move threads around, not duplicating them.
*)
MonitorConservative ==
      Mutex.holder \subseteq THREADS
   /\ Mutex.waiters \subseteq THREADS
   /\ CV.waiters \subseteq THREADS
   /\ CV.signaled \subseteq THREADS
   /\ ( Mutex.waiters \intersect Mutex.holder = {} )
   /\ ( Mutex.waiters \intersect CV.waiters = {} )
   /\ ( Mutex.holder \intersect CV.waiters = {} )
   /\ ( Mutex.waiters \intersect CV.signaled = {} )
   /\ ( Mutex.holder \intersect CV.signaled = {} )

MarkedCVWaiting(t) ==
   t \in CV.waiters

(**** Init states ****)
MInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]

(*
This is a non-trivial safety property for CV wait and signal: for every thread
that received signal, it must have called Wait() on CV before.
*)

CVWaitCorrectness ==
    \A t \in THREADS:
       (t \in CV'.signaled) => (t \in CV.signaled \/ t \in CV.waiters)

(*
This is one of the non-trivial liveness property any monitor spec must satisfy.
If some thread waited and then is signaled, it must eventually wake up and try
to acquire the lock again.

Monitors provide this fundamental guarantee so that different threads can
communicate with each other like:
T1: wait() on some condition
T2: change the condition and communicate with T1 via signal()/broadcast().
*)

CVSignalFairness ==
    \A t \in THREADS:
        (t \in CV.signaled) ~> (t \in Mutex.waiters)

(* Temporal Properties to Check *)
MonitorSafety ==
   [][CVWaitCorrectness]_<<CV, Mutex>>

MonitorLiveness ==
    CVSignalFairness

(* Invariants to Check *)
MonitorInv ==
       CVDomain /\ CVMemoryLess
    /\ MutexDomain /\ MutualExclusion
    /\ MonitorConservative

=============================================================================
\* Modification History
\* Last modified Thu Nov 01 00:33:26 PDT 2018 by junlongg
\* Created Sun Oct 28 16:06:17 PDT 2018 by junlongg
