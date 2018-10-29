------------------------------ MODULE monitor ------------------------------

CONSTANT THREADS (* a set of running threads *)

(* a mutex is a function (struct) maps from {holder, waiters} to
   sets of threads *)
VARIABLE Mutex
MutexDomain ==
   DOMAIN Mutex = {"holder", "waiters"}

MutualExclusion ==
      Mutex.holder = {}
   \/ \E t \in THREADS : Mutex.holder = {t}

(*
CV is modeled as two sets, first being the waiters and the second
being the signaled.
*)
VARIABLE CV
CVDomain ==
    DOMAIN CV = {"waiters", "signaled"}

(*
conditional variables are memoryless.
If a thread appears in signaled, it must has called wait before.
If a thread is not in the wait set, it must not appear as signaled. i.e. signalling
a not waiting thread has no effects for future wait.
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

(*
This is the invariant of the monitors,
which is the conjuction of the above 4 invariants
*)
MonitorTypeInv ==
       CVDomain /\ CVMemoryLess
    /\ MutexDomain /\ MutualExclusion
    /\ MonitorConservative

(* Init states *)
MInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]

(* What states are we interested in? *)

(*
A thread is blocked if it appears in either of the waiting sets

The negation of it is used as a part of the enabling condition.
If t is in the mutex waiter or cv waiter, then this is no op since a thread in
the waiter state cannot  do anything but wait.
This will naturally leads to deadlock execution if everyone is no longer enabled.

Curiously, we only have one lock in the model, and we do not allow locking
when the thread is the owner of the lock. Thus we cannot result in this trivial
deadlock.

Indeed, we have mode interesting properties to check regarding to CV, not mutex.
*)
Blocked(t) ==
   t \in CV.waiters
   \/ t \in Mutex.waiters

(*
- Lock(t) where t is in threads
   Enabling condition:
   1. not Blocked(t).
   2. t is not the current lock holder

   Next step:
   Add t to the waiters set. This is the relaxed locking semantics (still correct, but
   allows to express more subtle states in real world). See LockResolve step below.
*)
Lock(t) ==
    ~Blocked(t)
    /\ ~(t \in Mutex.holder)
    /\ CV' = CV
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

(*
    This really does not depend on any thread t.
    If the system has entered the state that there is some waiter for lock and
    no one is holding it, automatically resolve it to one waiter.

    This is required for both lock acquiring and CV signal. For CV signal, we need to be able to
    express the state where a thread just gets woken up from wait, but not yet become the owner
    of the lock.
    Instead of duplicating the lock logic, we allow a transient state where lock is not held
    by anyone and there are a few waiters. And system can choose to resolve this state at any
    time automatically as long as this enable condition is met.

    This is really more closer to the real world behavior, where if we see a thread calling
    "lock" we don't assume it acquires the lock immediately. We go into the reasoning of
     1) there is no holder, so it becomes the owner,
     2) there is a holder, so it waits and becomes the owner later.
     But this is semantically the same same as
     1) Regardless of holder, becomes waiter first,
     2) If/until there is not holder, become holder.

     This is another reason why putting mutex and CV together as monitors makes a
     more realistic model.

     Enabling condition:
     There are some waiters and no holder of the lock.

     Next step:
     Pick anyone to become the holder of the lock and remove it from waiter queue.
*)
LockResolve ==
   ~(Mutex.waiters = {})
   /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV>>

(*
- Unlock(t) where t is in threads
   Enabling condition:
   t is not blocked and is the holder of the lock.

   Next step:
   If t is in the holder, remove it from holder set.

   (For example, unlocking a not owned lock is not doing anything meaningful to the system
    state's evolution. The actual runtime implementation can choose to panic or throw exception)
*)
Unlock(t) ==
    ~Blocked(t)
    /\ Mutex.holder = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV>>

(*
- Wait(t) where t is in threads
   Enabling condition:
   t not blocked
   t is the holder of the lock (!! POSIX, we just exclude that from possible
   states in the model checking that call wait without holding lock. They are
   forbidden in POSIX anyway.)

   Next step:
   Atomically move t from holder to CV. (!!)

   This step implies, if some thread appears in the CV wait set, then
   we can conclude there exists some previous state, where this thread
   called Wait, but not yet woken up by some signal. We attach this semantics
   to this step so that we can express the liveness constraint of the spec.
*)
Wait(t) ==
    ~Blocked(t)
    /\ Mutex.holder = {t}
    /\ CV' = [ waiters |-> CV.waiters \union {t}, signaled |-> CV.signaled ]
    /\ Mutex' = [ holder |-> {}, waiters |-> Mutex.waiters]

(*
- Signal(t) where t is in threads
   Enabling condition:
   t not blocked.

   Next step:
   If CV is empty, this is no op, otherwise, choose ANY of the thread in CV
   to move it to mutex.waiters.
   Curiously it is not required to hold lock as part of the enabling conditions.
*)
Signal(t) ==
    ~Blocked(t)
    /\ IF CV.waiters = {}
       THEN
       UNCHANGED <<CV, Mutex>>
       ELSE
       LET waiter == CHOOSE waiter \in CV.waiters : TRUE
       IN    CV' = [ waiters  |-> CV.waiters,
                     signaled |-> CV.signaled \union { waiter }]
          /\ UNCHANGED <<Mutex>>


(*
- Broadcast(t)
   Enabling condition:
   t not blocked.

   Next step:
   If CV is empty, this is no op, otherwise, choose ALL of the thread in CV
   to move it to mutex.waiters
   Curiously it is not required to hold lock as part of the enabling conditions.
*)
Broadcast(t) ==
    ~Blocked(t)
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union CV.waiters]
    /\ UNCHANGED <<Mutex>>

(*
This is added to allow us to express the fact that
"A thread waited in some state and then is signaled in some state by another thread".

In POSIX, there is no requirement on whether the signaled thread should immediately
get lock or appear in some position in the lock queue (Mesa semantics). A signalled
thread cannot put itself on wait again before it is resolved from sleeping (woken)
and attempts to get the lock. Therefore, it is allowed to have some delay between
getting signaled and being put on lock's wait set.

Enabling condition:
signaled set not empty

Step:
Remove these signaled from waiters in CV and put them
into waiters of Lock.
*)
SignalResolve ==
      ~ (CV.signaled = {})
      /\  Mutex' = [ holder  |-> Mutex.holder,
                     waiters |-> Mutex.waiters \union CV.signaled ]
      /\  CV' = [ waiters |-> CV.waiters \  CV.signaled, signaled |-> {} ]

(*
MNext describes how system may evolve given any current state.
*)
MNext ==
    LockResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ Wait(t)
       \/ Signal(t)
       \/ Broadcast(t)

(*
MSpec describes the allowed behaviors as well as excluding behaviors containing
trivial infinite stuttering steps.
*)
MSpec ==
    MInit /\ [][MNext]_<<CV, Mutex>> /\ WF_<<CV, Mutex>>(MNext)

(*
This is one of the non-trivial liveness property any monitor spec must satisfy.
If some thread waited and then is signaled, it must eventually wake up and try to
acquire the lock again.

Monitor provides this fundamental guarantee so that different threads can
use these monitors to communicate each other like:
T1: wait() on some condition
T2: change the condition and communicate to T1 via signal()/broadcast().
*)
CVSignalFairness ==
    \A t \in THREADS:
        (t \in CV.signaled) ~> (t \in Mutex.waiters)

THEOREM MSpec => []MonitorTypeInv
=============================================================================
\* Modification History
\* Last modified Sun Oct 28 23:16:45 PDT 2018 by junlongg
\* Created Sun Oct 28 16:06:17 PDT 2018 by junlongg
