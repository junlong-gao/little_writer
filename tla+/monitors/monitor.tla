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
A cv is modeled as a set of waiting threads.
*)
VARIABLE CV
CVWaitingSet ==
    CV \subseteq THREADS

(*
Monitors only move threads around, not duplicating them.
*)
MonitorConservative ==
      Mutex.holder \subseteq THREADS
   /\ Mutex.waiters \subseteq THREADS
   /\ ( Mutex.waiters \intersect Mutex.holder = {} )
   /\ ( Mutex.waiters \intersect CV = {} /\  Mutex.holder \intersect CV = {})

(*
This is the invariant of the monitors,
which is the conjuction of the above 4 invariants
*)
MonitorTypeInv ==
    CVWaitingSet /\ MutexDomain /\ MutualExclusion /\ MonitorConservative

(* Init states *)
MInit ==
        CV = {}
     /\ Mutex = [ holder |-> {}, waiters |-> {}]

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
   t \in CV
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
    /\ ~(t \in Mutex["holder"])
    /\ CV' = CV
    /\ Mutex' = [ holder |-> Mutex["holder"], waiters |-> Mutex["waiters"] \union {t} ]

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
   ~(Mutex["waiters"] = {})
   /\ (Mutex["holder"] = {})
   /\ LET waiter == CHOOSE waiter \in Mutex["waiters"] : TRUE
      IN  Mutex' = [holder |-> {waiter},
                   waiters |-> Mutex["waiters"] \ {waiter}]
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
    /\ Mutex["holder"] = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex["waiters"]]
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
*)
Wait(t) ==
    ~Blocked(t)
    /\ Mutex.holder = {t}
    /\ CV' = CV \union {t}
    /\ Mutex' = [ holder |-> {}, waiters |-> Mutex["waiters"]]

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
    /\ IF CV = {}
       THEN
       UNCHANGED <<CV, Mutex>>
       ELSE
       LET waiter == CHOOSE waiter \in CV : TRUE
       IN    CV' = CV \ {waiter}
          /\ Mutex' = [holder |-> Mutex["holder"],
                       waiters |-> Mutex["waiters"] \union { waiter }]

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
    /\ CV' = {}
    /\ Mutex' = [holder |-> Mutex["holder"],
                 waiters |-> Mutex["waiters"] \union CV]

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

MSpec ==
    MInit /\ [][MNext]_<<CV, Mutex>>

THEOREM MSpec => []MonitorTypeInv
=============================================================================
\* Modification History
\* Last modified Sun Oct 28 20:57:11 PDT 2018 by junlongg
\* Created Sun Oct 28 16:06:17 PDT 2018 by junlongg
