------------------------------ MODULE monitor ------------------------------

CONSTANT THREADS (* a set of running threads *)

(* a mutex is a function (struct) maps from {holder, waiters} to 
   sets of threads *)
VARIABLE Mutex 
MutexDomain == 
   DOMAIN Mutex = {"holder", "waiters"}
   
MutualExclusion ==    
      Mutex.holder = {}
   \/ CHOOSE t \in THREADS : Mutex.holder = {t}
                   
(* a cv is a set of waiting threads *)
VARIABLE CV 
CVWaitingSet == 
    CV \subseteq THREADS
                              
(* Monitor only moves threads around, not duplicating them *)                  
MonitorConservative ==   
      Mutex.holder \subseteq THREADS
   /\ Mutex.waiters \subseteq THREADS
   /\ ( Mutex.waiters \intersect Mutex.holder = {} )
   /\ ( Mutex.waiters \intersect CV = {} /\  Mutex.holder \intersect CV = {})

(* this is the invariant the monitors, which is the conjuction of the above 4 invariants *)
MonitorTypeInv == 
    CVWaitingSet /\ MutexDomain /\ MutualExclusion /\ MonitorConservative       

(* init states *)
MInit ==    
        CV = {}
     /\ Mutex = [ holder |-> {}, waiters |-> {}]
         
(* what states are we interested in? *)
(* A thread is blocked if it appears in either of the waiting sets *)
Blocked(t) == 
   t \in CV
   \/ t \in Mutex.waiters
   
(*
- Lock(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   Add t to the waiters set. This is the relaxed locking semantics (still correct, but
   allows to express more subtle states in real world). See LockResolve step below.
  *)
Lock(t) ==   
    ~Blocked(t)
    /\ CV' = CV
    /\    Mutex'.holder = Mutex.holder 
    /\ Mutex'.waiters = Mutex.waiters \union {t}

(*
    This really does not depend on any thread t.
    If the system as entered the state that there is some waiter for lock and
    no one is holding it, automatically resolve it to one holder.
    
    This is required for both lock acquire and CV signal. For CV signal, we need to be able to
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
*)              
LockResolve == 
   IF (Mutex.waiters = {}) \/ ~(Mutex.holder = {})
   THEN CV' = CV /\ Mutex' = Mutex
   ELSE CHOOSE waiter \in Mutex.waiters :   Mutex'.holder = {waiter}
                                         /\ Mutex'.waiters = Mutex.waiters \ {waiter}
                                         /\ CV' = CV
 (* 
- Unlock(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot do anything but wait. 
   This will naturally leads to deadlock execution.
   
   If t is in the holder, remove it from holder set.
   Otherwise do nothing.
   
   (For example, unlocking a not owned lock is not doing anything meaningful to the system
    state's evolution. The actual runtime implementation can choose to panic or throw exception)
*)
Unlock(t) ==   
    ~Blocked(t)
     /\ CV' = CV
     /\ (
        IF Mutex.holder = {t}
        THEN    Mutex'.holder = {}
             /\ Mutex'.waiters = Mutex.waiters
        ELSE    Mutex' = Mutex
        )
                
(*
- Wait(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   otherwise, if t is not the holder of the lock, what should we do? Should we make this as
   an no op or invariant?
   
   If t is the holder of the lock, atomically move t from holder to CV. (!!)
*)
Wait(t) ==   
    ~Blocked(t)
      /\ IF Mutex.holder = {t}
         THEN     CV' = CV \union {t}
              /\  Mutex'.holder = {}
              /\  Mutex'.waiters = Mutex.waiters \union {t}
         ELSE
             (* What should I do here? POSIX says this is undefined.
        Let's try doing nothing. 
     *)
         CV' = CV
      /\ Mutex' = Mutex
(*
- Signal(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   If CV is empty, this is no op, otherwise, choose ANY of the thread in CV
   to move it to mutex.waiters
*)
Signal(t) == 
    ~Blocked(t)
    /\ IF CV = {} THEN CV' = CV /\ Mutex' = Mutex
       ELSE (
          CHOOSE waiter \in CV :   CV' = CV \ {waiter}
                                /\ Mutex'.holder = Mutex.holder
                                /\ Mutex'.waiters = Mutex.waiters \union { waiter }
       )

(*  
- Broadcast(t) 
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   If CV is empty, this is no op, otherwise, choose ALL of the thread in CV
   to move it to mutex.waiters
*)
Broadcast(t) == 
    ~Blocked(t)
    /\ CV' = {}
    /\ Mutex'.holder = Mutex.holder
    /\ Mutex'.waiters = Mutex.waiters \union CV
                
=============================================================================
\* Modification History
\* Last modified Sun Oct 28 17:43:21 PDT 2018 by junlongg
\* Created Sun Oct 28 16:06:17 PDT 2018 by junlongg
