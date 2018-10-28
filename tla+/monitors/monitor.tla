------------------------------ MODULE monitor ------------------------------

CONSTANT THREADS (* a set of running threads *)

(* a cv is a set of waiting threads *)
VARIABLE CV 

(* a mutex is a function (struct) maps from {holder, waiters} to 
   sets of threads *)
VARIABLE Mutex 

MTypeOK ==    DOMAIN Mutex = {"holder", "waiters"}
           /\ (\A t \in Mutex.holder : t \in THREADS )
           /\ (\A t \in Mutex.waiters : t \in THREADS )
           /\ ( Mutex.waiters \intersect Mutex.holder = {} )
           /\ (\A t \in CV : t \in THREADS )

(* init states *)
MInit ==    CV = {}
         /\ Mutex = [ holder |-> {}, waiters |-> {}]
         
(* what states are we interested in? *)

Blocked(t) ==    t \in CV
              \/ t \in Mutex.waiters
(*
- Lock(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   if Mutex.holder is empty, put it as holder
   else add it to the waiter set.
  *)
Lock(t) ==   ~Blocked(t)
           /\ CV' = CV
           /\ (
                IF Mutex.holder = {} 
                THEN    Mutex'.holder = {t} 
                     /\ Mutex'.waiter = Mutex.waiter
                ELSE    Mutex'.holder = Mutex.holder 
                     /\ Mutex'.waiter = Mutex.waiter \union {t}
              )   
 (* 
- Unlock(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   if t is in the holder, remove it from holder set.
   otherwise do nothing.
   
   (for example, unlocking a not owned lock is not doing anything meaningful to the system
    state's evolution. The actual runtime implementation can choose to panic or throw exception)

- Wait(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   otherwise, if t is not the holder of the lock, what should we do? we should make this as
   an no op or invariant?
   
   if t is the holder of the lock, atomically move t from holder to CV

- Signal(t) where t is in threads
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   if CV is empty, this is no op, otherwise, choose ANY of the thread in CV
   to move it to mutex.waiters
   
- Broadcast(t) 
   ~Blocked(t):
   if t is in the mutex waiter or cv waiter, then this is no op since a thread in 
   the waiter state cannot  do anything but wait. 
   This will naturally leads to deadlock execution.
   
   if CV is empty, this is no op, otherwise, choose ALL of the thread in CV
   to move it to mutex.waiters
*)
=============================================================================
\* Modification History
\* Last modified Sun Oct 28 16:45:00 PDT 2018 by junlongg
\* Created Sun Oct 28 16:06:17 PDT 2018 by junlongg
