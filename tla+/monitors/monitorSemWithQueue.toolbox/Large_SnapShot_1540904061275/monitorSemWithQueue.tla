------------------------ MODULE monitorSemWithQueue ------------------------

EXTENDS Integers, Sequences

(**** UTILITIES ****)  
RECURSIVE SetSize(_)
SetSize(set) == 
  IF set = {} THEN 0
  ELSE LET picked == CHOOSE x \in set : TRUE
       IN 1 + SetSize(set \ {picked}) 
            
(*Pop Back*)
Pop(seq) == 
  [j \in 1..(Len(seq)-1) |->  seq[j] ]

RECURSIVE PopN(_, _)
PopN(n, queue) ==
   IF n = 0 \/ Len(queue) = 0 THEN queue
   ELSE PopN(n - 1, Pop(queue))
   
RECURSIVE FlattenSet(_)
FlattenSet(ss) ==
   IF ss = {} 
   THEN {}
   ELSE 
   LET picked == CHOOSE x \in ss : TRUE
   IN picked \union FlattenSet(ss \ {picked}) 
       
(* get back *)
Back(seq) == 
  seq[Len(seq)]
   
(*Push front*)
Push(v, seq) ==
  [j \in 1..Len(seq) + 1 |->  IF j = 1 THEN v ELSE seq[j - 1] ]
  
(* get front *) 
Front(seq) == seq[1]               
                         
CONSTANT THREADS (* a set of running threads *)

(**** MODEL VARIABLES ****)   
(* a mutex is a function (struct) maps from {holder, waiters} to
   sets of threads *)
VARIABLE Mutex
MutexTypeOK ==
   DOMAIN Mutex = {"holder", "waiters"}
   /\ Mutex.holder \subseteq THREADS
   /\ Mutex.waiters \subseteq THREADS

MutualExclusion ==
      Mutex.holder = {}
   \/ \E t \in THREADS : Mutex.holder = {t}

(*
There is no CV. The CV modelled here is implmented using a queue of sem,
see wait and signal/broadcast below.
*)
VARIABLE CV
CVTypeOK ==
    DOMAIN CV = {"waiters", "signaled"}
    /\ CV.waiters \subseteq THREADS
    /\ CV.signaled \subseteq THREADS

CVMemoryLess ==
   CV.signaled \subseteq CV.waiters

(*
Model a queue of threads that emplaced their local semaphore
*)
VARIABLE SemQ   
SemTypeOK ==
     (Len(SemQ) < SetSize(THREADS) \/ Len(SemQ) = SetSize(THREADS))
   /\ ( \A i \in 1..Len(SemQ) : SemQ[i] \in THREADS )

(*
Model the semaphore created by each thread. note in the implementation
it is impossible for a thread to create more than 2 semaphore since it
cannot call CV.Wait() while sleeping.
*)
VARIABLE ThreadLocalSem 
ThreadLocalSemTypeOK ==
   DOMAIN ThreadLocalSem \subseteq THREADS
   /\ \A t \in THREADS :
          ~(ThreadLocalSem[t].counter < 0) /\ ~(ThreadLocalSem[t].counter > 1)
       /\ (~(ThreadLocalSem[t].waiters = {}) => ThreadLocalSem[t].counter = 0)

(*
Monitors only move threads around, not duplicating them.
*)
MonitorConservative ==
      ( Mutex.waiters \intersect Mutex.holder = {} )
      
   /\ ( Mutex.waiters \intersect CV.waiters = {} )
   /\ ( Mutex.holder \intersect CV.waiters = {} )
   
   /\ ( Mutex.waiters \intersect CV.signaled = {} )
   /\ ( Mutex.holder \intersect CV.signaled = {} )
   
   /\ (\A t \in THREADS :
          /\ ( Mutex.waiters \intersect ThreadLocalSem[t].waiters = {} )
          /\ ( Mutex.holder \intersect ThreadLocalSem[t].waiters = {} )
   )
   (* the size of the semaphore queue no larger than the size of threads
      registered for CV wait *)
   /\ (Len(SemQ) < SetSize(CV.waiters) \/ Len(SemQ) = SetSize(CV.waiters))
   
   (* and those that are physically blocked by semaphore is a subset
      of the threads registered for CV wait
   *)
   /\ FlattenSet({ThreadLocalSem[t].waiters : t \in THREADS}) \subseteq CV.waiters

(**** HELPFUL STATE CHECKS ****)
(* State Assertions *) 
(* check if a thread is physically blocked *)     
Blocked(t) ==
      t \in ThreadLocalSem[t].waiters
   \/ t \in Mutex.waiters
   
(* waiting is done in two steps. A thread is logically blocked
if it calls cv wait and before calling sem down, and is physically blocked
if it ends up in a sem queue *)    
MarkedCVWaiting(t) ==
   t \in CV.waiters

(* 
Since signal is done in two steps: signal/broadcast, then resolve
Use this to stop the world to only complete the signal if it is marked,
otherwise TLC liveness checker will assert this thread signal can be starved
forever.
*)
MarkedSignaled ==
   ~ (CV.signaled = {})

(*
If a thread's local sem is 1, it is considered in transient state
and the system must resolve these threads first by allowing them
unblock from CV wait.
Otherwise TLC liveness checker will assert this thread can be starved
forever.
*)
MarkedUped ==
   \E t \in THREADS :
      ThreadLocalSem[t].counter = 1
      
(**** THE STATE TRANSITIONS ****)   
(* Init states *)
MSemQInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]
     /\ SemQ = <<>>
     /\ ThreadLocalSem = [t \in THREADS |-> [counter |-> 0, waiters |-> {}]]
   

Lock(t) ==
       ~MarkedSignaled /\ ~MarkedUped
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, SemQ, ThreadLocalSem>>
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
      ~MarkedSignaled /\ ~MarkedUped
   /\ ~(Mutex.waiters = {}) /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

Unlock(t) ==
       ~MarkedSignaled /\ ~MarkedUped
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ Mutex.holder = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

(*
Wait cannot release lock and wait on sem atomically
*)
WaitA(t) ==
       ~MarkedSignaled /\ ~MarkedUped
    /\  ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ LET localSem == [counter |-> 0, 
                        waiters |-> {}]
       IN
       CV'    = [ waiters  |-> CV.waiters \union {t}, 
                  signaled |-> CV.signaled ]
    /\ Mutex' = [ holder  |-> {}, 
                  waiters |-> Mutex.waiters]
    /\ SemQ'  = Push(t, SemQ)
    /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = localSem] 

(* 
physically sleep, and wait for a signal resolved 
otherwise signalResolve will put this back to mutex wait queue
*)       
WaitB_1(t) ==
       ~MarkedSignaled /\ ~MarkedUped
    /\ ~Blocked(t) /\ MarkedCVWaiting(t) 
    /\ ThreadLocalSem[t].counter = 0
    /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = 
                                 [ counter |-> 0,
                                   waiters |-> ThreadLocalSem[t].waiters \union {t}
                                 ]
                               ] 
    /\ UNCHANGED<<Mutex, CV, SemQ>>
(*
Marked up, thus this concurrent wait immediately completes with another signal
*)
WaitB_2(t) ==
    ~MarkedSignaled /\ MarkedUped
    /\ ~Blocked(t) /\ MarkedCVWaiting(t) 
    /\ ThreadLocalSem[t].counter = 1
    /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = 
                                 [ counter |-> 0,
                                   waiters |-> {}
                                 ]
                               ] 
    /\ Mutex' = [ holder  |-> Mutex.holder, 
                  waiters |-> Mutex.waiters \union {t} ]
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled ]
    /\ UNCHANGED<<SemQ>>  
      
Signal(t) ==
       ~MarkedSignaled /\ ~MarkedUped      
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ IF SemQ = <<>>
       THEN (
           UNCHANGED <<CV, Mutex, SemQ, ThreadLocalSem>>
       )
       ELSE (
           LET waiting == Back(SemQ)
           IN CV'= [ waiters  |-> CV.waiters,
                     signaled |-> CV.signaled \union {waiting} ]
                 (* let signal resolve pop it of the queue *)
              /\ UNCHANGED<<Mutex, SemQ, ThreadLocalSem>>             
       )

Broadcast(t) ==
       ~MarkedSignaled /\ ~MarkedUped      
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union {SemQ[i] : i \in 1..Len(SemQ)}]
    /\ UNCHANGED <<Mutex, SemQ, ThreadLocalSem>>


(*
Signal resolve unblocks those signaled on the queue by resetting
their semaphore.
These binary semaphore are either 
1) down'ed, thus up here unblocks them
2) up'ed, thus cancels with the down of the caller.

This is still not an accurate modelling though. It would be
nice to have it here handle up and resolve some of the blocked,
and leave some counter to be 1 and let the waiters to call down
and make progress.
*)             
SignalResolve ==
         MarkedSignaled
      /\ LET physicall_blocked == { t \in CV.signaled : t \in ThreadLocalSem[t].waiters }
         IN (* remove those physically blocked from CV wait since their Wait() completes here. *)
            (* for the rest, they are up'ed and will be resolved concurrently in WaitB_2 *)
            (* we have to deque all of them during signal/broadcast, since in thread local context
               a thread does not know its position in queue
            *)
               CV' = [ waiters  |-> CV.waiters \ physicall_blocked, 
                       signaled |-> {} ]
            /\ SemQ' = PopN(SetSize(CV.signaled), SemQ)
            (* for those not physically blocked, mark them up'ed *)
            /\ ThreadLocalSem' = [ t \in THREADS |-> 
                             IF t \in CV.signaled 
                             THEN ( IF t \in physicall_blocked
                                    THEN [ counter |-> 0,
                                           waiters |-> {} ]
                                    ELSE [ counter |-> 1,
                                           waiters |-> {} ]
                                    )
                             ELSE ThreadLocalSem[t]
                            ]
      (* for  those physically blocked, mark them to be unblocked thus completes the wait for them *)
      /\ Mutex' = [ holder |-> Mutex.holder,
                    waiters |-> Mutex.waiters \union physicall_blocked ]

(**** THE COMPLETE SPEC ****)
MSemQNext ==
       LockResolve \/ SignalResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ WaitA(t) \/ WaitB_1(t) \/ WaitB_2(t)
       \/ Signal(t)
       \/ Broadcast(t)

MSemQSpec ==
    MSemQInit 
    /\ [][MSemQNext]_<<CV, Mutex, SemQ, ThreadLocalSem>> 
    /\ WF_<<CV, Mutex, SemQ, ThreadLocalSem>>(MSemQNext)

MonitorSpec == INSTANCE monitor

MonitorInv ==
       MutexTypeOK /\ CVTypeOK /\ SemTypeOK /\ ThreadLocalSemTypeOK
    /\ CVMemoryLess /\ MutualExclusion
    /\ MonitorConservative

(**** SAFETY CONSTRAINT ****)
MonitorSafety == 
   MonitorSpec!MonitorSafety
   /\ [][MonitorInv]_<<CV, Mutex, SemQ, ThreadLocalSem>>

(**** LIVENESS CONSTRAINT ****)
CVSignalFairness == MonitorSpec!CVSignalFairness

THEOREM MSemQSpec => MonitorSpec!MSpec

=============================================================================
\* Modification History
\* Last modified Tue Oct 30 05:49:03 PDT 2018 by junlongg
\* Created Mon Oct 29 13:23:27 PDT 2018 by junlongg
