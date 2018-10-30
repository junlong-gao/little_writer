--------------------------- MODULE monitorWithSem ---------------------------
EXTENDS Integers

CONSTANT THREADS (* a set of running threads *)
CONSTANT SEMCOUNT (* limit the semaphore counts *)
       
(* Util functions *)       
RECURSIVE SetSize(_)
SetSize(set) == 
  IF set = {} THEN 0
  ELSE LET picked == CHOOSE x \in set : TRUE
       IN 1 + SetSize(set \ {picked}) 
    
RECURSIVE ChooseN(_, _)
ChooseN(N, set) == 
  IF N < 0 \/ N = 0 \/ set = {} THEN {}
  ELSE LET picked == CHOOSE x \in set : TRUE
       IN {picked} \union ChooseN(N, set \ {picked})

MinOfTwoInt(x, y) ==
   IF x < y THEN x
   ELSE y

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
There is no CV. The CV modelled here is implmented using sem,
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
Model semaphore as a counter and a set of waiters
*)
VARIABLE Sem
SemTypeOK == 
   DOMAIN Sem = {"counter", "waiters"}
   /\ Sem.counter \in Nat
   /\ Sem.waiters \subseteq THREADS
   
SemNonNeg ==
   ~ (Sem.counter < 0)
   /\ (~(Sem.waiters = {}) => Sem.counter = 0)
  
(*
Monitors only move threads around, not duplicating them.
*)
MonitorConservative ==
      ( Mutex.waiters \intersect Mutex.holder = {} )
   /\ ( Mutex.waiters \intersect CV.waiters = {} )
   /\ ( Mutex.holder \intersect CV.waiters = {} )
   
   /\ ( Mutex.waiters \intersect CV.signaled = {} )
   /\ ( Mutex.holder \intersect CV.signaled = {} )
   
   /\ ( Mutex.waiters \intersect Sem.waiters = {} )
   /\ ( Mutex.holder \intersect Sem.waiters = {} )

SemWaitAfterCVWaitReg ==
   Sem.waiters \subseteq CV.waiters


(**** BODY OF THE SPEC ****)
(* Some helper checkers *)  
(* logically blocked by CV *)    
MarkedCVWaiting(t) ==
   t \in CV.waiters
(* physically blocked by CV wait or in Lock wait queue *)
Blocked(t) ==
   t \in Sem.waiters
   \/ t \in Mutex.waiters

(* signal is done in two steps: register for signalling (required for
   the spec to track liveness) then resolve those by unblocking the
   threads that are physically blocked.
   
   Signal is made into semantically a single step because no other threads can
   make progress if a signal and broadcast is called before it is resolved.
*)
MarkedSignaled ==
   ~ (CV.signaled = {})
      
(* Init states *)
MSemInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]
     /\ Sem = [ counter |-> 0, waiters |-> {} ]
   
Lock(t) ==
    Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, Sem>>
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
   Sem.counter < SEMCOUNT
   /\ ~MarkedSignaled
   /\ ~(Mutex.waiters = {})
   /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, Sem>>

Unlock(t) ==
    Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV, Sem>>

(*
Wait cannot release lock and wait on sem atomically
*)
WaitA(t) ==
    Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ Mutex.holder = {t}
    /\ CV' = [ waiters |-> CV.waiters \union {t}, signaled |-> CV.signaled ]
    /\ Mutex' = [ holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED<<Sem>>

(*
The second step of the CV.Wait call involves the semaphore down:
1) if the sem counter is pos, just proceed and remove itself from the wait set
2) else, phyiscally wait using semaphore down.
*)    
WaitB(t) ==
    Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ MarkedCVWaiting(t) 
    /\ IF Sem.counter > 0
       THEN (
          Sem' = [ counter |-> Sem.counter - 1,
                   waiters |-> Sem.waiters ]
          /\ CV' = [ waiters |-> CV.waiters \ {t}, 
                     signaled |-> CV.signaled]
          /\ Mutex' = [ holder |-> {}, 
                        waiters |-> Mutex.waiters \union {t} ]
       )
       ELSE (
          Sem'= [ counter |-> Sem.counter, (* 0 *)
                  waiters |-> Sem.waiters \union {t} ]
          /\ UNCHANGED<<Mutex, CV>>
       )


Signal(t) ==
       Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ IF CV.waiters = {}
       THEN (
       UNCHANGED <<CV, Mutex, Sem>>
       )
       ELSE (
           LET waiter == CHOOSE waiter \in CV.waiters : TRUE
           IN CV'= [ waiters  |-> CV.waiters,
                     signaled |-> CV.signaled \union {waiter} ]
              /\ UNCHANGED<<Mutex, Sem>>             
       )

Broadcast(t) ==
       Sem.counter < SEMCOUNT
    /\ ~MarkedSignaled
    /\ ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union CV.waiters]
    /\ UNCHANGED <<Mutex, Sem>>

(*
Apply thw signal for all the threads that signal just delivered:
1. unblock the threads in the sem.waiters by using CV.signaled,
   they are unblocked from CV.wait and go to lock competition
2. if there is still count remains, add them to sem.counter.
   they can be used by threads registered for CV wait but have
   not called sem.down yet.
*)          
SignalResolve ==
         Sem.counter < SEMCOUNT
      /\ MarkedSignaled
      /\ (
          LET minVal == MinOfTwoInt(SetSize(Sem.waiters), SetSize(CV.signaled))
          IN LET pickedSubSet == ChooseN(minVal, Sem.waiters)
          IN LET reduced == SetSize(CV.signaled) - minVal 
          IN  
          /\ Mutex' = [ holder  |-> Mutex.holder,
                        waiters |-> Mutex.waiters \union pickedSubSet ]
          /\ CV' = [ waiters  |-> CV.waiters \ pickedSubSet, 
                     signaled |-> {} ]
          /\ Sem' = [ counter |-> Sem.counter + reduced,
                      waiters |-> Sem.waiters \ pickedSubSet]
      )

(**** The complete spec ****)
MSemNext ==
    LockResolve
    \/ SignalResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ WaitA(t) \/ WaitB(t)
       \/ Signal(t)
       \/ Broadcast(t)


MSemSpec ==
    MSemInit 
    /\ [][MSemNext]_<<CV, Mutex, Sem>> 
    /\ WF_<<CV, Mutex, Sem>>(MSemNext)

MonitorSpec == INSTANCE monitor 

MSemSpecTypeInv ==
       MutexTypeOK /\ CVTypeOK /\ SemTypeOK
    /\ CVMemoryLess /\ MutualExclusion /\ SemNonNeg
    /\ MonitorConservative
    /\ SemWaitAfterCVWaitReg
    
(**** SAFTY CONSTRAINT ****) 
MonitorSafety == 
    MonitorSpec!MonitorSafety
    /\ [][MSemSpecTypeInv]_<<CV, Mutex, Sem>> 
    
(**** LIVENESS CONSTRAINT ****)
CVSignalFairness == MonitorSpec!CVSignalFairness

THEOREM MSemSpec => MonitorSpec!MSpec
 
=============================================================================
\* Modification History
\* Last modified Tue Oct 30 06:08:14 PDT 2018 by junlongg
\* Created Mon Oct 29 00:00:19 PDT 2018 by junlongg
