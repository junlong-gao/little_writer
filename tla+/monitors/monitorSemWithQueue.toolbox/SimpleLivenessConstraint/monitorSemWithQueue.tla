------------------------ MODULE monitorSemWithQueue ------------------------

EXTENDS Integers, Sequences

(* Util functions *)  
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
   ELSE PopN(n - 1, Tail(queue))
   
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


MonitorInv ==
       MutexTypeOK /\ CVTypeOK /\ SemTypeOK /\ ThreadLocalSemTypeOK
    /\ CVMemoryLess /\ MutualExclusion
    /\ MonitorConservative

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

(* Since signal is done in two steps: signal/broadcast, then resolve
Use this to stop the world to only complete the signal if it is marked
*)
MarkedSignaled ==
   ~ (CV.signaled = {})
   
(* Init states *)
MSemQInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]
     /\ SemQ = <<>>
     /\ ThreadLocalSem = [t \in THREADS |-> [counter |-> 0, waiters |-> {}]]
   

Lock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t) /\ ~MarkedSignaled
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, SemQ, ThreadLocalSem>>
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
      ~MarkedSignaled
   /\ ~(Mutex.waiters = {}) /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

Unlock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t) /\ ~MarkedSignaled
    /\ Mutex.holder = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

(*
Wait cannot release lock and wait on sem atomically
*)
WaitA(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t) /\ ~MarkedSignaled
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

    
WaitB(t) ==
       ~Blocked(t) /\ MarkedCVWaiting(t) /\ ~MarkedSignaled
    /\ LET localSem == ThreadLocalSem[t]
       IN
       IF localSem.counter > 0
       (* if the sem counter is pos (a signal has already resolved this thread,
          sem.down immediately gets unblocked and gets put into mutex
          queue *)
       THEN (
             CV' = [ waiters  |-> CV.waiters \ {t}, 
                     signaled |-> CV.signaled ]
          /\ Mutex' = [ holder  |-> {}, 
                        waiters |-> Mutex.waiters \union {t} ]
          /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = [counter |-> 0, waiters |-> {}]] 
          /\ UNCHANGED<<SemQ>>
       )
       ELSE (
       (* physically sleep, and wait for a signal resolved *)
             ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = 
                                 [ counter |-> 0,
                                   waiters |-> ThreadLocalSem[t].waiters \union {t}
                                 ]
                               ] 
          /\ UNCHANGED<<Mutex, CV, SemQ>>
       )


Signal(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)  /\ ~MarkedSignaled
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ IF SemQ = <<>>
       THEN (
           UNCHANGED <<CV, Mutex, SemQ, ThreadLocalSem>>
       )
       ELSE (
           LET waiting == Front(SemQ)
           IN CV'= [ waiters  |-> CV.waiters,
                     signaled |-> CV.signaled \union {waiting} ]
                 (* let signal resolve pop it of the queue *)
              /\ UNCHANGED<<Mutex, SemQ, ThreadLocalSem>>             
       )

Broadcast(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)  /\ ~MarkedSignaled
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union {SemQ[i] : i \in 1..Len(SemQ)}]
    /\ UNCHANGED <<Mutex, SemQ, ThreadLocalSem>>


             
SignalResolve ==
         MarkedSignaled
      /\ LET physically_blocked == { t \in THREADS : t \in CV.signaled /\ t \in ThreadLocalSem[t].waiters }
         IN CV' = [ waiters  |-> CV.waiters \ physically_blocked, 
                    signaled |-> {} ]
            /\ SemQ' = PopN(SetSize(CV.signaled), SemQ)
            /\ ThreadLocalSem' = [ t \in THREADS |-> 
                                   IF t \in CV.signaled 
                                THEN 
                                   (IF ThreadLocalSem[t].waiters = {}
                                    THEN 
                                    [ counter |-> 1,
                                      waiters |-> {} ]
                                    ELSE
                                    [ counter |-> 0,
                                      waiters |-> {} ]
                                    )
                                ELSE ThreadLocalSem[t]
                            ]
      /\ Mutex' = [ holder |-> Mutex.holder,
                    waiters |-> Mutex.waiters \union physically_blocked]

(*
MNext describes how system may evolve given any current state.
*)
MSemQNext ==
       LockResolve \/ SignalResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ WaitA(t) \/ WaitB(t)
       \/ Signal(t)
       \/ Broadcast(t)

(*
MSpec describes the allowed behaviors as well as excluding behaviors containing
trivial infinite stuttering steps.
*)
MSemQSpec ==
    MSemQInit 
    /\ [][MSemQNext]_<<CV, Mutex, SemQ, ThreadLocalSem>> 
    /\ WF_<<CV, Mutex, SemQ, ThreadLocalSem>>(MSemQNext)

MonitorSpec == INSTANCE monitor

CVSignalFairness == MonitorSpec!CVSignalFairness

THEOREM MSemQSpec => MonitorSpec!MSpec

=============================================================================
\* Modification History
\* Last modified Mon Oct 29 16:21:39 PDT 2018 by junlongg
\* Created Mon Oct 29 13:23:27 PDT 2018 by junlongg
