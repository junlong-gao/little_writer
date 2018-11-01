------------------------ MODULE monitorSemWithQueue ------------------------

EXTENDS Integers, Sequences, monitor

(**** UTILITIES ****)  
RECURSIVE SetSize(_)
SetSize(set) == 
  IF set = {} THEN 0
  ELSE LET picked == CHOOSE x \in set : TRUE
       IN 1 + SetSize(set \ {picked}) 
            
(*Pop Back*)
Pop(seq) == 
  [j \in 1..(Len(seq)-1) |->  seq[j] ]
   
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
                         
(**** MODEL VARIABLES ****)   
(* a mutex is a function (struct) maps from {holder, waiters} to
   sets of threads *)

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
SemConservative ==
      MonitorConservative
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
   /\ (\A t \in THREADS:
         ThreadLocalSem[t].counter > 0 => t \in CV.signaled)

(**** HELPFUL STATE CHECKS ****)
(* State Assertions *) 
(* check if a thread is physically blocked *)     
Blocked(t) ==
      t \in ThreadLocalSem[t].waiters
   \/ t \in Mutex.waiters
   

(**** THE STATE TRANSITIONS ****)   
(* Init states *)
MSemQInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]
     /\ SemQ = <<>>
     /\ ThreadLocalSem = [t \in THREADS |-> [counter |-> 0, waiters |-> {}]]
   

Lock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, SemQ, ThreadLocalSem>>
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
      ~(Mutex.waiters = {}) /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

Unlock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t) 
    /\ Mutex.holder = {t}
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV, SemQ, ThreadLocalSem>>

(*
Wait cannot release lock and wait on sem atomically
*)
WaitA(t) ==
      ~Blocked(t) /\ ~MarkedCVWaiting(t)
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
    
WaitB_fast(t) ==
       ~Blocked(t) 
    /\ MarkedCVWaiting(t) 
    /\ ThreadLocalSem[t].counter > 0
    /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = 
                                 [ counter |-> 0,
                                   waiters |-> {}
                                 ]
                               ] 
    /\ Mutex' = [ holder  |-> Mutex.holder, 
                  waiters |-> Mutex.waiters \union {t}] 
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled \ {t} ]                          
    /\ UNCHANGED<<SemQ>>
(* 
physically sleep, and wait for a signal resolved 
otherwise signalResolve will put this back to mutex wait queue
*)       
WaitB_sleep(t) ==
       ~Blocked(t) 
    /\ MarkedCVWaiting(t) 
    /\ ThreadLocalSem[t].counter = 0
    /\ ~(t \in CV.signaled)
    /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![t] = 
                                 [ counter |-> 0,
                                   waiters |-> ThreadLocalSem[t].waiters \union {t}
                                 ]
                               ] 
    /\ UNCHANGED<<Mutex, CV, SemQ>>

WaitB_wake(t) ==   
       ~Blocked(t) 
    /\ MarkedCVWaiting(t) 
    /\ t \in CV.signaled
    /\ ThreadLocalSem[t].counter = 0
    /\ Mutex' = [ holder  |-> Mutex.holder, 
                  waiters |-> Mutex.waiters \union {t} ]
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled \ {t} ]
    /\ UNCHANGED<<ThreadLocalSem, SemQ>>  

SemUp(Sem) ==
   IF Sem.waiters = {}
   THEN [ counter |-> 1,
          waiters |-> {} ]
   ELSE
     LET picked == CHOOSE x \in Sem.waiters : TRUE
     IN [ counter |-> 0,
          waiters |-> Sem.waiters \ { picked }  ] 
               
Signal(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ ~ (SemQ = <<>>)
    /\ LET waiting == Back(SemQ)
       IN CV'= [ waiters  |-> CV.waiters,
                 signaled |-> CV.signaled \union {waiting} ]
          /\ ThreadLocalSem' = [ThreadLocalSem EXCEPT ![waiting] = SemUp(ThreadLocalSem[waiting]) ] 
          /\ SemQ' = Pop(SemQ)
          /\ UNCHANGED<<Mutex>>             

Broadcast(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ LET waked == {SemQ[i] : i \in 1..Len(SemQ)}
       IN CV' = [ waiters  |-> CV.waiters,
                  signaled |-> CV.signaled \union waked]
          /\ SemQ' = <<>>
          /\ ThreadLocalSem' = [ thr \in THREADS |->
             IF thr \in waked
             THEN SemUp(ThreadLocalSem[thr])
             ELSE  ThreadLocalSem[thr] ]
          /\ UNCHANGED <<Mutex>>


(**** THE COMPLETE SPEC ****)
MSemQNext ==
       LockResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ WaitA(t) \/ WaitB_fast(t) \/ WaitB_sleep(t) \/ WaitB_wake(t)
       \/ Signal(t)
       \/ Broadcast(t)

MSemQSpec ==
    MSemQInit 
    /\ [][MSemQNext]_<<CV, Mutex, SemQ, ThreadLocalSem>> 
    /\ \A t \in THREADS :
        WF_<<CV, Mutex, SemQ, ThreadLocalSem>>(WaitB_wake(t))
        /\ WF_<<CV, Mutex, SemQ, ThreadLocalSem>>(WaitB_fast(t))

MSemQSpecInv ==
       MonitorInv
    /\ SemConservative

=============================================================================
\* Modification History
\* Last modified Thu Nov 01 00:46:11 PDT 2018 by junlongg
\* Created Mon Oct 29 13:23:27 PDT 2018 by junlongg
