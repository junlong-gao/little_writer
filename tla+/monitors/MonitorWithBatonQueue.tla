------------------------ MODULE MonitorWithBatonQueue ------------------------

EXTENDS FiniteSets, Integers, Sequences, Monitor

(**** UTILITIES ****)

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

(*
Model a queue of threads that emplaced their local baton
*)

VARIABLE BatonQ
BatonTypeOK ==
     (Len(BatonQ) < Cardinality(THREADS) \/ Len(BatonQ) = Cardinality(THREADS))
   /\ ( \A i \in 1..Len(BatonQ) : BatonQ[i] \in THREADS )

BatonSignal(Baton) ==
   IF Baton.waiters = {}
   THEN [ counter |-> Baton.counter + 1,
          waiters |-> {} ]
   ELSE
     LET picked == CHOOSE x \in Baton.waiters : TRUE
     IN [ counter |-> 0,
          waiters |-> Baton.waiters \ { picked }  ]

BatonWait(Baton, t) ==
   IF Baton.counter = 0
   THEN [ counter |-> 0,
          waiters |-> Baton.waiters \union { t } ]
   ELSE
        [ counter |-> Baton.counter - 1,
          waiters |-> Baton.waiters ]

(*
Model the baton created by each thread. Note in the implementation it is
impossible for a thread to create more than 2 baton since it cannot call
CV.Wait() while sleeping.
*)

VARIABLE ThreadLocalBaton
ThreadLocalBatonTypeOK ==
   DOMAIN ThreadLocalBaton \subseteq THREADS
   /\ \A t \in THREADS :
          ((ThreadLocalBaton[t].counter = 0) \/ (ThreadLocalBaton[t].counter = 1))
       /\ (~(ThreadLocalBaton[t].waiters = {}) => ThreadLocalBaton[t].counter = 0)
       /\ ((Cardinality(ThreadLocalBaton[t].waiters) = 0
          \/ Cardinality(ThreadLocalBaton[t].waiters) = 1))

BatonConservative ==
      MonitorConservative
   /\ (\A t \in THREADS :
          /\ ( Mutex.waiters \intersect ThreadLocalBaton[t].waiters = {} )
          /\ ( Mutex.holder \intersect ThreadLocalBaton[t].waiters = {} )
   )
   (* The size of the baton queue no larger than the size of threads
      registered for CV wait. *)
   /\ ~(Len(BatonQ) > Cardinality(CV.waiters))

   (* And those are physically blocked by baton is a subset
      of the threads registered for CV wait.

      Expression {ThreadLocalBaton[t].waiters : t \in THREADS} is a set of thread
      sets, not a plain thread set, thus it has to be flattened.
   *)
   /\ FlattenSet({ThreadLocalBaton[t].waiters : t \in THREADS})
         \subseteq CV.waiters
   /\ (\A t \in THREADS:
         ThreadLocalBaton[t].counter > 0 => t \in CV.signaled)

(**** HELPFUL STATE CHECKS ****)

(* check if a thread is physically blocked *)
Blocked(t) ==
      t \in ThreadLocalBaton[t].waiters
   \/ t \in Mutex.waiters

(**** THE STATE TRANSITIONS ****)

(**** Init States ****)
MBatonQInit ==
        MInit
     /\ BatonQ = <<>>
     /\ ThreadLocalBaton = [t \in THREADS |-> [counter |-> 0, waiters |-> {}]]

Lock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, BatonQ, ThreadLocalBaton>>
    /\ Mutex' = [ holder |-> Mutex.holder,
                  waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
      ~(Mutex.waiters = {}) /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, BatonQ, ThreadLocalBaton>>

Unlock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ Mutex' = UnlockMutex(Mutex)
    /\ UNCHANGED <<CV, BatonQ, ThreadLocalBaton>>

Wait(t) ==
      ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ LET localBaton == [counter |-> 0,
                        waiters |-> {}]
       IN
       CV'    = [ waiters  |-> CV.waiters \union {t},
                  signaled |-> CV.signaled ]
    /\ Mutex' = UnlockMutex(Mutex)
    /\ BatonQ'  = Push(t, BatonQ)
    /\ ThreadLocalBaton' = [ThreadLocalBaton EXCEPT ![t] = localBaton]

Wait_fast_wake(t) ==
       ~Blocked(t)
    /\ MarkedCVWaiting(t)
    /\ ThreadLocalBaton[t].counter > 0
    /\ ThreadLocalBaton' = [ThreadLocalBaton
          EXCEPT ![t] = BatonWait(ThreadLocalBaton[t], t) ]
    /\ Mutex' = [ holder  |-> Mutex.holder,
                  waiters |-> Mutex.waiters \union {t}]
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled \ {t} ]
    /\ UNCHANGED<<BatonQ>>

Wait_slow_sleep(t) ==
       ~Blocked(t)
    /\ MarkedCVWaiting(t)
    /\ ThreadLocalBaton[t].counter = 0
    /\ ~(t \in CV.signaled)
    /\ ThreadLocalBaton' = [ThreadLocalBaton
          EXCEPT ![t] = BatonWait(ThreadLocalBaton[t], t) ]
    /\ UNCHANGED<<Mutex, CV, BatonQ>>

Wait_slow_wake(t) ==
       ~Blocked(t)
    /\ MarkedCVWaiting(t)
    /\ t \in CV.signaled
    /\ ThreadLocalBaton[t].counter = 0
    /\ Mutex' = [ holder  |-> Mutex.holder,
                  waiters |-> Mutex.waiters \union {t} ]
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled \ {t} ]
    /\ UNCHANGED<<ThreadLocalBaton, BatonQ>>

Signal(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ ~ (BatonQ = <<>>)
    /\ LET waiting == Back(BatonQ)
       IN CV'= [ waiters  |-> CV.waiters,
                 signaled |-> CV.signaled \union {waiting} ]
          /\ ThreadLocalBaton' =
             [ThreadLocalBaton
             EXCEPT
             ![waiting] = BatonSignal(ThreadLocalBaton[waiting]) ]
          /\ BatonQ' = Pop(BatonQ)
          /\ UNCHANGED<<Mutex>>

Broadcast(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ LET waked == {BatonQ[i] : i \in 1..Len(BatonQ)}
       IN CV' = [ waiters  |-> CV.waiters,
                  signaled |-> CV.signaled \union waked]
          /\ BatonQ' = <<>>
          /\ ThreadLocalBaton' = [ thr \in THREADS |->
             IF thr \in waked
             THEN BatonSignal(ThreadLocalBaton[thr])
             ELSE  ThreadLocalBaton[thr] ]
          /\ UNCHANGED <<Mutex>>


(**** The Complete Spec ****)
MBatonQNext ==
       LockResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ Wait(t)
       \/ Wait_fast_wake(t)
       \/ Wait_slow_sleep(t)
       \/ Wait_slow_wake(t)
       \/ Signal(t)
       \/ Broadcast(t)

MBatonQSpec ==
    MBatonQInit
    /\ [][MBatonQNext]_<<CV, Mutex, BatonQ, ThreadLocalBaton>>
    /\ WF_<<CV, Mutex, BatonQ, ThreadLocalBaton>>(LockResolve)
    /\ \A t \in THREADS :
        WF_<<CV, Mutex, BatonQ, ThreadLocalBaton>>(Wait_fast_wake(t))
        /\ WF_<<CV, Mutex, BatonQ, ThreadLocalBaton>>(Wait_slow_wake(t))

(**** Implementation Specific Invariant ****)
MBatonQSpecInv ==
       MonitorInv
    /\ ThreadLocalBatonTypeOK
    /\ BatonConservative

=============================================================================
