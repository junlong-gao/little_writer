--------------------------- MODULE MonitorWithSem ---------------------------
(*
This spec shows a wrong implementation for using semaphore implementing
monitors.
*)

EXTENDS FiniteSets, Integers, Monitor

(* Util functions *)
RECURSIVE ChooseN(_, _)
ChooseN(N, set) ==
  IF N < 0 \/ N = 0 \/ set = {} THEN {}
  ELSE LET picked == CHOOSE x \in set : TRUE
       IN {picked} \union ChooseN(N, set \ {picked})

MinOfTwoInt(x, y) ==
   IF x < y THEN x
   ELSE y

(**** MODEL VARIABLES ****)

(*
Model semaphore as a counter and a set of waiters.
*)

VARIABLE Sem
SemTypeOK ==
   DOMAIN Sem = {"counter", "waiters"}
   /\ Sem.counter \in Nat
   /\ Sem.waiters \subseteq THREADS

SemNonNeg ==
   ~ (Sem.counter < 0)
   /\ (~(Sem.waiters = {}) => Sem.counter = 0)

SemWaitAfterCVWaitReg ==
   Sem.waiters \subseteq CV.waiters

SemCountConstraintSmall ==
   Sem.counter < 2

SemCountConstraintLarge ==
   Sem.counter < 10

VARIABLE WaiterCount
VARIABLE SignalCount
CounterTypeOK ==
   WaiterCount \in Nat
   /\ SignalCount \in Nat

(**** BODY OF THE SPEC ****)

(* Physically blocked by CV wait or in Mutex wait queue *)

Blocked(t) ==
   t \in Sem.waiters
   \/ t \in Mutex.waiters

(**** Init States ****)
MSemInit ==
        MInit
     /\ Sem = [ counter |-> 0, waiters |-> {} ]
     /\ WaiterCount = 0
     /\ SignalCount = 0

Lock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ ~(t \in Mutex.holder)
    /\ UNCHANGED<<CV, Sem, WaiterCount, SignalCount>>
    /\ Mutex' = [ holder |-> Mutex.holder, waiters |-> Mutex.waiters \union {t} ]

LockResolve ==
      ~(Mutex.waiters = {})
   /\ (Mutex.holder = {})
   /\ LET waiter == CHOOSE waiter \in Mutex.waiters : TRUE
      IN  Mutex' = [holder |-> {waiter},
                    waiters |-> Mutex.waiters \ {waiter}]
   /\ UNCHANGED <<CV, Sem, WaiterCount, SignalCount>>

Unlock(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ Mutex' = UnlockMutex(Mutex)
    /\ UNCHANGED <<CV, Sem, WaiterCount, SignalCount>>

(*
Wait cannot release lock and wait on sem atomically
*)

Wait(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ CV' = [ waiters |-> CV.waiters \union {t},
               signaled |-> CV.signaled ]
    /\ Mutex' = UnlockMutex(Mutex)
    /\ UNCHANGED<<Sem, SignalCount>>
    /\ WaiterCount' = WaiterCount + 1

(*
Reduce the set size by 1 by removing any element deterministically if val is
not in the set.
*)

Reduce(set, val) ==
    IF Cardinality(set) = 0 THEN set
    ELSE IF val \in set THEN set \ {val}
         ELSE LET picked == CHOOSE x \in set : TRUE
              IN set \ {picked}
(*
Pass through since semaphore count is positive.
*)

Wait_fast_wake(t) ==
       ~Blocked(t)
    /\ Sem.counter > 0
    /\ MarkedCVWaiting(t)
    /\ Sem' = [ counter |-> Sem.counter - 1,
                waiters |-> Sem.waiters ]
    (* decrease both the counters *)
    /\ CV' = [ waiters |-> CV.waiters \ {t},
    (* This is why the implementation is wrong: signal can be stolen and the
    liveness constraint is violated.
    Note it is very difficult to think about this case in the original C++
    implementation as there is no set tracked, only the counters. In the model
    both sets and the counters are tracked and the counter = set size invariant
    must be maintained, thus the error is apparent here.
    *)
               signaled |-> Reduce(CV.signaled, t) ]
    /\ WaiterCount' = WaiterCount - 1
    /\ SignalCount' = SignalCount - 1
    /\ Mutex' = [ holder |-> {},
                  waiters |-> Mutex.waiters \union {t} ]

(*
Physically sleep as the count is 0.
*)

Wait_slow_sleep(t) ==
       ~Blocked(t)
    /\ ~(t \in CV.signaled) /\ MarkedCVWaiting(t)
    /\ Sem.counter = 0
    /\ Sem' = [ counter |-> 0,
                waiters |-> Sem.waiters \union {t} ]
    /\ UNCHANGED<<CV, Mutex, WaiterCount, SignalCount>>

(*
Wake up from semaphore down.
*)

Wait_slow_wake(t) ==
       ~(t \in Mutex.waiters)
    /\ t \in CV.signaled /\ MarkedCVWaiting(t)
    /\ Sem.counter = 0
    (* signal resolve called up and unblocked this thread *)
    /\ UNCHANGED<<Sem>>
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> CV.signaled \ {t} ]
    /\ WaiterCount' = WaiterCount - 1
    /\ SignalCount' = SignalCount - 1
    /\ Mutex' = [ holder |-> {},
                  waiters |-> Mutex.waiters \union {t} ]

(*
Apply signals for all the threads that the signals were just delivered to:
1. Unblock the threads in the sem.waiters.
   They will be unblocked from CV.wait and go to lock competition

2. If there is still count remains, add them to sem.counter.
   They can be used by threads registered for CV wait but have
   not called sem.down yet.
*)

ComputeSem(Signaled) ==
  LET minVal == MinOfTwoInt(Cardinality(Sem.waiters), Cardinality(Signaled))
  IN LET pickedSubSet == ChooseN(minVal, Sem.waiters)
  IN LET reduced == Cardinality(Signaled) - minVal
  IN [ counter |-> Sem.counter + reduced,
       waiters |-> Sem.waiters \ pickedSubSet]

Signal(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    (*
    POSIX does not require that, but to show this implementation is wrong even
    with lock held calling signal.
     *)
    /\ Mutex.holder = {t}
    /\ (WaiterCount > 0 /\ WaiterCount > SignalCount)
    /\ LET waiter == CHOOSE waiter \in (CV.waiters \ CV.signaled) : TRUE
       IN CV'= [ waiters  |-> CV.waiters,
                 signaled |-> CV.signaled \union {waiter} ]
          /\ SignalCount' = SignalCount + 1
          /\ Sem' = ComputeSem({waiter})
          /\ UNCHANGED<<Mutex, WaiterCount>>


Broadcast(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    (*
    POSIX does not require that, but to show this implementation is wrong even
    with lock held calling broadcast.
     *)
    /\ Mutex.holder = {t}
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union (CV.waiters \ CV.signaled)]
    /\ Sem' = ComputeSem(CV.waiters \ CV.signaled)
    /\ UNCHANGED <<Mutex, WaiterCount>>
    /\ SignalCount' = Cardinality(CV.waiters)


(**** The Complete Spec ****)

MSemNext ==
    LockResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ Wait(t)
       \/ Wait_fast_wake(t) \/ Wait_slow_sleep(t) \/ Wait_slow_wake(t)
       \/ Signal(t)
       \/ Broadcast(t)

MSemSpec ==
    MSemInit
    /\ [][MSemNext]_<<CV, Mutex, Sem, SignalCount, WaiterCount>>
    /\ WF_<<CV, Mutex, Sem, SignalCount, WaiterCount>>(LockResolve)
    /\ \A t \in THREADS:
        WF_<<CV, Mutex, Sem, SignalCount, WaiterCount>>(Wait_fast_wake(t))
        /\ WF_<<CV, Mutex, Sem, SignalCount, WaiterCount>>(Wait_slow_wake(t))

(**** Implementation Specific Invariant ****)

MSemSpecInv ==
    MonitorInv
    /\ SemTypeOK /\ SemNonNeg /\ SemWaitAfterCVWaitReg
    /\ CounterTypeOK
    /\ WaiterCount = Cardinality(CV.waiters)
    /\ SignalCount = Cardinality(CV.signaled)

=============================================================================
