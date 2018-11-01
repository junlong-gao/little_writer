--------------------------- MODULE monitorWithSem ---------------------------
(*
This spec shows a wrong implementation for using semaphore implementing
monitors.
*)

EXTENDS Integers, monitor

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
   
VARIABLE WaiterCount
VARIABLE SignalCount
CounterTypeOK ==
   WaiterCount \in Nat
   /\ SignalCount \in Nat

(**** BODY OF THE SPEC ****)
(* Some helper checkers *)
(* logically blocked by CV *)

(* physically blocked by CV wait or in Lock wait queue *)
Blocked(t) ==
   t \in Sem.waiters
   \/ t \in Mutex.waiters

(*
IsTrivialWait(t) ==
   {t} = THREADS \ Sem.waiters

Do we need this? No. TLA+ can easily generate a behavior where two of the
threads starts waiting one after another, but there is no liveness violation here.
Liveness says system must resolve if there is a signal delivered to a waiting thread,
and does not care cases where no signal is delivered at all.
*)

(* Init states *)
MSemInit ==
        CV = [ waiters |-> {}, signaled |-> {} ]
     /\ Mutex = [ holder |-> {}, waiters |-> {} ]
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
    /\ Mutex' = [holder |-> {}, waiters |-> Mutex.waiters]
    /\ UNCHANGED <<CV, Sem, WaiterCount, SignalCount>>

(*
Wait cannot release lock and wait on sem atomically
*)
WaitA(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t}
    /\ CV' = [ waiters |-> CV.waiters \union {t},
               signaled |-> CV.signaled ]
    /\ Mutex' = [ holder |-> {},
                  waiters |-> Mutex.waiters]
    /\ UNCHANGED<<Sem, SignalCount>>
    /\ WaiterCount' = WaiterCount + 1

(*
reduce the set size by 1 by removing any element determinisitcally
if val is not in the set
*)
Reduce(set, val) ==
    IF SetSize(set) = 0 THEN set
    ELSE IF val \in set THEN set \ {val}
         ELSE LET picked == CHOOSE x \in set : TRUE
              IN set \ {picked}
(*
pass through
*)
WaitB_fast(t) ==
       ~Blocked(t)
    /\ Sem.counter > 0
    /\ MarkedCVWaiting(t)
    /\ Sem' = [ counter |-> Sem.counter - 1,
                waiters |-> Sem.waiters ]
    (* decrease both the counters *)
    /\ CV' = [ waiters |-> CV.waiters \ {t},
               signaled |-> Reduce(CV.signaled, t) ] (* <---- this is why the impl is wrong, it is a counter *)
    /\ WaiterCount' = WaiterCount - 1
    /\ SignalCount' = SignalCount - 1
    /\ Mutex' = [ holder |-> {},
                  waiters |-> Mutex.waiters \union {t} ]

(*
physically sleep
*)
WaitB_sleep(t) ==
       ~Blocked(t)
    /\ ~(t \in CV.signaled) /\ MarkedCVWaiting(t)
    /\ Sem.counter = 0
    /\ Sem' = [ counter |-> 0,
                waiters |-> Sem.waiters \union {t} ]
    /\ UNCHANGED<<CV, Mutex, WaiterCount, SignalCount>>
(*
wake up from sem down
*)
WaitB_wake (t) ==
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
Apply signal for all the threads that signal just delivered:
1. unblock the threads in the sem.waiters by using CV.signaled,
   they are unblocked from CV.wait and go to lock competition
2. if there is still count remains, add them to sem.counter.
   they can be used by threads registered for CV wait but have
   not called sem.down yet.
*)
ComputeSem(Signaled) ==
  LET minVal == MinOfTwoInt(SetSize(Sem.waiters), SetSize(Signaled))
  IN LET pickedSubSet == ChooseN(minVal, Sem.waiters)
  IN LET reduced == SetSize(Signaled) - minVal
  IN [ counter |-> Sem.counter + reduced,
       waiters |-> Sem.waiters \ pickedSubSet]

Signal(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ (WaiterCount > 0 /\ WaiterCount > SignalCount)
    /\ LET waiter == CHOOSE waiter \in (CV.waiters \ CV.signaled) : TRUE
       IN CV'= [ waiters  |-> CV.waiters,
                 signaled |-> CV.signaled \union {waiter} ]
          /\ SignalCount' = SignalCount + 1
          /\ Sem' = ComputeSem({waiter})
          /\ UNCHANGED<<Mutex, WaiterCount>>


Broadcast(t) ==
       ~Blocked(t) /\ ~MarkedCVWaiting(t)
    /\ Mutex.holder = {t} (* posix does not require that, but... *)
    /\ CV' = [ waiters  |-> CV.waiters,
               signaled |-> CV.signaled \union (CV.waiters \ CV.signaled)]
    /\ Sem' = ComputeSem(CV.waiters \ CV.signaled)
    /\ UNCHANGED <<Mutex, WaiterCount>>
    /\ SignalCount' = SetSize(CV.waiters)


(**** The complete spec ****)
MSemNext ==
    LockResolve
    \/ \E t \in THREADS :
       \/ Lock(t)
       \/ WaitA(t)
       \/ WaitB_fast(t) \/ WaitB_sleep(t) \/ WaitB_wake(t)
       \/ Signal(t)
       \/ Broadcast(t)

MSemSpec ==
    MSemInit
    /\ [][MSemNext]_<<CV, Mutex, Sem, SignalCount, WaiterCount>>
    /\ \A t \in THREADS:
        WF_<<CV, Mutex, Sem, SignalCount, WaiterCount>>(WaitB_fast(t))
        /\ WF_<<CV, Mutex, Sem, SignalCount, WaiterCount>>(WaitB_wake(t))

MSemSpecInv ==
    MonitorInv
    /\ SemTypeOK /\ SemNonNeg /\ SemWaitAfterCVWaitReg
    /\ CounterTypeOK
    /\ WaiterCount = SetSize(CV.waiters)
    /\ SignalCount = SetSize(CV.signaled)

=============================================================================
\* Modification History
\* Last modified Thu Nov 01 00:43:36 PDT 2018 by junlongg
\* Created Mon Oct 29 00:00:19 PDT 2018 by junlongg
