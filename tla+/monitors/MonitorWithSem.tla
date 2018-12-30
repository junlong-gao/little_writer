--------------------------- MODULE MonitorWithSem ---------------------------
(*
This spec shows a wrong implementation for using semaphore implementing
monitors.
*)

EXTENDS FiniteSets, Integers
CONSTANT THREADS (* a set of running threads *)

VARIABLE ThreadState
VARIABLE MutexHolder

VARIABLE SemCount
VARIABLE SemWaiters
VARIABLE WaiterCount
VARIABLE WaitPrepared

SemCountConstraintSmall ==
   SemCount < 2

SemCountTypeOK == SemCount \in Nat
SemWaitersTypeOK ==
   SemWaiters \subseteq THREADS
   /\ ~(SemWaiters={}) => (SemCount = 0)
WaiterCountTypeOK == WaiterCount \in Nat
WaitPreparedTypeOK ==
   WaitPrepared \subseteq THREADS
   /\ (\A t \in WaitPrepared: (ThreadState[t] /= "Running"))
   /\ (\A t \in WaitPrepared: ~(t \in MutexHolder))
   /\ (\A t \in WaitPrepared: ~(t \in SemWaiters))

SemCVMutexLock(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {}
   /\ MutexHolder' = {t}
   /\ UNCHANGED<<ThreadState, SemCount, SemWaiters, WaiterCount, WaitPrepared>>

SemCVMutexUnlock(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ MutexHolder' = {}
   /\ UNCHANGED<<ThreadState, SemCount, SemWaiters, WaiterCount, WaitPrepared>>

SemCVWait(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ ThreadState' = [ThreadState EXCEPT ![t] = "Blocked"]
   /\ MutexHolder' = {}
   /\ WaitPrepared' = WaitPrepared \union {t}
   /\ WaiterCount' = WaiterCount + 1
   /\ UNCHANGED<<SemCount, SemWaiters>>

SemCVWaitCommit(t) ==
   t \in WaitPrepared
   /\ SemCount = 0
   /\ SemWaiters' = SemWaiters \union {t}
   /\ WaitPrepared' = WaitPrepared \ {t}
   /\ UNCHANGED<<SemCount, MutexHolder, ThreadState, WaiterCount>>

SemCVWakeFast(t) ==
   t \in WaitPrepared
   /\ MutexHolder = {}
   /\ SemCount > 0
   /\ SemCount' = SemCount - 1
   /\ MutexHolder' = {t}
   /\ ThreadState' = [ThreadState EXCEPT ![t] = "Running"]
   /\ WaitPrepared' = WaitPrepared \ {t}
   /\ UNCHANGED<<SemWaiters, WaiterCount>>

SemCVWakeSlow(t) ==
   ThreadState[t] = "Signaled"
   /\ ~(t \in WaitPrepared)
   /\ ~(t \in SemWaiters)
   /\ MutexHolder = {}
   /\ MutexHolder' = {t}
   /\ ThreadState' = [ThreadState EXCEPT ![t] = "Running"]
   /\ UNCHANGED<<WaitPrepared, SemCount, SemWaiters, WaiterCount>>

SemCVSignal(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ WaiterCount > 0
   /\ WaiterCount' = WaiterCount - 1
   /\ MutexHolder' = {}
   /\ (
   IF SemWaiters = {} THEN
      LET picked == CHOOSE thr \in THREADS: thr \in WaitPrepared
      IN ThreadState' = [ThreadState EXCEPT ![picked] = "Signaled"]
      /\ SemCount' = SemCount + 1
      /\ UNCHANGED<<SemWaiters, WaitPrepared>>
   ELSE
      LET picked == CHOOSE thr \in THREADS: thr \in SemWaiters
      IN ThreadState' = [ThreadState EXCEPT ![picked] = "Signaled"]
      /\ SemWaiters' = SemWaiters \ {picked}
      /\ UNCHANGED<<SemCount, WaitPrepared>>
   )

SemMInit ==
    ThreadState = [t \in THREADS |-> "Running"]
    /\ MutexHolder = {}
    /\ SemCount = 0
    /\ SemWaiters = {}
    /\ WaiterCount = 0
    /\ WaitPrepared = {}

SemMNext ==
    \E t \in THREADS:
    SemCVWait(t) \/ SemCVSignal(t)
    \/ SemCVWakeSlow(t)  \/ SemCVWakeFast(t) \/ SemCVWaitCommit(t)
    \/ SemCVMutexLock(t) \/ SemCVMutexUnlock(t)

SemCVState ==
    <<ThreadState, SemCount, SemWaiters, WaiterCount, WaitPrepared, MutexHolder>>

SemMSpec ==
    SemMInit
    /\ [][SemMNext]_<<SemCVState>>
    /\ (\A t \in THREADS: SF_<<SemCVState>>(SemCVWakeSlow(t)))
    /\ (\A t \in THREADS: SF_<<SemCVState>>(SemCVWakeFast(t)))
    /\ (\A t \in THREADS: WF_<<SemCVState>>(SemCVMutexUnlock(t)))

SemMTypeOK ==
   SemCountTypeOK /\ SemWaitersTypeOK /\ WaiterCountTypeOK /\ WaitPreparedTypeOK

INSTANCE Monitor

THEOREM SemMSpec => [](SemMTypeOK /\ MTypeOK)

THEOREM SemMSpec => MSpec (* This is not true *)
=============================================================================
