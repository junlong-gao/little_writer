------------------------------ MODULE Monitor ------------------------------

CONSTANT THREADS (* a set of running threads *)

VARIABLE ThreadState
VARIABLE MutexHolder

ThreadStateTypeOK ==
   ThreadState \in [THREADS -> {"Running", "Blocked", "Signaled"}]
   
MutexHolderTypeOK ==
   MutexHolder = {}
   \/ \E t \in THREADS: MutexHolder = {t}
   
MutexLock(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {}
   /\ MutexHolder' = {t}
   /\ UNCHANGED<<ThreadState>>
   
MutexUnlock(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ MutexHolder' = {}
   /\ UNCHANGED<<ThreadState>>
   
CVWait(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ MutexHolder' = {}
   /\ ThreadState' = [ThreadState EXCEPT ![t] = "Blocked"]

CVSignal(t) ==
   ThreadState[t] = "Running"
   /\ MutexHolder = {t}
   /\ (
      IF \A thr \in THREADS: ThreadState[thr] /= "Blocked"
      THEN MutexHolder' = {}
           /\ UNCHANGED<<ThreadState>>
      ELSE LET blocked == CHOOSE thr \in THREADS : ThreadState[thr] = "Blocked"
           IN MutexHolder' = {} (* we can do Hoare semantics here *)
              /\ ThreadState' = [ThreadState EXCEPT ![blocked] = "Signaled"]
      )
CVWake(t) ==
   ThreadState[t] = "Signaled"
   /\ MutexHolder = {}
   /\ MutexHolder' = {t}
   /\ ThreadState' = [ThreadState EXCEPT ![t] = "Running"]

MInit == ThreadState = [t \in THREADS |-> "Running"]
         /\ MutexHolder = {}

MNext == \E t \in THREADS: CVWait(t) \/ CVSignal(t) \/ CVWake(t) \/ MutexLock(t) \/ MutexUnlock(t)

MSpec == MInit /\ [][MNext]_<<ThreadState, MutexHolder>>
         /\ (\A t \in THREADS: SF_<<ThreadState, MutexHolder>>(CVWake(t)))
         /\ (\A t \in THREADS: WF_<<ThreadState, MutexHolder>>(MutexUnlock(t)))

MTypeOK == ThreadStateTypeOK \/ MutexHolderTypeOK

CVSignalFairness ==
    \A t \in THREADS:
        ThreadState[t] = "Signaled" ~> ThreadState[t] = "Running"

THEOREM MSpec => MTypeOK /\ CVSignalFairness
(* Model check: Spec, check Inv MTypeOK and temporal property CVSignalFairness *)
=============================================================================
