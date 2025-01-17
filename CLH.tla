\* A CLH lock
---- MODULE CLH ----
EXTENDS Integers, Sequences

CONSTANTS NProc,
          GRANTED,
          PENDING,
          X \* Don't care

first == 0 \* Initial request on the queue, not owned by any process
Processes == 1..NProc
RequestIDs == Processes \union {first}

NIL == -1


VARIABLES
    requests, \* map request ids to request state
    myreq, \* request owned by process
    watch, \* request watched by process (the one ahead of me in line)
    tail, \* request id
    state \* Process state

TypeOk ==
    /\ requests \in [RequestIDs -> {PENDING, GRANTED, X}]
    /\ myreq \in [Processes -> RequestIDs]
    /\ watch \in [Processes -> RequestIDs \union {NIL}]
    /\ tail \in RequestIDs
    /\ state \in [Processes -> {"ready", "to-enqueue", "waiting", "acquired", "in-cs"}]

Init ==
    /\ requests = [r \in RequestIDs |-> IF r = first THEN GRANTED ELSE X]
    /\ myreq = [p \in Processes |-> p] \* initially, process id = request id
    /\ watch = [p \in Processes |-> NIL]
    /\ tail = first
    /\ state = [p \in Processes |-> "ready"]

MarkPending(process) ==
    /\ state[process] = "ready"
    /\ requests' = [requests EXCEPT ![myreq[process]]=PENDING]
    /\ state' = [state EXCEPT ![process] = "to-enqueue"]
    /\ UNCHANGED <<myreq, watch, tail>>

\* Enqueue my request: watch the old tail and make me the new one
EnqueueRequest(process) ==
    /\ state[process] = "to-enqueue"
    /\ watch' = [watch EXCEPT ![process]=tail]
    /\ tail' = myreq[process]
    /\ state' = [state EXCEPT ![process]="waiting"]
    /\ UNCHANGED <<requests, myreq>>

AcquireLock(process) ==
    /\ state[process] = "waiting"
    /\ requests[watch[process]] = GRANTED
    /\ state' = [state EXCEPT ![process]="acquired"]
    /\ UNCHANGED <<requests, myreq, watch, tail>>

EnterCriticalSection(process) ==
    /\ state[process] = "acquired"
    /\ state' = [state EXCEPT ![process]="in-cs"]
    /\ UNCHANGED <<requests, myreq, watch, tail>>

\* Release the lock and grant it to the next process,
\* Take ownership of the request I was watching
GrantLock(process) ==
    /\ state[process] = "in-cs"
    /\ requests' = [requests EXCEPT ![myreq[process]]=GRANTED]
    /\ myreq' = [myreq EXCEPT ![process]=watch[process]]
    /\ state' = [state EXCEPT ![process]="ready"]
    /\ UNCHANGED <<watch, tail>>

Next == \E p \in Processes : \/ MarkPending(p)
                             \/ EnqueueRequest(p)
                             \/ AcquireLock(p)
                             \/ EnterCriticalSection(p)
                             \/ GrantLock(p)
  
Unowned(request) ==
    ~ \E p \in Processes : myreq[p] = request

\* Need to reconstruct the queue to do our mapping
RECURSIVE QueueFromTail(_)
QueueFromTail(rid) ==
    IF Unowned(rid) THEN <<>> ELSE 
        LET tl == CHOOSE p \in Processes : myreq[p] = rid
            r == watch[tl]
        IN Append(QueueFromTail(r), tl)

Mapping == INSTANCE FifoLock
    WITH queue <- QueueFromTail(tail),
         Threads <- Processes,
         state <- [p \in Processes |-> 
            CASE state[p]="ready" -> "ready"
              [] state[p]="to-enqueue" -> "ready"
              [] state[p]="waiting" -> "requested"
              [] state[p]="acquired" -> "acquired"
              [] state[p]="in-cs" -> "in-cs"]

Refinement == Mapping!Spec

MutualExclusion ==
    \A p1,p2 \in Processes : (state[p1] = "in-cs" /\ state[p2] = "in-cs") => p1=p2

====