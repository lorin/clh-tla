\* A lock that grants access in FIFO order
---- MODULE FifoLock ----
EXTENDS Sequences

CONSTANT Threads

VARIABLES queue, state

TypeOK == /\ queue \in Seq(Threads)
          /\ state \in [Threads -> {"ready", "requested", "acquired", "in-cs", "released"}]
        

Init == /\ queue = <<>>
        /\ state = [t \in Threads |-> "ready"]

Request(thread) == 
    /\ state[thread] = "ready"
    /\ queue' = Append(queue, thread)
    /\ state' = [state EXCEPT ![thread]="requested"]

Acquired(thread) ==
    /\ state[thread] = "requested"
    /\ Head(queue) = thread
    /\ state' = [state EXCEPT ![thread]="acquired"]
    /\ UNCHANGED queue

CriticalSection(thread) ==
    /\ state[thread] = "acquired"
    /\ state' = [state EXCEPT ![thread]="in-cs"]
    /\ UNCHANGED queue

Released(thread) ==
    /\ state[thread] = "in-cs"
    /\ queue' = Tail(queue)
    /\ state ' = [state EXCEPT ![thread]="ready"]


Next == \/ \E t \in Threads : \/ Request(t)
                              \/ Acquired(t)
                              \/ CriticalSection(t)
                              \/ Released(t)
         
Spec == Init /\ [][Next]_<<queue, state>>

MutualExclusion ==
    \A t1,t2 \in Threads : (state[t1] = "in-cs" /\ state[t2] = "in-cs") => t1=t2

====