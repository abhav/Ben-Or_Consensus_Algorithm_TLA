------------------------------- MODULE benor -------------------------------
(*\* Ben-Or algorithm *)
EXTENDS Integers, Sequences, FiniteSets
\* \* N - nodes, F - failure, MAXROUND - max rounds, INPUT - initial value for each node
CONSTANT N, F, MAXROUND, INPUT
ASSUME N \in Nat /\ F \in Nat /\ F<N
Procs == 1..N \* Procs - Nodes in the algorithm
Rounds == 1..MAXROUND \* No of rounds algorithm will run
(* 
 --algorithm BenOr
 { variable p1Msg = {}, p2Msg = {}; \* 2 Message boards as told in requirements
   define
   {
       \* return tuple of messages in same round with same value
       p1MsgTotalCountValue(r,b) == {m \in p1Msg: (m.round=r) /\ (m.val=b)}
       p2MsgTotalCountValue(r,b) == {m \in p2Msg: (m.round=r) /\ (m.val=b)}
       \* return tuple of messages in same round
       p1MsgTotalCount(r) == {m \in p1Msg: (m.round=r)}
       p2MsgTotalCount(r) == {m \in p2Msg: (m.round=r)}
   }
   
   \* \* node calls this to send p1 msg to other nodes(message board)
   macro SendP1 (n,r,b) 
   {
     p1Msg := p1Msg \union {[node_id |-> n, round |-> r, val |-> b]};
   }
   
   \* \* node calls this after sending p1 msgs to other nodes(message board)
   macro CollectP1 (n,r) 
   {
     \* waiting for p1a msgs in the same round from nodes and proceed if greater or equal to n-f
     await (Cardinality(p1MsgTotalCount(r)) >= (N-F));
     \* if received more than n/2 messages with the same v, then p2v (0/1) else -1 
     if (Cardinality(p1MsgTotalCountValue(r,1))*2 > N){
         p2v := 1;
     }else if(Cardinality(p1MsgTotalCountValue(r,0))*2 > N){
         p2v := 0;
     }else{
         p2v := -1;
     };
     phase1_complete := TRUE;
   }
   
   \* \* node calls this to send p2 msg to other nodes(message board)
   macro SendP2 (n,r,b)
   {
     p2Msg := p2Msg \union {[node_id |-> n, round |-> r, val |-> b]};
   }
   
   \* \* node calls this after sending p1 msgs to other nodes(message board)
   macro CollectP2 (n,r)
   {
    \* waiting for p2 msgs in the same round from nodes and proceed if greater or equal to n-f
    await (Cardinality(p2MsgTotalCount(r)) >= (N-F));
    \* if received at least f + 1 message with the same v # -1 then decided := v else 2
    if (Cardinality(p2MsgTotalCountValue(r,0)) >= (F + 1)){
        decided := 0;
    }else if(Cardinality(p2MsgTotalCountValue(r,1)) >= (F + 1)){
        decided := 1;
     }else{
        \* if decide is not set then it is set to 2 which is reset to -1 at start of next round, primarly done for handling invariants
        decided := 2; 
     };
    phase2_complete := TRUE;
   }  
   
   \* \* Node process
   fair process (p \in Procs)
   variable n_id=self, phase1_complete=FALSE, phase2_complete=FALSE, r=1, p1v = INPUT[self], p2v = -1, decided=-1; 
   {
        P: while (r <= MAXROUND) {
        \*  rest values to default
        decided := -1; 
        phase1_complete := FALSE;
        phase2_complete := FALSE;
        p2v := -1;
        
        \*\* Move to phase1
        P1:     SendP1(n_id, r, p1v);
        CP1:    CollectP1(n_id,r);
        \*\* Move to phase2
        if (phase1_complete=TRUE){          
            P2:  SendP2(n_id, r, p2v);
            };
        CP2: CollectP2(n_id, r);
         
        \*\* put value in p1v for next round
        P2F:  if (phase2_complete=TRUE){ 
                \* if consensus value decided then put that value to initate
                if (decided \in {0,1}){
                    p1v := decided;
                 \* else see if any message with value 0/1 id p2 message board
                }else if(Cardinality(p2MsgTotalCountValue(r,0)) > 0 \/ Cardinality(p2MsgTotalCountValue(r,1)) > 0){
                    if(Cardinality(p2MsgTotalCountValue(r,0)) > 0){
                        p1v := 0;
                    }else{
                        p1v := 1;
                    };
                \* else choode randomly
                }else{
                    \*x := CHOOSE y \in {0,1}: TRUE; -  deterministic and therefore not used
                    \* with is non deterministic and is therefore used 
                    with (y \in {0,1})
                        p1v := y;
                };  
             };
        r:=r+1;
     } 
   } 
 }
*)
\* BEGIN TRANSLATION
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
p1MsgTotalCountValue(r,b) == {m \in p1Msg: (m.round=r) /\ (m.val=b)}
p2MsgTotalCountValue(r,b) == {m \in p2Msg: (m.round=r) /\ (m.val=b)}

p1MsgTotalCount(r) == {m \in p1Msg: (m.round=r)}
p2MsgTotalCount(r) == {m \in p2Msg: (m.round=r)}

VARIABLES n_id, phase1_complete, phase2_complete, r, p1v, p2v, decided

vars == << p1Msg, p2Msg, pc, n_id, phase1_complete, phase2_complete, r, p1v, 
           p2v, decided >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ n_id = [self \in Procs |-> self]
        /\ phase1_complete = [self \in Procs |-> FALSE]
        /\ phase2_complete = [self \in Procs |-> FALSE]
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> -1]
        /\ pc = [self \in ProcSet |-> "P"]

P(self) == /\ pc[self] = "P"
           /\ IF r[self] <= MAXROUND
                 THEN /\ decided' = [decided EXCEPT ![self] = -1]
                      /\ phase1_complete' = [phase1_complete EXCEPT ![self] = FALSE]
                      /\ phase2_complete' = [phase2_complete EXCEPT ![self] = FALSE]
                      /\ p2v' = [p2v EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << phase1_complete, phase2_complete, p2v, 
                                      decided >>
           /\ UNCHANGED << p1Msg, p2Msg, n_id, r, p1v >>

P1(self) == /\ pc[self] = "P1"
            /\ p1Msg' = (p1Msg \union {[node_id |-> n_id[self], round |-> r[self], val |-> p1v[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP1"]
            /\ UNCHANGED << p2Msg, n_id, phase1_complete, phase2_complete, r, 
                            p1v, p2v, decided >>

CP1(self) == /\ pc[self] = "CP1"
             /\ (Cardinality(p1MsgTotalCount(r[self])) >= (N-F))
             /\ IF Cardinality(p1MsgTotalCountValue(r[self],1))*2 > N
                   THEN /\ p2v' = [p2v EXCEPT ![self] = 1]
                   ELSE /\ IF Cardinality(p1MsgTotalCountValue(r[self],0))*2 > N
                              THEN /\ p2v' = [p2v EXCEPT ![self] = 0]
                              ELSE /\ p2v' = [p2v EXCEPT ![self] = -1]
             /\ phase1_complete' = [phase1_complete EXCEPT ![self] = TRUE]
             /\ IF phase1_complete'[self]=TRUE
                   THEN /\ pc' = [pc EXCEPT ![self] = "P2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CP2"]
             /\ UNCHANGED << p1Msg, p2Msg, n_id, phase2_complete, r, p1v, 
                             decided >>

P2(self) == /\ pc[self] = "P2"
            /\ p2Msg' = (p2Msg \union {[node_id |-> n_id[self], round |-> r[self], val |-> p2v[self]]})
            /\ pc' = [pc EXCEPT ![self] = "CP2"]
            /\ UNCHANGED << p1Msg, n_id, phase1_complete, phase2_complete, r, 
                            p1v, p2v, decided >>

CP2(self) == /\ pc[self] = "CP2"
             /\ (Cardinality(p2MsgTotalCount(r[self])) >= (N-F))
             /\ IF Cardinality(p2MsgTotalCountValue(r[self],0)) >= (F + 1)
                   THEN /\ decided' = [decided EXCEPT ![self] = 0]
                   ELSE /\ IF Cardinality(p2MsgTotalCountValue(r[self],1)) >= (F + 1)
                              THEN /\ decided' = [decided EXCEPT ![self] = 1]
                              ELSE /\ decided' = [decided EXCEPT ![self] = 2]
             /\ phase2_complete' = [phase2_complete EXCEPT ![self] = TRUE]
             /\ pc' = [pc EXCEPT ![self] = "P2F"]
             /\ UNCHANGED << p1Msg, p2Msg, n_id, phase1_complete, r, p1v, p2v >>

P2F(self) == /\ pc[self] = "P2F"
             /\ IF phase2_complete[self]=TRUE
                   THEN /\ IF decided[self] \in {0,1}
                              THEN /\ p1v' = [p1v EXCEPT ![self] = decided[self]]
                              ELSE /\ IF Cardinality(p2MsgTotalCountValue(r[self],0)) > 0 \/ Cardinality(p2MsgTotalCountValue(r[self],1)) > 0
                                         THEN /\ IF Cardinality(p2MsgTotalCountValue(r[self],0)) > 0
                                                    THEN /\ p1v' = [p1v EXCEPT ![self] = 0]
                                                    ELSE /\ p1v' = [p1v EXCEPT ![self] = 1]
                                         ELSE /\ \E y \in {0,1}:
                                                   p1v' = [p1v EXCEPT ![self] = y]
                   ELSE /\ TRUE
                        /\ p1v' = p1v
             /\ r' = [r EXCEPT ![self] = r[self]+1]
             /\ pc' = [pc EXCEPT ![self] = "P"]
             /\ UNCHANGED << p1Msg, p2Msg, n_id, phase1_complete, 
                             phase2_complete, p2v, decided >>

p(self) == P(self) \/ P1(self) \/ CP1(self) \/ P2(self) \/ CP2(self)
              \/ P2F(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
Agreement == \A a1,a2 \in Procs: (decided[a1] # -1 /\ decided[a2] # -1 /\ decided[a1] # 2 /\ decided[a2] # 2) => decided[a1]=decided[a2]
Progress == \A a1 \in Procs: Cardinality({i \in Procs:(INPUT[i]=0)}) = N \/ Cardinality({i \in Procs:(INPUT[i]=1)}) = N => decided[a1]#2 
BaitProgress == \A a1 \in Procs: Cardinality({i \in Procs:(INPUT[i]=0)}) = Cardinality({i \in Procs:(INPUT[i]=1)}) => decided[a1] = -1 \/ decided[a1] = 2
MinorityReport0 == \A a1 \in Procs: Cardinality({i \in Procs:(INPUT[i]=0)}) < Cardinality({i \in Procs:(INPUT[i]=1)}) => decided[a1] # 0  
MinorityReport1 == \A a1 \in Procs: Cardinality({i \in Procs:(INPUT[i]=0)}) > Cardinality({i \in Procs:(INPUT[i]=1)}) => decided[a1] # 1 
MinorityReport == MinorityReport0 /\ MinorityReport1                            
ProgressTermination == <>(\A a1 \in Procs: decided[a1] = 0 \/ decided[a1] = 1)                      
=============================================================================
\* Project Completed by Abhav Luthra (50288904) and Krishna Sehgal(50291124)
\* Modification History
\* Last modified Thu Nov 28 16:02:28 EST 2019 by abhavluthra
\* Created Tue Nov 12 12:51:46 EST 2019 by abhavluthra

=============================================================================
\* Project Report
-----------------------------------------------------------------------------
\* The above code have implmentation of Ben-Or's Randomized Consensus Algorithm in PlusCal.
Each round has 6 states for each node:
P  - Start of round, while loop checker
P1 - Send message in phase 1 of algorithm
CP1- Collect message in phase 1 of algorithm and set p2v value
P2 - Send message in phase 2 of algorithm
CP2- Collect message in phase 2 of algorithm and set decided value
P2F- Set value of p1v for the next round of the algorithm

=============================================================================
\* Code Description
-----------------------------------------------------------------------------
Code is exact implemetation of paper Correctness Proof of Ben-Or's Randomized Consensus Algorithm(1998)
where R and P is replaced by node_id and ? by -1. After round completetion, we set the decided value as 2 if not decided among 0,1.
At the start of next round. Decided is reset to -1
=============================================================================
\* Agreement
-----------------------------------------------------------------------------
Agreement variant states that if dedided variable of 2 nodes are not -1 or 2 (which means the same that
no value was assigned before orafter the round), they have to be same.

\* Agreement invariant remains true with all the below values and with rest of the properties
N=3, F=0, MAXROUNDS = 3, INPUT=<<1,1,1>>, unique states - 416
N=3, F=1, MAXROUNDS = 3, INPUT=<<1,1,1>>, unique states - 2720
N=3, F=2, MAXROUNDS = 3, INPUT=<<1,1,1>>, unique states - 438560
N=3, F=0, MAXROUNDS = 3, INPUT=<<0,1,1>>, unique states - 416
N=3, F=1, MAXROUNDS = 3, INPUT=<<0,1,1>>, unique states - 146870
N=3, F=2, MAXROUNDS = 3, INPUT=<<0,1,1>>, unique states - 921940
=============================================================================
\* Bait Progress
-----------------------------------------------------------------------------
Bait progress states that it is not possible for all processes to decide ie it has to be -1 or 2 after every round
but it after some rounds, it will happen
We ran the model with N=4, F=0, MAXROUNDS = 3, INPUT=<<0,0,1,1>>. After finding 5538 unique states,
we experience a failure 

Initial Value
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {}
/\  p1v = <<0, 0, 1, 1>>
/\  p2Msg = {}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"P", "P", "P", "P">>
/\  phase1_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  phase2_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  r = <<1, 1, 1, 1>>
-----------------------------------------------------------------------------
After 1st round, No consensus is formed and decided remain -1
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 0, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 1, val |-> 1, node_id |-> 4]}
/\  p1v = <<0, 0, 1, 1>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3], [round |-> 1, val |-> -1, node_id |-> 4]}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"CP2", "CP2", "CP2", "CP2">>
/\  phase1_complete = <<TRUE, TRUE, TRUE, TRUE>>
/\  phase2_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  r = <<1, 1, 1, 1>>
-----------------------------------------------------------------------------
In round 2, value of p1v is initialized as <<0, 1, 0, 0>> which helps form a consensus with value 0
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 0, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 1, val |-> 1, node_id |-> 4], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 4], [round |-> 2, val |-> 1, node_id |-> 2]}
/\  p1v = <<0, 1, 0, 0>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3], [round |-> 1, val |-> -1, node_id |-> 4]}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"CP1", "CP1", "CP1", "CP1">>
/\  phase1_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  phase2_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  r = <<2, 2, 2, 2>>
-----------------------------------------------------------------------------
In final state, consensus is formed and decided value is updated to 0. Therefore, invariant is violated.
-----------------------------------------------------------------------------
/\  decided = <<0, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 0, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 1, val |-> 1, node_id |-> 4], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 4], [round |-> 2, val |-> 1, node_id |-> 2]}
/\  p1v = <<0, 1, 0, 0>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3], [round |-> 1, val |-> -1, node_id |-> 4], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2], [round |-> 2, val |-> 0, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 4]}
/\  p2v = <<0, 0, 0, 0>>
/\  pc = <<"P2F", "CP2", "CP2", "CP2">>
/\  phase1_complete = <<TRUE, TRUE, TRUE, TRUE>>
/\  phase2_complete = <<TRUE, FALSE, FALSE, FALSE>>
/\  r = <<2, 2, 2, 2>>


=============================================================================
\* Minority Report
-----------------------------------------------------------------------------
MinorityReport states that it is not possible for all the nodes to finalize a value as consensus value which is not a majority value.

We ran the model with N=4, F=0, MAXROUNDS = 3, INPUT=<<0,1,1,1>>, we got 1824 unique states with decided value 1 
eventually and never reaching 0 as no failure was observed. Then,
We ran the model with N=4, F=1, MAXROUNDS = 3, INPUT=<<0,1,1,1>>, we got 46224 unique states after which decided value become 0 ,ie
minority value became consensus value and invariant is violated.

Inital Value
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {}
/\  p1v = <<0, 1, 1, 1>>
/\  p2Msg = {}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"P", "P", "P", "P">>
/\  phase1_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  phase2_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  r = <<1, 1, 1, 1>>
-----------------------------------------------------------------------------
As after round 1 phase 1, we need than n-f = 3 messages(0,1,1) more than n/2 ie > 2 nodes with the same p1v
But that does not happen and p2v become -1 for all 3 running nodes 
Round 2 starts with resetting p1v with 0 in all 3 nodes as seen in these two states
-----------------------------------------------------------------------------
/\  decided = <<2, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3]}
/\  p1v = <<0, 1, 1, 1>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3]}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"P2F", "CP2", "CP2", "P">>
/\  phase1_complete = <<TRUE, TRUE, TRUE, FALSE>>
/\  phase2_complete = <<TRUE, FALSE, FALSE, FALSE>>
/\  r = <<1, 1, 1, 1>>
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, 2, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2]}
/\  p1v = <<0, 0, 0, 1>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3]}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"CP1", "CP1", "P", "P">>
/\  phase1_complete = <<FALSE, FALSE, TRUE, FALSE>>
/\  phase2_complete = <<FALSE, FALSE, TRUE, FALSE>>
/\  r = <<2, 2, 2, 1>>
-----------------------------------------------------------------------------
Thereby, setting the decide value as 0 after which invariant get violated
-----------------------------------------------------------------------------

/\  decided = <<0, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2], [round |-> 2, val |-> 0, node_id |-> 3]}
/\  p1v = <<0, 0, 0, 1>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2], [round |-> 2, val |-> 0, node_id |-> 3]}
/\  p2v = <<0, 0, 0, -1>>
/\  pc = <<"P2F", "CP2", "CP2", "P">>
/\  phase1_complete = <<TRUE, TRUE, TRUE, FALSE>>
/\  phase2_complete = <<TRUE, FALSE, FALSE, FALSE>>
/\  r = <<2, 2, 2, 1>>
-----------------------------------------------------------------------------

Then, We ran the model with N=4, F=2, MAXROUNDS = 3, INPUT=<<0,1,1,1>>, we got 217512 unique states after which decided value become 0 ,ie
minority value became consensus value and invariant is violated.
Final State 32 for refernce
-----------------------------------------------------------------------------
/\  decided = <<0, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {[round |-> 1, val |-> 0, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2], [round |-> 2, val |-> 0, node_id |-> 3]}
/\  p1v = <<0, 0, 0, 1>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 1], [round |-> 1, val |-> -1, node_id |-> 2], [round |-> 1, val |-> -1, node_id |-> 3], [round |-> 2, val |-> 0, node_id |-> 1], [round |-> 2, val |-> 0, node_id |-> 2], [round |-> 2, val |-> 0, node_id |-> 3]}
/\  p2v = <<0, 0, 0, -1>>
/\  pc = <<"P2F", "CP2", "CP2", "P">>
/\  phase1_complete = <<TRUE, TRUE, TRUE, FALSE>>
/\  phase2_complete = <<TRUE, FALSE, FALSE, FALSE>>
/\  r = <<2, 2, 2, 1>>

=============================================================================
\* Progress
Progress property states that if we start with all same preference value at all nodes, this should terminate, ie, 
every process eventually will not have decided # 2, that means it will decide 0,1 after the end of the round.

As i posted it piazza as well that if we need to run Progress with failures so we wrote 2 different property to check progress
-----------------------------------------------------------------------------
I Progress Property
-----------------------------------------------------------------------------
The property written below is always true for less than N/2 failures
Progress == \A a1 \in Procs: Cardinality({i \in Procs:(INPUT[i]=0)}) = N \/ Cardinality({i \in Procs:(INPUT[i]=1)}) = N => decided[a1]#2
Here at the end of the round, decided value becomes 1 or 0.

We ran the model with N=4, F=0, MAXROUNDS = 3, INPUT=<<1,1,1,1>>, we got 1824 unique states. Then,
We ran the model with N=4, F=1, MAXROUNDS = 3, INPUT=<<1,1,1,1>>, we got 15296 unique states.


-----------------------------------------------------------------------------
II Progress Property
-----------------------------------------------------------------------------
ProgressTermination == <>(\A a1 \in Procs: decided[a1] = 0 \/ decided[a1] = 1)   

It states that there will be termination only when decided became 0/1 eventually

The execution result remain same for less than N/2 failures

We ran the model with N=4, F=1, MAXROUNDS = 3, INPUT=<<1,1,1,1>>
we got more than 438,560 unique states and invariant get vioated as decided still not become 0/1 after round 3. 
which is correct as N-F(=1) might become true but there will never be more than N/2(=1) message in phase 1 of any roound
so p2v will always be -1 and therefore decided always remain -1

Therefore there will be bo progress with N/2 or more failures

Trace/Log-
Initial State
-----------------------------------------------------------------------------
/\  decided = <<-1, -1, -1, -1>>
/\  n_id = <<1, 2, 3, 4>>
/\  p1Msg = {}
/\  p1v = <<1, 1, 1, 1>>
/\  p2Msg = {}
/\  p2v = <<-1, -1, -1, -1>>
/\  pc = <<"P", "P", "P", "P">>
/\  phase1_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  phase2_complete = <<FALSE, FALSE, FALSE, FALSE>>
/\  r = <<1, 1, 1, 1>>
-----------------------------------------------------------------------------
Final State
-----------------------------------------------------------------------------
/\  decided = <<2, 2, 2>>
/\  n_id = <<1, 2, 3>>
/\  p1Msg = {[round |-> 1, val |-> 1, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 1, val |-> 1, node_id |-> 3], [round |-> 2, val |-> 1, node_id |-> 1], [round |-> 2, val |-> 1, node_id |-> 2], [round |-> 2, val |-> 1, node_id |-> 3], [round |-> 3, val |-> 1, node_id |-> 1], [round |-> 3, val |-> 1, node_id |-> 2], [round |-> 3, val |-> 1, node_id |-> 3]}
/\  p1v = <<1, 1, 0>>
/\  p2Msg = {[round |-> 1, val |-> -1, node_id |-> 3], [round |-> 1, val |-> 1, node_id |-> 1], [round |-> 1, val |-> 1, node_id |-> 2], [round |-> 2, val |-> 1, node_id |-> 1], [round |-> 2, val |-> 1, node_id |-> 2], [round |-> 2, val |-> 1, node_id |-> 3], [round |-> 3, val |-> -1, node_id |-> 3], [round |-> 3, val |-> 1, node_id |-> 1], [round |-> 3, val |-> 1, node_id |-> 2]}
/\  p2v = <<1, 1, -1>>
/\  pc = <<"Done", "Done", "Done">>
/\  phase1_complete = <<TRUE, TRUE, TRUE>>
/\  phase2_complete = <<TRUE, TRUE, TRUE>>
/\  r = <<4, 4, 4>>
