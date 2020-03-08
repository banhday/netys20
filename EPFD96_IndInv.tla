--------------------------- MODULE EPFD96_IndInv ---------------------------

(* A TLA+ encoding of the eventually perfect failure detectors in Figure 10 [1] 
   under partially synchronous constraints of the DLS computational model [2].  
  
   [1] Chandra, Tushar Deepak, and Sam Toueg. "Unreliable failure detectors for 
   reliable distributed systems." Journal of the ACM (JACM) 43.2 (1996): 225-267.
   
   [2] Dwork, Cynthia, Nancy Lynch, and Larry Stockmeyer. "Consensus in the presence 
   of partial synchrony." Journal of the ACM (JACM) 35.2 (1988): 288-323.                                                                 
  
   Thanh-Hai Tran, Igor Konnov, Josef Widder, 2019
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE. 
 *)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS N,              \* The number of processes  
          T,              \* The maximum number of failures
          F,              \* The current number of failures  
          Delta,          \* Bound for message delay
          Phi             \* Bound for relaive process speed
                          
Proc == 1..N                        \* Set of processes  
MsgAge == 0..Delta                  \* Possible ages of in-transit messages 
TOGuard == 3 * Phi + Delta + 2      \* The upper bound of timeout[p, q]
TODefault == 1                      \* Default value for timeout[p, q]
TOSet == 0..TOGuard                 \* Possible values of timeout[p, q]
Break_Period == 0..(Phi - 1)        \* A process can be frozen in (Phi-1) steps.
\* For type information of msg buffers  
MsgAgePowerSet == [Proc \times Proc -> SUBSET (0..Delta)]
FromLastSendSet == 0..(3 * Phi - 1) \* For an inductive invariant

\* For the model checker APALACHE
a <: b == a

\* Set of processes, and process IDs are from 1 to N
\* Marks Proc as a comment since APALACHE's complaints
\* Proc == 1..N 

\* If Delta = 0 and Phi = 1, the computational model is asynchronous.
ASSUME 0 <= Delta /\ 1 <= Phi
 
\*  - After the time point T_0, ages of messages in transit are eventually  
\*  limited by (Delta + 6 * Phi). 
\*  - However, we can apply an abstraction on message ages. After an message 
\*  reaches Delta years old, we can stop increasing its age.
\*  - Assume that new messages are 0 years old.
\*  - Therefore, possible message ages range from 0 to Delta. 
\* MsgAge == 0..Delta       
 
\*  - My inductive invariant is checked with TOGuard = 3 * Phi + Delta + 2.
\*  The reason of this change is that a time-out never changes since it reaches 
\*  3 * Phi + Delta + 2. 
\*  - Notice that the mimimal upper bound of time-outs might be less.
\*  - Here we set TODefault is 1. In an execution, a time-out might be increased.
\* TOGuard == 3 * Phi + Delta + 2  
\* TODefault == TOGuard

\*  - For every process, there is a clock to measure how long it has not take
\*  a transition. These clocks are declared later as an array "break_timer".
\*  In every global step, every clock is increased by 1, or reset to 0. When
\*  break_timer[i] reaches Phi - 1, it will be reset to 0 in the next step.
\*  If break_timer[i] = 0 and process i is correct, it must take a transition
\*  in this logically global step.
\*  - A break timer of a crashed process is always 0.    
\*  - Break_Period is a set of possible values of break_timer[i] for every i.
\*  Hence, break_timer has a type invariant [Proc -> Break_Period].     
\* Break_Period == 0..(Phi - 1)


Action == {"send", "del", "comp", "crash"}                \* Transition names
 
\*  - MsgAgePowerSet is a set of two dimensional matrixs who are possible 
\*  configuration of message channels. 
\*  - The value of MsgAgePowerSet is cached and never computed again in the 
\*  running time of TLC.
\*  - MsgAgePowerSet is used to non-deterministically deliver in-transit messages.   
\* MsgAgePowerSet == [Proc \times Proc -> SUBSET (0..Delta)]


  
\* Algorithm's variables  
VARIABLES suspected,    \* Two dimenstional matrix has type [Proc \times Proc -> BOOL]
          waiting_time, \* Two dimenstional matrix has type [Proc \times Proc -> Int] 
                        \* How long a process p_i has waited for process p_j
          time_out,     \* Two dimenstional matrix has type [Proc \times Proc -> Int]
                        \* The time-out value for how long process p_i waits for 
                        \* process p_j
          pc            \* Describe transitions which processes take 
          
\* Model's variables          
VARIABLES msgBuf,       \* Two dimensional matrix contains ages of messages sent 
                        \* from process p_i to process p_j.                     
          del,          \* Whether a process p_i received any messages from
                        \* process p_j in the last execution of Receive.           
          break_timer,  \* How long a process has not take a transition 
          subround         \* 4 subrounds: schedule, send, receive, and compute
          
\*  - The below variable fromLastSend is a ghost one, and is used only to construct
\*  an inductive invariant.
\*  - This variable fromLastSend tracks how long it has been from the last time 
\*  process i sent a message, and has a simple type [Proc -> Int]. More precisely, 
\*  its type is [Proc -> 0..(3 * Phi - 1)].  
VARIABLES fromLastSend          

vars == << del, msgBuf, break_timer, subround, 
           suspected, waiting_time, time_out, pc,
           fromLastSend >>          
             
  
\*  - Initialize the enviromental variables.
\*  - The first transition is a scheduling step.
Scheduler_Init ==   
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) = 0
  /\ break_timer = [p \in Proc |-> 0]
  /\ subround = "sched"  
  /\ fromLastSend = [p \in Proc |-> 0 ]
               

\*  - Initialize process variables.
\*  - If a process is crashed, set its time-outs to 0. Otherwise, set 1.          
Proc_Init ==
  /\ pc = [ p \in Proc |-> "send" ]
  /\ msgBuf = [<< p, q >> \in Proc \times Proc |-> {} <: {Int} ]       
  /\ suspected = [<< p, q >> \in Proc \times Proc |-> FALSE]
  /\ waiting_time = [<< rcver, snder >> \in Proc \times Proc |-> 0 ]
  /\ time_out = [<< p, q >> \in Proc \times Proc |-> IF pc[p] = "crash" 
                                                     THEN 0
                                                     ELSE TODefault ]
  /\ del = [<< p, q >> \in Proc \times Proc |-> FALSE]                  

  
\*  - Initial states 
\*  - Initial states might not satisfy the inductive invariant IndInvInPostfix.
\*  However, for every execution path, there exists a postfix such that every 
\*  state in this postfix satisfies IndInvInPostfix. This property is checked 
\*  with the liveness PostfixIndInv of the specification ESpec which are defined in the
\*  end. Notice that initial states in Spec_EventualIndInv always have F crashes.
Init == Proc_Init /\  Scheduler_Init  

\*  - Schedule the movement of processes. 
\*  - If break_timer'[i] # 0, process p_i is frozen in the next global transition. 
\*  - If process i is already crashed, then break_timer[i] = 0.
\*  - In this encoding, a global transition contains four subrounds: schedule, send, 
\*  deliver, and comp whose order is fixed: sched -> send -> del -> comp. 
\*  - A global transition is sometimes called as a big step, and subrounds are called 
\*  small steps. 
Schedule ==  
  /\ subround = "sched"
  /\ subround' = "send"  
  /\ \E aliveProc \in SUBSET { p \in Proc : pc[p] # "crash" } :  \* correct processes
        /\ Cardinality(aliveProc) >= N - F   
        /\ \E activeProc \in SUBSET aliveProc :         \* arbitrarily active processes         
              /\ pc' = [p \in Proc |-> 
                          IF p \notin aliveProc
                          THEN "crash"
                          ELSE IF p \notin activeProc 
                          THEN pc[p]
                          ELSE IF pc[p] = "send" 
                          THEN  "del"
                          ELSE IF pc[p] = "del"
                          THEN "comp"
                          ELSE "send"]    
          /\ break_timer' = [ p \in Proc |-> IF p \notin aliveProc   
                                             THEN 0 
                                             ELSE IF p \in activeProc
                                             THEN 0
                                             ELSE break_timer[p] + 1]
                                          
       
\* Increase every age by 1. This udpate is done in the "sched" subround.                                                                                    
\* All process variables are unchanged. The ghost variable fromLastSend
\* is updated only here.          
AgeIncrease ==                                         
  /\ msgBuf' = [<< p, q >> \in Proc \times Proc |-> 
                   IF pc'[q] = "crash"
                   THEN {} <: {Int}
                   ELSE {IF k < Delta THEN k + 1 ELSE Delta: k \in msgBuf[p, q]}]
  /\ fromLastSend' = [p \in Proc |-> IF pc'[p] = "send" /\ break_timer'[p] = 0                                          
                                     THEN 0 
                                     ELSE IF pc'[p] = "crash" 
                                     THEN 0
                                     ELSE fromLastSend[p] + 1]                            
   
\* Update the configuration because of recently crashed processes.     
UponCrash ==
  /\ time_out' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN 0
                        ELSE time_out[p, q]]
  /\ waiting_time' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN 0
                        ELSE waiting_time[p, q]]
  /\ suspected' = [<<p, q>> \in Proc \times Proc |-> 
                        IF pc'[p] = "crash" 
                        THEN FALSE
                        ELSE suspected[p, q]]  
                                                                 
\*  - Messages sent to crashed processes are ignored.
\*  - Here we assume that new messages are 0 year old. Only active processes in 
\*  the subround "send" can add 0 in message buffers.
\*  - Other variables are unchanged.                                                                                                                                                             
AddNewMsgs ==
  /\ subround = "send"
  /\ subround' = "del" 
  /\ msgBuf' = [<< snder, rcver >> \in Proc \times Proc |->     
                    IF pc[rcver] = "crash"  
                    THEN {} <: {Int}       
                    ELSE IF /\ pc[snder] = "send" 
                            /\ break_timer[snder] = 0                             
                    THEN { 0 } \cup msgBuf[snder, rcver] 
                    ELSE msgBuf[snder, rcver] ]
  /\ UNCHANGED << pc, break_timer, del, fromLastSend >>
     
\* Only increase waiting time  
UponSend ==                
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"   
                            THEN 0
                            ELSE IF /\ pc[p] = "send" 
                                    /\ break_timer[p] = 0 
                                    /\ waiting_time[p, q] < time_out[p, q]
                            THEN waiting_time[p, q] + 1
                            ELSE waiting_time[p, q]]
  /\ UNCHANGED << suspected, time_out >>                           
   
\*  - For every pair of processes <<snder, rcver>>, remove an arbitrary set of 
\*  messages in msgBuf[snder, rcver]. The obtained result must satisfy partially 
\*  synchronous constraints. Messages sent to crashed processes are ignored.
\*  - Set del'[rcver, snder] = msgBuf'[snder, rcver] # msgBuf[snder, rcver] for 
\*  every snder, for every active "del" rcver. We do not need to know what messages 
\*  have been delivered.  
Deliver ==
  /\ subround = "del"
  /\ subround' = "comp"     
  /\ msgBuf' \in MsgAgePowerSet 
  /\ \A snder, rcver \in Proc : 
          IF pc[rcver] = "crash"
          THEN msgBuf'[snder, rcver] = {} <: {Int}
          ELSE IF pc[rcver] = "del" /\ break_timer[rcver] = 0
          THEN /\ msgBuf'[snder, rcver] \subseteq msgBuf[snder, rcver]
               /\ \A k \in msgBuf'[snder, rcver] : k < Delta 
          ELSE msgBuf'[snder, rcver] = msgBuf[snder, rcver]      
  /\ del' = [<< rcver, snder >> \in Proc \times Proc |->
                    IF pc[rcver] = "crash"                                                             
                    THEN FALSE                    
                    ELSE IF pc[rcver] = "del" /\ break_timer[rcver] = 0 
                    THEN msgBuf'[snder, rcver] # msgBuf[snder, rcver]                           
                    ELSE del[rcver, snder] ] 
  /\ UNCHANGED << pc, break_timer, fromLastSend >>
                      
\*  - If an active rcver has not received any messages from a snder in this step,  
\*  and has waited for snder less than time_out[rcver, snder], then it increases 
\*  waiting_time[rcver, snder] by 1. If waiting-time[rcver, snder] already equals
\*  to time-out[rcver, snder], the waiting time is unchanged. This optimization 
\*  is used to reduced the number of states.
\*  - If received some message from a suspected process, update the prediction,
\*  and increase the timeout.                      
UponReceive ==                                          
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash" 
                            THEN 0
                            ELSE IF pc[p] = "del"/\ break_timer[p] = 0  
                            THEN IF del'[p, q] 
                                 THEN 0
                                 ELSE IF waiting_time[p, q] < time_out[p, q] 
                                 THEN waiting_time[p, q] + 1           
                                 ELSE waiting_time[p, q]
                            ELSE waiting_time[p, q]]      
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                            CASE pc[p] = "crash" ->  
                                    FALSE
                              [] pc[p] = "del" /\ break_timer[p] = 0 /\ del'[p, q] /\ suspected[p, q] -> 
                                    FALSE
                              [] OTHER -> 
                                    suspected[p, q] ]                                  
  /\ time_out' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"   
                            THEN 0
                            ELSE IF /\ pc[p] = "del" 
                                    /\ break_timer[p] = 0
                                    /\ suspected[p, q]                                    
                                    /\ ~suspected'[p, q]  
                            THEN time_out[p, q] + 1
                            ELSE time_out[p, q]]   
    
      
\*  - If the waiting time equals the time-out, change the predicition.
\*  - Update the waiting time.    
Comp ==
  /\ suspected' = [<< p, q >> \in Proc \times Proc |-> 
                      CASE pc[p] = "crash" ->  
                                FALSE
                        [] /\ pc[p] = "comp" 
                           /\ p # q
                           /\ break_timer[p] = 0 
                           /\ ~del[p, q] 
                           /\ waiting_time[p, q] = time_out[p, q] -> 
                                TRUE
                        [] OTHER -> 
                                suspected[p, q] ]
  /\ waiting_time' = [<< p, q >> \in Proc \times Proc |-> 
                            IF pc[p] = "crash"    
                            THEN 0
                            ELSE IF /\ pc[p] = "comp" 
                                    /\ break_timer[p] = 0 
                                    /\ waiting_time[p, q] < time_out[p, q]
                                    /\ ~suspected'[p, q]
                            THEN waiting_time[p, q] + 1
                            ELSE waiting_time[p, q]]
  /\ UNCHANGED << time_out >>                               
  
  
\* Partially synchronous constraint for relative process speed. This constraint
\* is checked in only the scheduling step.          
PhiConstraint == 
  \A i \in Proc : pc'[i] # "crash" => /\ 0 <= break_timer'[i] 
                                      /\ break_timer'[i] < Phi
                                  
\* Partially synchronous constraint for message delay. This constraint is checked
\* in only the delivery step.
DeltaConstraint ==
  subround = "del" => 
      (\A rcver \in Proc : 
               (pc[rcver] = "del" /\ break_timer[rcver] = 0) 
            => (\A snder \in Proc : \A k \in msgBuf'[snder, rcver] : k < Delta))   
                                        

\* Constraints on behaviors of crashed processes: their speed, predictions and  
\* upcoming messages can be ignored. Similar to PhiConstraint, this contraint
\* is checked in only the scheduling step.  
CrashConstraint ==
  /\ Cardinality({p \in Proc : pc'[p] = "crash"}) <= F
  /\ \A p \in Proc : 
        pc'[p] = "crash"  
            => /\ break_timer'[p] = 0
               /\ \A q \in Proc : /\ del'[p, q] = FALSE                                                                    
                                  /\ msgBuf'[q, p] = {} <: {Int}   
  
\* Transitions                                             
Next == 
  \/ /\ Schedule          \* Mark a subset of Proc as active ones               
     /\ PhiConstraint     \* A new schedule must satisfy Phi and                               
     /\ AgeIncrease       \* Move to a next time point
     /\ UNCHANGED del     \* No delivery in the schedule step
     /\ CrashConstraint   \* Crash constraints              
     /\ UponCrash         \* Only for crashed processes         
  \/ /\ AddNewMsgs        \* New messages appear in the message buffers
     /\ UponSend          \* Only increase wating time        
  \/ /\ Deliver           \* Deliver messages
     /\ DeltaConstraint   \* Check the Delta constraint                         
     /\ UponReceive       \* Update failure detectors based on incoming messages                          
  \/ /\ subround = "comp"    \* The environment updates only the variable subround
     /\ subround' = "sched"
     /\ UNCHANGED << msgBuf, del, pc, break_timer, fromLastSend >>
     /\ Comp               

\* Check only StrongCompleteness and EventualStrongAccuracy with Spec  
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
               
\* Type information - very simple ones
TypeOK ==
  /\ pc \in [Proc -> Action]
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) <= F
  /\ del \in [Proc \times Proc -> BOOLEAN]  
  /\ msgBuf \in [Proc \times Proc -> SUBSET Int]
  /\ subround \in {"sched", "send", "del", "comp"}
  /\ break_timer \in [Proc -> Int] 
  /\ waiting_time \in [ Proc \times Proc -> Int]
  /\ suspected \in [Proc \times Proc -> BOOLEAN]  
  /\ time_out \in [ Proc \times Proc -> Int]

\* More complex constraints on possible values of variables             
ComplexTypeInfo ==
  /\ msgBuf \in [ Proc \times Proc -> SUBSET MsgAge ]
  /\ \A rcver \in Proc : 
          IF pc[rcver] = "crash"  
          THEN \A snder \in Proc : 
                      /\ msgBuf[snder, rcver] = {} <: {Int}
                      /\ time_out[rcver, snder] = 0
                      /\ waiting_time[rcver, snder] = 0
                      /\ ~del[rcver, snder]              
                      /\ ~suspected[rcver, snder]  
                      /\ break_timer[rcver] = 0
          ELSE \A snder \in Proc : 
                  \A k \in msgBuf[snder, rcver] : k < Delta + 3 * Phi                      
  /\ \A rcver \in Proc : 
        ((subround = "comp" /\ pc[rcver] = "del" /\ break_timer[rcver] = 0)
            => (\A snder \in Proc : \A k \in msgBuf[snder, rcver] : /\ 0 <= k 
                                                                    /\ k < Delta))       
  /\ break_timer \in [ Proc -> Break_Period ]  
  /\ \A p \in Proc : IF pc[p] = "crash"
                     THEN break_timer[p] = 0
                     ELSE break_timer[p] < Phi  
  /\ suspected \in [Proc \times Proc -> BOOLEAN]  
  /\ \A p, q \in Proc : pc[p] = "crash" => suspected[p, q] = FALSE
  /\ time_out \in [ Proc \times Proc -> TOSet ]
  /\ \A p, q \in Proc : pc[p] = "crash" => time_out[p, q] = 0    
  /\ \A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash")
                            => (time_out[p, q] # 0)  
  /\ waiting_time \in [ Proc \times Proc -> TOSet ]
  /\ \A p, q \in Proc : waiting_time[p, q] <= time_out[p, q]                  
                
\* Eventually every process that crashes is permanently suspected by every correct 
\* process.
StrongCompleteness == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] = "crash") => suspected[p, q])

\* There is a time after which correct processes are not suspected by any correct 
\* process. 
EventualStrongAccuracy == 
  <>[](\A p, q \in Proc : (pc[p] # "crash" /\ pc[q] # "crash") => ~suspected[p, q])
  
\* The following is a list of constraints in my inductive invariant. This inductive
\* invariant holds only in the postfix in which (1) every process that crashes is 
\* permanently suspected by every correct, and (2) correct processes are not suspected 
\* by any correct process. These constraints are: 
\*  (1) FCrashes                    (7)  WaitingTimeImpliesMsgAge
\*  (2) CompletenessAndAccuracy     (8)  WaitingTimeImpliesPC
\*  (3) TOVal                       (9)  BreakTimerVal
\*  (4) WaitingTimeVal              (10) FromLastSendVal
\*  (5) MsgBufVal                   (11) ImmediatelyAfterDelivery      
\*  (6) NotEmptyChan                (12) DelVal  
\*  

\* (1) Set #crashed = F
FCrashes ==   
  /\ pc \in [Proc -> Action]                                            
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) = F                                                                                                                     

\* (2) Every prediction is permanently correct. 
CompletenessAndAccuracy ==
  suspected = [ << p, q >> \in Proc \times Proc |-> IF pc[p] = "crash"
                                                    THEN FALSE
                                                    ELSE pc[q] = "crash" ]
\* (3) For every pair of processes, its corresponding time-out has a fixed value.  
\* If pc[p] = "crash", then 0. Otherwise, TOGuard.
TOVal == 
  time_out = [ <<p, q>> \in Proc \times Proc |-> 
                  IF pc[p] = "crash" 
                  THEN 0
                  ELSE TOGuard]                                                           

\* (4) For every pair of processes <<p, q>>, we have three cases:
\*  - If processes p and q are the same, then  waiting_time[p, q] = 0.
\*  - If orocesses p and q are different, and pc[p] is already "crash", then we 
\*  set waiting_time[p, q] = 0.
\*  - If process p is correct and process q is crashed, then waiting_time[p, q] 
\*  is permanently equals TOGuard, i.e. waiting_time[p, q] = time_out[p, q].
\*  - If these processes are different and correct, then waiting_time[p, q] is 
\*  less than time_out[p, q], e.g. waiting_time[p, q] < time_out[p, q].   
WaitingTimeVal ==
  /\ waiting_time \in [ Proc \times Proc -> TOSet]        
  /\ \A p, q \in Proc :                                                  
            IF pc[p] = "crash"
            THEN waiting_time[p, q] = 0
            ELSE IF pc[q] = "crash"
            THEN waiting_time[p, q] = time_out[p, q] 
            ELSE waiting_time[p, q] < time_out[p, q]   
                                         

\* The postfix requires that every message which was sent by a crashed process was
\* already delivered. By our abstraction, we know that message ages are not greater
\* than Delta. 
MsgBufVal ==
  /\ msgBuf \in MsgAgePowerSet               
  /\ \A rcver, snder \in Proc :                                         
          IF pc[rcver] = "crash" \/ pc[snder] = "crash" 
          THEN msgBuf[snder, rcver] = {} <: {Int}
          ELSE \A k \in msgBuf[snder, rcver] : k <= Delta  
             
\* While waiting_time is measured by a local clock, fromLastSend is measured by
\* the local clock. Since the speed of every local clock is slower than the global
\* clock's speed, if waiting_time[rcver, snder] > fromLastSend[snder]) for a pair of
\* correct processes, then process rcver has not received the message which was sent
\* in the last execution of Send by process q.
NotEmptyChan ==          
  \A rcver, snder \in Proc :                                                 
      (( /\ pc[rcver] # "crash"
         /\ pc[snder] # "crash"
         /\ waiting_time[rcver, snder] > fromLastSend[snder])
            => msgBuf[snder, rcver] # {} <: {Int})
            
\*  1) The 1st constraint is based on another constraint: every correct process must
\*  execute the primitive Send at least once in every time interval with 3 * Phi
\*  ticks. If waiting_time[rcver, snder] >= 3 * Phi, then we know that there exists 
\*  a time interval [t + 1, t + 3 * Phi ] for some natural number t such that process
\*  rcver does not receive any message from process snder. By the above observation, 
\*  we know that process snder must send a message m before the time t + 3 * Phi. 
\*  And this message has not received by process rcver. Therefore, its age must not
\*  be smaller than waiting_time[rcver, snder] - 3 * Phi. Because of our abstraction,
\*  its maximum age is Delta.
\*  2) The 2nd constraint is similar to the 1st one but has an addition condition that
\*  the message buffer msgBuf[snder, rcver] is not empty.
WaitingTimeImpliesMsgAge ==            
  /\ \A rcver, snder \in Proc :                                                 
        ((  /\ pc[rcver] # "crash"
            /\ pc[snder] # "crash"
            /\ waiting_time[rcver, snder] >= 3 * Phi )         
                => (\E k \in msgBuf[snder, rcver] : 
                        \/ k = Delta
                        \/ k >= waiting_time[rcver, snder] - 3 * Phi))
  /\ \A rcver, snder \in Proc :                                                 
        ((  /\ pc[rcver] # "crash"
            /\ pc[snder] = "crash"
            /\ msgBuf[snder, rcver] # {} <: {Int}
            /\ waiting_time[rcver, snder] >= 3 * Phi )         
                => (\E k \in msgBuf[snder, rcver] : 
                        \/ k = Delta
                        \/ k >= waiting_time[rcver, snder] - 3 * Phi))         
            
\*  - If waiting_time[rcver, snder] = 3 * Phi + Delta, correct process rcver does 
\*  not receive any message from correct process snder. By the argument in the 
\*  constraint WaitingTimeImpliesMsgAge, we know that there exists a message whose 
\*  age in the message channel msgBuf[snder, rcver]. By the DeltaConstraint, it
\*  follows that process rcver cannot execute Receive when its waiting time for 
\*  process snder reaches 3 * Phi + Delta. Therefore, pc[rcver] at the time point
\*  3 * Phi + Delta is either "send" or "comp".      
\*  - By similar arguments, process rcver cannot execute the primitive Receive when 
\*  its waiting time for process snder reaches 3 * Phi + Delta + 1. Hence, pc[rcver] 
\*  at the time point 3 * Phi + Delta + 1 should be "comp".              
WaitingTimeImpliesPC ==       
  /\ \A rcver, snder \in Proc :                                         
         (( /\ pc[rcver] # "crash"
            /\ pc[snder] # "crash"
            /\ waiting_time[rcver, snder] = 3 * Phi + Delta )
                  => ( \/ pc[rcver] = "send" 
                       \/ pc[rcver] = "comp" )) 
  /\ \A rcver, snder \in Proc :                                         
          (( /\ pc[rcver] # "crash"
             /\ pc[snder] # "crash"
             /\ waiting_time[rcver, snder] = Delta + 3 * Phi + 1)
                  => pc[rcver] = "send")            
 
\* No correct process is frozen in any time interval with Phi time points. After
\* a process crashes, its break timer is reset to 0.                   
BreakTimerVal ==
  /\ break_timer \in [Proc -> Break_Period]                                
  /\ \A p \in Proc : IF pc[p] = "crash"                                 
                     THEN break_timer[p] = 0
                     ELSE break_timer[p] < Phi 
 
\* The possible value of fromLastSend[i] is related to its pc[i] and break_timer[i].                     
FromLastSendVal ==
  /\ fromLastSend \in [Proc -> FromLastSendSet]                   
  /\ \A p \in Proc :                                                    \* 19
          \/ /\ pc[p] = "crash" 
             /\ fromLastSend[p] = 0
          \/ /\ pc[p] = "send" 
             /\ fromLastSend[p] = break_timer[p]
             /\ fromLastSend[p] < Phi
          \/ /\ pc[p] = "del" 
             /\ fromLastSend[p] >= break_timer[p] + 1
             /\ fromLastSend[p] <= Phi + break_timer[p]
          \/ /\ pc[p] = "comp" 
             /\ fromLastSend[p] >= break_timer[p] + 2
             /\ fromLastSend[p] <= 2 * Phi + break_timer[p]                                       
                    
\* After correct process rcver executes Receiver, the rest of messages which were
\* sent to process rcver are younger than Delta years .                      
ImmediatelyAfterDelivery ==                     
  \A rcver \in Proc : 
      (( /\ pc[rcver] = "del"
         /\ break_timer[rcver] = 0)
              => (\A snder \in Proc : \A k \in msgBuf[snder, rcver] : k < Delta))  
           
\* In this postfix, a correct process never receives a message from a crashed one.
\* Moreover, del[p, p] is always FALSE.           
DelVal ==              
  /\ del \in [Proc \times Proc -> BOOLEAN]                                
  /\ \A snder, rcver \in Proc :                                         
        ((pc[snder] = "crash" \/ pc[rcver] = "crash")
            => ~del[rcver, snder])  
 
\* Interesting constraints in my inductive invariant             
PostfixConstraints ==      
  /\ FCrashes                                                             
  /\ CompletenessAndAccuracy  
  /\ TOVal  
  /\ MsgBufVal
  /\ BreakTimerVal
  /\ ImmediatelyAfterDelivery
  /\ DelVal
  /\ WaitingTimeVal
  /\ WaitingTimeImpliesMsgAge  
  /\ WaitingTimeImpliesPC  
  /\ FromLastSendVal  
  /\ NotEmptyChan
  
\* Only checking the inductive invariant after every correct process finishes its 
\* turn. In other words, when subround = "sched".     
IndInvInPostfix ==
  \/ subround \in {"send", "del", "comp"} 
  \/ /\ subround = "sched"
     /\ PostfixConstraints
  
\* Initial states in the postfix         
PostfixInit ==
  /\ subround = "sched"
  /\ PostfixConstraints  
  
\* The specification of the postfix  
PostfixSpec == PostfixInit /\ [][Next]_vars /\ WF_vars(Next)

\* Eventually 
PostfixIndInv ==                                                           
  <>[]( IndInvInPostfix)


\* The following describes an inductive invariant in this algorithm which
\* allow that the number of crashes increases after one transition.  
Crash_IndInv ==  
  /\ pc \in [Proc -> Action]
  /\ Cardinality({p \in Proc : pc[p] = "crash"}) <= F

\* Following constraints on time_out are used in IndInv.  
Timeout_IndInv ==  
  /\ time_out \in [ Proc \times Proc -> TOSet]
  /\ \A p \in Proc : 
        /\ time_out[p, p] = 0
        /\ pc[p] = "crash" => (\A q \in Proc : time_out[p, q] = 0)
        /\ pc[p] # "crash" => (\A q \in Proc \ {p} : time_out[p, q] > 0)
        
\* Following constraints on waiting_time are used in IndInv.       
WaitingTime_IndInv ==         
  /\ waiting_time \in [ Proc \times Proc -> TOSet]
  /\ \A rcver \in Proc : 
        /\ waiting_time[rcver, rcver] = 0
        /\ pc[rcver] = "crash" 
              => (\A snder \in Proc : waiting_time[rcver, snder] = 0)
        /\ pc[rcver] # "crash" 
              => \A snder \in Proc \ {rcver} : 
                    /\ waiting_time[rcver, snder] <= time_out[rcver, snder]
                    /\ (  /\ time_out[rcver, snder] = TOGuard
                          /\ waiting_time[rcver, snder] = time_out[rcver, snder] )
                              => pc[snder] = "crash"
                    /\ (  /\ time_out[rcver, snder] = TOGuard 
                          /\ pc[snder] # "crash" )
                              => waiting_time[rcver, snder] < time_out[rcver, snder]
  /\ WaitingTimeImpliesPC
                            
                              
\* Only for checking IndInv.
FromLastSend_IndInv == FromLastSendVal

\* Following constraints on msgBuf are used in IndInv.
EmptyChan ==  
  \A rcver, snder \in Proc :                                                 
      (( /\ pc[rcver] # "crash"         
         /\ waiting_time[rcver, snder] = TOGuard)
            => msgBuf[snder, rcver] = {} <: {Int})

MsgBuf_IndInv ==  
  /\ msgBuf \in MsgAgePowerSet               
  /\ \A rcver, snder \in Proc :                                         
          IF pc[rcver] = "crash" 
          THEN msgBuf[snder, rcver] = {} <: {Int}
          ELSE \A k \in msgBuf[snder, rcver] : k <= Delta
  /\ NotEmptyChan
  /\ EmptyChan
  /\ WaitingTimeImpliesMsgAge
  /\ WaitingTimeImpliesPC
  
BreakTimer_IndInv == BreakTimerVal

\* Following constraints on del are used in IndInv.
Del_IndInv ==
  /\ del \in [Proc \times Proc -> BOOLEAN]
  /\ \A rcver \in Proc :         
        pc[rcver] = "crash" => \A snder \in Proc : ~del[rcver, snder]
                               
\* Following constraints on subround are used in IndInv.                                    
Subround_IndInv == subround \in {"sched", "send", "del", "comp"}                                
   
\* Following constraints on suspected are used in IndInv.                              
Suspect_IndInv ==
  /\ suspected \in [Proc \times Proc -> BOOLEAN]
  /\ \A p \in Proc : 
          /\ ~suspected[p, p]
          /\ pc[p] = "crash" => \A q \in Proc \ {p} : ~suspected[p, q]
          /\ pc[p] # "crash" 
                => (\A q \in Proc \ {p} : 
                      suspected[p, q] => waiting_time[p, q] = time_out[p, q])

\* Following constraints on waitingtime and crashed processes are used in IndInv.
WaitingTimeCrashPC ==
  \A rcver, snder \in Proc :                                         
      ( pc[rcver] # "crash" /\ pc[snder] = "crash" )
            => \/ msgBuf[snder, rcver] = {} <: {Int}
               \/ /\ msgBuf[snder, rcver] # {} <: {Int} 
                  /\ waiting_time[rcver, snder] = 3 * Phi + Delta 
                          => ( \/ pc[rcver] = "send" 
                               \/ pc[rcver] = "comp" ) 
                  /\ waiting_time[rcver, snder] = 3 * Phi + Delta + 1 
                          => ( \/ pc[rcver] = "send" ) 

\* Inductive invariant
IndInv ==
  \/ subround \in {"send", "del", "comp"}
  \/ /\ Crash_IndInv
     /\ Timeout_IndInv  
     /\ WaitingTime_IndInv     
     /\ BreakTimer_IndInv
     /\ FromLastSend_IndInv
     /\ MsgBuf_IndInv      
     /\ ImmediatelyAfterDelivery     
     /\ Del_IndInv     
     /\ Suspect_IndInv     
     /\ Subround_IndInv     
     /\ WaitingTimeCrashPC     
     
\* Whilte we can write Init_IndInv == subround = "sched" /\ IndInv, APALACHE
\* complains about no assignment strategy.      
Init_IndInv ==
  /\ subround = "sched"
  /\ Crash_IndInv
  /\ Timeout_IndInv  
  /\ WaitingTime_IndInv
  /\ BreakTimer_IndInv
  /\ FromLastSend_IndInv
  /\ MsgBuf_IndInv      
  /\ ImmediatelyAfterDelivery
  /\ Del_IndInv
  /\ Suspect_IndInv
  /\ Subround_IndInv    
  /\ WaitingTimeCrashPC
     
Spec_IndInv == Init_IndInv /\ [][Next]_vars /\ WF_vars(Next)



\* Test case configurations's for APALACHE 
(*
ConstInit_N1T0F0P1D0 == 
  /\ N \in {1} 
  /\ T \in {0} 
  /\ F \in {0} 
  /\ Phi \in {1} 
  /\ Delta \in {0} 
  /\ Proc \in {1..1}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {5}
  /\ TODefault \in {1}
  /\ TOSet \in {0..5}
  /\ Break_Period \in {0..0}
  /\ MsgAgePowerSet \in {[(1..1) \times (1..1) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..2}

  ConstInit_N1T1F1P1D0 == 
  /\ N \in {1} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {1} 
  /\ Delta \in {0} 
  /\ Proc \in {1..1}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {5}
  /\ TODefault \in {1}
  /\ TOSet \in {0..5}
  /\ Break_Period \in {0..0}
  /\ MsgAgePowerSet \in {[(1..1) \times (1..1) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..2}

  ConstInit_N2T0F0P1D0 == 
  /\ N \in {2} 
  /\ T \in {0} 
  /\ F \in {0} 
  /\ Phi \in {1} 
  /\ Delta \in {0} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {5}
  /\ TODefault \in {1}
  /\ TOSet \in {0..5}
  /\ Break_Period \in {0..0}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..2}  

ConstInit_N2T1F1P1D0 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {1} 
  /\ Delta \in {0} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {5}
  /\ TODefault \in {1}
  /\ TOSet \in {0..5}
  /\ Break_Period \in {0..0}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..2}   

ConstInit_N2T0F0P2D0 == 
  /\ N \in {2} 
  /\ T \in {0} 
  /\ F \in {0} 
  /\ Phi \in {2} 
  /\ Delta \in {0} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {8}
  /\ TODefault \in {1}
  /\ TOSet \in {0..8}
  /\ Break_Period \in {0..1}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..5}   

ConstInit_N2T1F1P2D0 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {2} 
  /\ Delta \in {0} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..0} 
  /\ TOGuard \in {8}
  /\ TODefault \in {1}
  /\ TOSet \in {0..8}
  /\ Break_Period \in {0..1}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..0)]}
  /\ FromLastSendSet \in {0..5}   

ConstInit_N2T0F0P2D1 == 
  /\ N \in {2} 
  /\ T \in {0} 
  /\ F \in {0} 
  /\ Phi \in {2} 
  /\ Delta \in {1} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..1} 
  /\ TOGuard \in {9}
  /\ TODefault \in {1}
  /\ TOSet \in {0..9}
  /\ Break_Period \in {0..1}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..1)]}
  /\ FromLastSendSet \in {0..5}    

ConstInit_N2T1F1P2D1 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {2} 
  /\ Delta \in {1} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..1} 
  /\ TOGuard \in {9}
  /\ TODefault \in {1}
  /\ TOSet \in {0..9}
  /\ Break_Period \in {0..1}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..1)]}
  /\ FromLastSendSet \in {0..5}     
     
ConstInit_N2T1F1P2D2 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {2} 
  /\ Delta \in {2} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..2} 
  /\ TOGuard \in {10}
  /\ TODefault \in {1}
  /\ TOSet \in {0..10}
  /\ Break_Period \in {0..1}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..2)]}
  /\ FromLastSendSet \in {0..5}   

ConstInit_N2T1F1P3D2 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {3} 
  /\ Delta \in {2} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..2} 
  /\ TOGuard \in {13}
  /\ TODefault \in {1}
  /\ TOSet \in {0..13}
  /\ Break_Period \in {0..2}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..2)]}
  /\ FromLastSendSet \in {0..8}      

ConstInit_N2T1F1P3D3 == 
  /\ N \in {2} 
  /\ T \in {1} 
  /\ F \in {1} 
  /\ Phi \in {3} 
  /\ Delta \in {3} 
  /\ Proc \in {1..2}
  /\ MsgAge \in  {0..3} 
  /\ TOGuard \in {14}
  /\ TODefault \in {1}
  /\ TOSet \in {0..14}
  /\ Break_Period \in {0..2}
  /\ MsgAgePowerSet \in {[(1..2) \times (1..2) -> SUBSET (0..3)]}
  /\ FromLastSendSet \in {0..8}   
*)
  
=============================================================================
\* Modification History
\* Last modified Sun Mar 08 22:31:28 CET 2020 by tthai
\* Created Fri Nov 29 14:06:49 CET 2019 by tthai
