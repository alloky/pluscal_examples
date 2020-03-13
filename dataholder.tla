------------------------------ MODULE dataholder ------------------------------
EXTENDS Integers, TLC, Naturals, Sequences, FiniteSets
CONSTANT N
ASSUME Nasm == (N \in Nat) /\ (N > 0)

(* --algorithm dataholder {
variables cached = FALSE; 
         checksum = 0;
         numCalced = 0;
         locCached = [p1 \in 0..N-1 |-> FALSE];
         locCheck = [p2 \in 0..N-1 |-> 0]; 
         locAct = [p3 \in 0..N-1 |-> 0]; 
    
define {
    BAD(i) == locAct[i] = 1 /\ locCached[i] = TRUE /\ locCheck[i] = 0
    PCorrect == \A i \in 0..N-1 : ~BAD(i)  
}


macro WrapInc(p)  {
    p := p + 1
}

\*procedure Copy() {
\*cop1:  locCached[self] := cached;
\*cop2:  locCheck[self] := checksum;
\*    return;
\*}

procedure Copy() {
cop1:  locCheck[self] := checksum;
cop2:  locCached[self] := cached;
    return;
}


procedure getSum()
    variables c = FALSE; {
gsc:  c := cached;
gsif: if (~c) {
         checksum := 20;
         WrapInc(numCalced);
         cached := TRUE;   
      };
gssum: locCheck[self] := checksum;  
gsret: return;
}


process (proc \in 0..N-1) {
a: call Copy();
c: locAct[self] := 1;
b: call getSum();
}

} *)
\* BEGIN TRANSLATION
\* Label c of process proc at line 52 col 4 changed to c_
VARIABLES cached, checksum, numCalced, locCached, locCheck, locAct, pc, stack

(* define statement *)
BAD(i) == locAct[i] = 1 /\ locCached[i] = TRUE /\ locCheck[i] = 0
PCorrect == \A i \in 0..N-1 : ~BAD(i)

VARIABLE c

vars == << cached, checksum, numCalced, locCached, locCheck, locAct, pc, 
           stack, c >>

ProcSet == (0..N-1)

Init == (* Global variables *)
        /\ cached = FALSE
        /\ checksum = 0
        /\ numCalced = 0
        /\ locCached = [p1 \in 0..N-1 |-> FALSE]
        /\ locCheck = [p2 \in 0..N-1 |-> 0]
        /\ locAct = [p3 \in 0..N-1 |-> 0]
        (* Procedure getSum *)
        /\ c = [ self \in ProcSet |-> FALSE]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "a"]

cop1(self) == /\ pc[self] = "cop1"
              /\ locCheck' = [locCheck EXCEPT ![self] = checksum]
              /\ pc' = [pc EXCEPT ![self] = "cop2"]
              /\ UNCHANGED << cached, checksum, numCalced, locCached, locAct, 
                              stack, c >>

cop2(self) == /\ pc[self] = "cop2"
              /\ locCached' = [locCached EXCEPT ![self] = cached]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << cached, checksum, numCalced, locCheck, locAct, c >>

Copy(self) == cop1(self) \/ cop2(self)

gsc(self) == /\ pc[self] = "gsc"
             /\ c' = [c EXCEPT ![self] = cached]
             /\ pc' = [pc EXCEPT ![self] = "gsif"]
             /\ UNCHANGED << cached, checksum, numCalced, locCached, locCheck, 
                             locAct, stack >>

gsif(self) == /\ pc[self] = "gsif"
              /\ IF ~c[self]
                    THEN /\ checksum' = 20
                         /\ numCalced' = numCalced + 1
                         /\ cached' = TRUE
                    ELSE /\ TRUE
                         /\ UNCHANGED << cached, checksum, numCalced >>
              /\ pc' = [pc EXCEPT ![self] = "gssum"]
              /\ UNCHANGED << locCached, locCheck, locAct, stack, c >>

gssum(self) == /\ pc[self] = "gssum"
               /\ locCheck' = [locCheck EXCEPT ![self] = checksum]
               /\ pc' = [pc EXCEPT ![self] = "gsret"]
               /\ UNCHANGED << cached, checksum, numCalced, locCached, locAct, 
                               stack, c >>

gsret(self) == /\ pc[self] = "gsret"
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ c' = [c EXCEPT ![self] = Head(stack[self]).c]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << cached, checksum, numCalced, locCached, 
                               locCheck, locAct >>

getSum(self) == gsc(self) \/ gsif(self) \/ gssum(self) \/ gsret(self)

a(self) == /\ pc[self] = "a"
           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Copy",
                                                    pc        |->  "c_" ] >>
                                                \o stack[self]]
           /\ pc' = [pc EXCEPT ![self] = "cop1"]
           /\ UNCHANGED << cached, checksum, numCalced, locCached, locCheck, 
                           locAct, c >>

c_(self) == /\ pc[self] = "c_"
            /\ locAct' = [locAct EXCEPT ![self] = 1]
            /\ pc' = [pc EXCEPT ![self] = "b"]
            /\ UNCHANGED << cached, checksum, numCalced, locCached, locCheck, 
                            stack, c >>

b(self) == /\ pc[self] = "b"
           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "getSum",
                                                    pc        |->  "Done",
                                                    c         |->  c[self] ] >>
                                                \o stack[self]]
           /\ c' = [c EXCEPT ![self] = FALSE]
           /\ pc' = [pc EXCEPT ![self] = "gsc"]
           /\ UNCHANGED << cached, checksum, numCalced, locCached, locCheck, 
                           locAct >>

proc(self) == a(self) \/ c_(self) \/ b(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Copy(self) \/ getSum(self))
           \/ (\E self \in 0..N-1: proc(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================
