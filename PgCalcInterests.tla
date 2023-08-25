---- MODULE PgCalcInterests ----
EXTENDS PgIsolationCommon

CONSTANT isolation_level
ASSUME isolation_level \in isolation_levels

(* --algorithm read_skew
variables
  exec = <<>>;
  data =
    1 :> [client |-> "alice", amount |-> 100000] @@
    2 :> [client |-> "bob", amount |-> 20000] @@
    3 :> [client |-> "bob", amount |-> 80000];


define
  AllDone == \A session \in 1..2: pc[session] = "Done"
  NoReadSkew ==
    AllDone => (Satisfies(exec, isolation_level) =>
                  /\ data[2].amount = 20000
                  /\ data[3].amount = 70000)
end define;

macro Guard(counter, target) begin
  await counter = target;
  counter := counter + 1;
end macro;

\* Only retake snapshot for the read committed isolation level. For the
\* snapshot isolation and serializable levels, the snapshot was taken at
\* the beginning of the session and should remain unchanged.
macro RetakeSnapshot(old, new) begin
  old := IF isolation_level = "RC" THEN new ELSE old;
end macro;

process update = 1
variables
  snapshot = data;
  v;

begin
  WITHDRAW:
    v := [snapshot[3] EXCEPT !.amount = snapshot[3].amount - 10000];
    exec := exec \o
      <<[parentState |-> snapshot, transaction |-> <<W(3, v)>>]>>;
    data := [snapshot EXCEPT ![3] = v];
end process;

process deposit_interests = 2
variables
  counter = 0;
  snapshot = data;
  enough_fund = FALSE;
  v2, v3;

begin
  ENOUGH_FUND:
    Guard(counter, 0);
    v2 := snapshot[2];
    v3 := snapshot[3];
    enough_fund := v2.amount + v3.amount >= 100000;
    exec := exec \o
      <<[parentState |-> snapshot, transaction |-> <<R(2, v2), R(3, v3)>>]>>;
  DEPOSIT:
    Guard(counter, 1);
    await enough_fund;
    RetakeSnapshot(snapshot, data);
    v2 := [snapshot[2] EXCEPT !.amount = @ + @ \div 100];
    v3 := [snapshot[3] EXCEPT !.amount = @ + @ \div 100];
    exec := exec \o
      <<[parentState |-> snapshot, transaction |-> <<W(2, v2), W(3, v3)>>]>>;
    data := [snapshot EXCEPT ![2] = v2, ![3] = v3];
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ee378a51" /\ chksum(tla) = "743ac734")
\* Process variable snapshot of process update at line 38 col 3 changed to snapshot_
CONSTANT defaultInitValue
VARIABLES exec, data, pc

(* define statement *)
AllDone == \A session \in 1..2: pc[session] = "Done"
NoReadSkew ==
  AllDone => (Satisfies(exec, isolation_level) =>
                /\ data[2].amount = 20000
                /\ data[3].amount = 70000)

VARIABLES snapshot_, v, counter, snapshot, enough_fund, v2, v3

vars == << exec, data, pc, snapshot_, v, counter, snapshot, enough_fund, v2, 
           v3 >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ exec = <<>>
        /\ data = (1 :> [client |-> "alice", amount |-> 100000] @@
                   2 :> [client |-> "bob", amount |-> 20000] @@
                   3 :> [client |-> "bob", amount |-> 80000])
        (* Process update *)
        /\ snapshot_ = data
        /\ v = defaultInitValue
        (* Process deposit_interests *)
        /\ counter = 0
        /\ snapshot = data
        /\ enough_fund = FALSE
        /\ v2 = defaultInitValue
        /\ v3 = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "WITHDRAW"
                                        [] self = 2 -> "ENOUGH_FUND"]

WITHDRAW == /\ pc[1] = "WITHDRAW"
            /\ v' = [snapshot_[3] EXCEPT !.amount = snapshot_[3].amount - 10000]
            /\ exec' =       exec \o
                       <<[parentState |-> snapshot_, transaction |-> <<W(3, v')>>]>>
            /\ data' = [snapshot_ EXCEPT ![3] = v']
            /\ pc' = [pc EXCEPT ![1] = "Done"]
            /\ UNCHANGED << snapshot_, counter, snapshot, enough_fund, v2, v3 >>

update == WITHDRAW

ENOUGH_FUND == /\ pc[2] = "ENOUGH_FUND"
               /\ counter = 0
               /\ counter' = counter + 1
               /\ v2' = snapshot[2]
               /\ v3' = snapshot[3]
               /\ enough_fund' = (v2'.amount + v3'.amount >= 100000)
               /\ exec' =       exec \o
                          <<[parentState |-> snapshot, transaction |-> <<R(2, v2'), R(3, v3')>>]>>
               /\ pc' = [pc EXCEPT ![2] = "DEPOSIT"]
               /\ UNCHANGED << data, snapshot_, v, snapshot >>

DEPOSIT == /\ pc[2] = "DEPOSIT"
           /\ counter = 1
           /\ counter' = counter + 1
           /\ enough_fund
           /\ snapshot' = (IF isolation_level = "RC" THEN data ELSE snapshot)
           /\ v2' = [snapshot'[2] EXCEPT !.amount = @ + @ \div 100]
           /\ v3' = [snapshot'[3] EXCEPT !.amount = @ + @ \div 100]
           /\ exec' =       exec \o
                      <<[parentState |-> snapshot', transaction |-> <<W(2, v2'), W(3, v3')>>]>>
           /\ data' = [snapshot' EXCEPT ![2] = v2', ![3] = v3']
           /\ pc' = [pc EXCEPT ![2] = "Done"]
           /\ UNCHANGED << snapshot_, v, enough_fund >>

deposit_interests == ENOUGH_FUND \/ DEPOSIT

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == update \/ deposit_interests
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
