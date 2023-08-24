---- MODULE PgReadSkew ----
EXTENDS PgIsolationCommon

CONSTANT isolation_level
ASSUME isolation_level \in isolation_levels

(* --algorithm read_skew
variables
  execs = <<>>;
  data = db;

define
  SumRead(ts) == ReduceSeq(LAMBDA o, acc:
                              IF o.op = "read"
                              THEN acc + o.value.amount
                              ELSE acc,
                           ts, 0)
  Sum(es) == ReduceSeq(LAMBDA e, acc: acc + SumRead(e.transaction), es, 0)

  AllDone == \A session \in 1..2: pc[session] = "Done"
  NoReadSkew ==
    AllDone => (Satisfies(execs, isolation_level) =>
                  /\ Sum(execs) = 100000
                  /\ data[2].amount = 0
                  /\ data[3].amount = 100000)
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

process transfer = 1
variables
  counter = 0;
  snapshot = db;
  up_to_date = db;
  v;

begin
  WITHDRAW:
    Guard(counter, 0);
    v := [snapshot[2] EXCEPT !.amount = snapshot[2].amount - 10000];
    execs := execs \o
      <<[parentState |-> snapshot, transaction |-> <<W(2, v)>>]>>;
    up_to_date := [up_to_date EXCEPT ![2] = v];
  DEPOSIT:
    Guard(counter, 1);
    RetakeSnapshot(snapshot, data);
    v := [snapshot[3] EXCEPT !.amount = snapshot[3].amount + 10000];
    execs := execs \o
      <<[parentState |-> snapshot, transaction |-> <<W(3, v)>>]>>;
    data := [up_to_date EXCEPT ![3] = v];
end process;

process read = 2
variables
  counter = 0;
  snapshot = db;

begin
  READ2:
    Guard(counter, 0);
    execs := execs \o
      <<[parentState |-> snapshot, transaction |-> <<R(2, snapshot[2])>>]>>;
  READ3:
    Guard(counter, 1);
    RetakeSnapshot(snapshot, data);
    execs := execs \o
      <<[parentState |-> snapshot, transaction |-> <<R(3, snapshot[3])>>]>>;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "b700d247" /\ chksum(tla) = "5dafc216")
\* Process variable counter of process transfer at line 42 col 3 changed to counter_
\* Process variable snapshot of process transfer at line 43 col 3 changed to snapshot_
CONSTANT defaultInitValue
VARIABLES execs, data, pc

(* define statement *)
SumRead(ts) == ReduceSeq(LAMBDA o, acc:
                            IF o.op = "read"
                            THEN acc + o.value.amount
                            ELSE acc,
                         ts, 0)
Sum(es) == ReduceSeq(LAMBDA e, acc: acc + SumRead(e.transaction), es, 0)

AllDone == \A session \in 1..2: pc[session] = "Done"
NoReadSkew ==
  AllDone => (Satisfies(execs, isolation_level) =>
                /\ Sum(execs) = 100000
                /\ data[2].amount = 0
                /\ data[3].amount = 100000)

VARIABLES counter_, snapshot_, up_to_date, v, counter, snapshot

vars == << execs, data, pc, counter_, snapshot_, up_to_date, v, counter, 
           snapshot >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ execs = <<>>
        /\ data = db
        (* Process transfer *)
        /\ counter_ = 0
        /\ snapshot_ = db
        /\ up_to_date = db
        /\ v = defaultInitValue
        (* Process read *)
        /\ counter = 0
        /\ snapshot = db
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "WITHDRAW"
                                        [] self = 2 -> "READ2"]

WITHDRAW == /\ pc[1] = "WITHDRAW"
            /\ counter_ = 0
            /\ counter_' = counter_ + 1
            /\ v' = [snapshot_[2] EXCEPT !.amount = snapshot_[2].amount - 10000]
            /\ execs' =        execs \o
                        <<[parentState |-> snapshot_, transaction |-> <<W(2, v')>>]>>
            /\ up_to_date' = [up_to_date EXCEPT ![2] = v']
            /\ pc' = [pc EXCEPT ![1] = "DEPOSIT"]
            /\ UNCHANGED << data, snapshot_, counter, snapshot >>

DEPOSIT == /\ pc[1] = "DEPOSIT"
           /\ counter_ = 1
           /\ counter_' = counter_ + 1
           /\ snapshot_' = (IF isolation_level = "RC" THEN data ELSE snapshot_)
           /\ v' = [snapshot_'[3] EXCEPT !.amount = snapshot_'[3].amount + 10000]
           /\ execs' =        execs \o
                       <<[parentState |-> snapshot_', transaction |-> <<W(3, v')>>]>>
           /\ data' = [up_to_date EXCEPT ![3] = v']
           /\ pc' = [pc EXCEPT ![1] = "Done"]
           /\ UNCHANGED << up_to_date, counter, snapshot >>

transfer == WITHDRAW \/ DEPOSIT

READ2 == /\ pc[2] = "READ2"
         /\ counter = 0
         /\ counter' = counter + 1
         /\ execs' =        execs \o
                     <<[parentState |-> snapshot, transaction |-> <<R(2, snapshot[2])>>]>>
         /\ pc' = [pc EXCEPT ![2] = "READ3"]
         /\ UNCHANGED << data, counter_, snapshot_, up_to_date, v, snapshot >>

READ3 == /\ pc[2] = "READ3"
         /\ counter = 1
         /\ counter' = counter + 1
         /\ snapshot' = (IF isolation_level = "RC" THEN data ELSE snapshot)
         /\ execs' =        execs \o
                     <<[parentState |-> snapshot', transaction |-> <<R(3, snapshot'[3])>>]>>
         /\ pc' = [pc EXCEPT ![2] = "Done"]
         /\ UNCHANGED << data, counter_, snapshot_, up_to_date, v >>

read == READ2 \/ READ3

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == transfer \/ read
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
====
