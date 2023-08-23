---- MODULE PgReadCommit ----
EXTENDS PgIsolationCommon

(*  Implement the book 'PostgreSQL 14 Internals' p.52 - 53
      User1:
        BEGIN;
        UPDATE accounts SET amount = amount - 200 WHERE id = 1;
        SELECT * FROM accounts WHERE client = 'alice';
        COMMIT;
      User2:
        SELECT * FROM accounts WHERE client = 'alice';
*)

Satisfies(execs) == CC!executionSatisfiesCT(execs, CC!CT_RC)

(* --algorithm read_commited
variables
  execs = <<>>;
  data = db;

define
  AllDone == \A user \in 1..2: pc[user] = "Done"
  Correct ==
    AllDone => (Satisfies(execs) => data[1].amount = 80000)
end define;

process update_read = 1
variables
  v1 = [data[1] EXCEPT !.amount = data[1].amount - 20000];

begin
  UpdateThenRead:
    \* UPDATE accounts SET amount = amount - 200 WHERE id = 1;
    \* SELECT * FROM accounts WHERE client = 'alice';
    execs := execs \o
      <<[parentState |-> data, transaction |-> <<W(1, v1), R(1, v1)>>]>>;
    data := [data EXCEPT ![1] = v1];
end process;

process read = 2
variable
  v1;

begin
  Read:
    either
      v1 := data[1];
    or
      v1 := [data[1] EXCEPT !.amount = 80000];
    end either;
    execs := execs \o
      <<[parentState |-> data, transaction |-> <<R(1, v1)>>]>>;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "dc973252" /\ chksum(tla) = "944456a0")
\* Process variable v1 of process update_read at line 29 col 3 changed to v1_
CONSTANT defaultInitValue
VARIABLES execs, data, pc

(* define statement *)
AllDone == \A user \in 1..2: pc[user] = "Done"
Correct ==
  AllDone => (Satisfies(execs) => data[1].amount = 80000)

VARIABLES v1_, v1

vars == << execs, data, pc, v1_, v1 >>

ProcSet == {1} \cup {2}

Init == (* Global variables *)
        /\ execs = <<>>
        /\ data = db
        (* Process update_read *)
        /\ v1_ = [data[1] EXCEPT !.amount = data[1].amount - 20000]
        (* Process read *)
        /\ v1 = defaultInitValue
        /\ pc = [self \in ProcSet |-> CASE self = 1 -> "UpdateThenRead"
                                        [] self = 2 -> "Read"]

UpdateThenRead == /\ pc[1] = "UpdateThenRead"
                  /\ execs' =        execs \o
                              <<[parentState |-> data, transaction |-> <<W(1, v1_), R(1, v1_)>>]>>
                  /\ data' = [data EXCEPT ![1] = v1_]
                  /\ pc' = [pc EXCEPT ![1] = "Done"]
                  /\ UNCHANGED << v1_, v1 >>

update_read == UpdateThenRead

Read == /\ pc[2] = "Read"
        /\ \/ /\ v1' = data[1]
           \/ /\ v1' = [data[1] EXCEPT !.amount = 80000]
        /\ execs' =        execs \o
                    <<[parentState |-> data, transaction |-> <<R(1, v1')>>]>>
        /\ pc' = [pc EXCEPT ![2] = "Done"]
        /\ UNCHANGED << data, v1_ >>

read == Read

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == update_read \/ read
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

====
