---- MODULE PgUpdateAntiPattern ----
EXTENDS PgIsolationCommon

(*  Implement the book 'PostgreSQL 14 Internals' p.53
      User1:
        IF (SELECT amount FROM accounts WHERE id = 1) >= 1000 THEN
          UPDATE accounts SET amount = amount - 1000 WHERE id = 1;
        END IF;
      User2:
        IF (SELECT amount FROM accounts WHERE id = 1) >= 200 THEN
          UPDATE accounts SET amount = amount - 200 WHERE id = 1;
        END IF;

    It *might* fail to meet the business criteria that any account shouldn't
    have negative balance depending on how the two transactions interleave
    with each other. The TLA+ will explore the state space to expose the
    potential failure.
*)

Satisfies(execs) == CC!executionSatisfiesCT(execs, CC!CT_RC)

(* --algorithm update_anti_pattern
variables
  execs = <<>>;
  data = db;

define
  AllNonnegative == \A id \in DOMAIN data: data[id].amount >= 0
  AlwaysNonnegative == [](Satisfies(execs) => AllNonnegative)
end define;

process update \in {20000, 100000}
variables
  counter = 0;
  amount = self;
  enough_fund = FALSE;
  v1;

begin
  Check:
    await counter = 0;
    counter := counter + 1;
    execs := execs \o
      <<[parentState |-> data, transaction |-> <<R(1, data[1])>>]>>;
    enough_fund := data[1].amount >= amount;
  Withdraw:
    await
      /\ counter = 1
      /\ enough_fund;
    counter := counter + 1;
    v1 := [data[1] EXCEPT !.amount = data[1].amount - amount];
    execs := execs \o
      <<[parentState |-> data, transaction |-> <<W(1, v1)>>]>>;
    data := [data EXCEPT ![1] = v1];
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "8b8273e4" /\ chksum(tla) = "6ded5bac")
CONSTANT defaultInitValue
VARIABLES execs, data, pc

(* define statement *)
AllNonnegative == \A id \in DOMAIN data: data[id].amount >= 0
AlwaysNonnegative == [](Satisfies(execs) => AllNonnegative)

VARIABLES counter, amount, enough_fund, v1

vars == << execs, data, pc, counter, amount, enough_fund, v1 >>

ProcSet == ({20000, 100000})

Init == (* Global variables *)
        /\ execs = <<>>
        /\ data = db
        (* Process update *)
        /\ counter = [self \in {20000, 100000} |-> 0]
        /\ amount = [self \in {20000, 100000} |-> self]
        /\ enough_fund = [self \in {20000, 100000} |-> FALSE]
        /\ v1 = [self \in {20000, 100000} |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "Check"]

Check(self) == /\ pc[self] = "Check"
               /\ counter[self] = 0
               /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
               /\ execs' =        execs \o
                           <<[parentState |-> data, transaction |-> <<R(1, data[1])>>]>>
               /\ enough_fund' = [enough_fund EXCEPT ![self] = data[1].amount >= amount[self]]
               /\ pc' = [pc EXCEPT ![self] = "Withdraw"]
               /\ UNCHANGED << data, amount, v1 >>

Withdraw(self) == /\ pc[self] = "Withdraw"
                  /\ /\ counter[self] = 1
                     /\ enough_fund[self]
                  /\ counter' = [counter EXCEPT ![self] = counter[self] + 1]
                  /\ v1' = [v1 EXCEPT ![self] = [data[1] EXCEPT !.amount = data[1].amount - amount[self]]]
                  /\ execs' =        execs \o
                              <<[parentState |-> data, transaction |-> <<W(1, v1'[self])>>]>>
                  /\ data' = [data EXCEPT ![1] = v1'[self]]
                  /\ pc' = [pc EXCEPT ![self] = "Done"]
                  /\ UNCHANGED << amount, enough_fund >>

update(self) == Check(self) \/ Withdraw(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in {20000, 100000}: update(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

====
