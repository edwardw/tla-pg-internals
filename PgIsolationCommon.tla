---- MODULE PgIsolationCommon ----
EXTENDS TLC, Integers, Sequences

db ==
  1 :> [client |-> "alice", amount |-> 100000] @@
  2 :> [client |-> "bob", amount |-> 10000] @@
  3 :> [client |-> "bob", amount |-> 90000]

Codomain(f) == {f[x]: x \in DOMAIN f}
CC == INSTANCE ClientCentric WITH Keys <- DOMAIN db, Values <- Codomain(db)
R(k, v) == CC!r(k, v)
W(k ,v) == CC!w(k, v)

ReduceSet(op(_, _), set, acc) == CC!ReduceSet(op, set, acc)
ReduceSeq(op(_, _), seq, acc) == CC!ReduceSeq(op, seq, acc)

isolation_levels == {"RC", "SI", "SER"}
Satisfies(es, level) ==
  CASE
    level = "RC"  -> CC!executionSatisfiesCT(es, CC!CT_RC)  []
    level = "SI"  -> CC!executionSatisfiesCT(es, CC!CT_SI)  []
    level = "SER" -> CC!executionSatisfiesCT(es, CC!CT_SER)

====
