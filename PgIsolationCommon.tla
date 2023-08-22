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

====
