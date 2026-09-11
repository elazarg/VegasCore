# Outcomes and utilities

Compiler correctness should first identify an observable target result and a
decoder to the source result. Utility preservation then follows only for
utilities that factor through that decoder, or under an additional bound for
target-specific costs and signals.

Runtime traces may contain timing, retries, receipts, message order, fees, and
failure information absent from the source outcome. Players who value those
features are playing a richer game. Generic simulation and equilibrium
transport belong in `GameTheoryExtensions`; a Vegas theorem must supply the
concrete source/target simulation certificate.

Support correspondence, equality of outcome laws, expected-utility equality,
and equilibrium transport are distinct claims. Active documentation and audits
must name the strongest one actually proved.
