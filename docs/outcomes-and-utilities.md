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

The checked pending-message compiler supplies an exact finite-mixture
simulation. Besides Nash correspondence, it gives
`Vegas.SourceProgram.Setup.eventPendingGame_deviation_utility_bound`: for a
fixed profile, native deviation, and real-valued test of the terminal source
state, some source deviation achieves at least the native expected test value.
The witness may depend on that test; this does not identify a single source
policy reproducing the entire outcome law.

`GameTheory.GameForm.UtilitySimulation` is the reusable weaker interface for
edges that bound expected utility rather than reproduce a law. It composes
across successive edges and is obtained from the exact-mixture certificate
when needed. It supplies no extra trace-utility theorem for Vegas without a
concrete bound on those additional preferences.
