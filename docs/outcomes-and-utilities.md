# Outcomes and utilities

Compiler correctness should first identify an observable target result and a
decoder to the source result. Utility preservation then follows only for
utilities that factor through that decoder, or under an additional bound for
target-specific costs and signals.

A Vegas source outcome is the public result of a completed program: its
publications and public samples, and nothing a player kept to itself. A
preference over what was never published is not a preference over anything the
program produced, and every later edge would owe a decoder for it.

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
fixed profile, native deviation, and real-valued test of the public source
result, some source deviation achieves at least the native expected test
value.
The witness may depend on that test; this does not identify a single source
policy reproducing the entire outcome law.

`GameTheory.GameForm.UtilitySimulation` is the reusable weaker interface for
edges that bound expected utility rather than reproduce a law. It composes
across successive edges and is obtained from the exact-mixture certificate
when needed. It supplies no extra trace-utility theorem for Vegas without a
concrete bound on those additional preferences.

The interface is indexed by the coalitions whose joint deviations it bounds.
At one-player coalitions it transfers approximate Nash; at every nonempty
coalition it would transfer strong Nash. Honest utility equality alone
reflects either predicate from a compiled profile, so only preservation needs
a bound. The exact-mixture certificate supplies the one-player index only: a
mixture has a component at least as good as its mean for one player, while a
coalition bound needs a single source witness serving every member at once.

That gap is not an artifact. A target that adds a communication channel to the
source carries an exact one-player certificate and admits no coalition
certificate at all, for any strategy translation, because one member can route
private information to another. The witness is
`GameTheory.GameForm.CoalitionWitness.isEmpty_coalitionSimulation`, with
`compiled_not_isStrongNash` recording that strong Nash is lost. Coalition
claims therefore need their own certificate, never a corollary of the
unilateral one.

Channels are not the only obstruction, and reading them as the only one invites
a wrong inference. The value-binding edge adds nothing to the source game — it
is an inclusion on strategies, with the identity on outcomes, so there is no
device for a coalition to exploit — and it still carries only the one-player
index. Its certificate answers a behavioral deviation with a purification
mixture, and the coalition predicate asks only that *some* member fail to gain;
that member may differ between components, so component-wise coalition bounds do
not average. Against *pure* coalition deviations the translation is a point mass
and the obstruction disappears, but the interface has no place to record such a
restriction. So a channel-free edge is not thereby a coalition edge, and the
reason to check is the shape of the certificate, not the presence of a channel.

The channel is not a modelling flourish. `InteractionTests.CoalitionChannel`
runs the same comparison against the actual message application: nature draws a
secret, the first principal alone observes it, and the host's `handle` rejects
every message, so the pool alone carries the secret to the second principal
before any inclusion. That coalition is worth one against a base value of one
half, so no coalition certificate relates the two.

Refuting a new target needs no equilibrium computation.
`UtilitySimulation.isEmpty_of_unmatchedValue` asks for one coalition, one
member, and a target replacement whose value for that member exceeds every
source deviation's, whatever the nonmembers play.
`UtilitySimulation.isEmpty_of_grandCoalitionValue` is the case where the
coalition is everyone, and then the strategy translation drops out entirely:
it is enough that one target profile is worth more to one player than every
source profile.
