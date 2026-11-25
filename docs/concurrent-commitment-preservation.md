# Concurrent commitment preservation

The graph theorem is checked in
[SourcePrefixForfeit](../Vegas/Game/SourcePrefixForfeit.lean). The native
capstone `Vegas.native_compileIntendedExtension_preserved` is in
[PrefixClientNash](../Vegas/Game/PrefixClientNash.lean). Both are pinned in
[Paper.lean](../Paper.lean), including the concrete combined binding/reveal
relaxation. The native theorem uses the existing dependency-parametric
`Vegas.serviceGame` and application.

## Checked scope

Both results are uniform over valid dependencies satisfying
`Vegas.EventGraph.RevealRelaxedOrdered`: retain public barriers, causal reads
and same-owner order, while permitting independent private bindings and
independent reveals to complete in either order. The combined instance is
`setup.dataflowGraph.bindingDependencies setup.revealDependencies`.
Private inputs may be correlated.

For every intended ε-Nash equilibrium and every supplied extension under the
full commitment interface, the native first-turn effective-opening source-prefix
clients preserve the same ε against arbitrary raw native policies. The joint
law uses the actual `Vegas.serviceRankedReadout` and actual forfeited payoff
vector. It equals the intended law of the complete terminal source configuration
and ordinary payoff vector. Supported native runs terminate without public
defaults or failed reveals.

The native theorem assumes well formedness, finite players, finite binding
payload types and initial support, a forfeit at least the utility spread, and
the existing asynchronous service and timeliness contracts. There is no source
disclosure, independent-prior, audit, deposit or finite raw-menu premise.
The graph result uses every disclosing extension and every public scheduler.

The [honest native law](../Vegas/Game/PrefixClientOutcomeDistribution.lean) separately
preserves the full configuration/payoff law and clean terminal play of every
intended extension without equilibrium, finite binding catalogue, finite initial
support, source disclosure or utility-bound premises.

## Prescribed clients

At event rank `e`, the prescribed observation is the source-ranked prefix before
`e`, with one default slot per instruction and only the owner's earlier actions,
in rank order. Public-event default markers are retained; private-binding slots
carry `none`, including bindings not yet completed. The typed projected store
is unchanged. Binding omission is replaced by an opaque unopenable submission.

The graph theorem uses clients that disclose every active reveal. Native clients
apply effective opening to the prescribed source-prefix profile: they open exactly when the
opening would be accepted, and otherwise stay silent. The final theorem uses
these clients of the original supplied extension, with no disclosure premise.
Deviators retain their full actual observations, timing, pending traffic and
available native responses.

## Proof ownership and remaining scope

[PrefixClientDeviation](../Vegas/Game/PrefixClientDeviation.lean) composes actual
stopped binding, publication and chance phases into one policy of the existing
source information-graph game that bounds the expected native deviation payoff.
Its conditional sampling retains the full source state and remaining honest suffix
jointly with native traffic; no product prior is assumed. Intermediate native
cuts need not be source prefixes. Actual defaults and source debt are connected
to failed native publications before applying the forfeiture bound.

[PrefixClientNash](../Vegas/Game/PrefixClientNash.lean) derives binding repair
and forced source disclosure internally, retaining the original effective-opening
clients, and combines the deviation bound with the honest full law. The source
fixed-exit comparator is internal; the native equilibrium and final joint law
use the actual forfeited payoff.

Full-source exact correspondence under relaxed dependencies and concurrent
sequential-equilibrium preservation remain separate questions. The checked SE
compiler retains the source information graph.
