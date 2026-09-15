# Active compilation tower

This page records checked theorem scope. The [road ahead](a-road-ahead.md)
records the compiler goal; the [graph-to-message plan](typed-message-edge.md)
separates the implemented host from the remaining strategic proof.

## Full failure-aware language

| Boundary | Implementation | Checked result |
| --- | --- | --- |
| Source semantics | `Vegas.Source`: `SourceProgram` | Arbitrary binding and disclosure policies, own-action recall, heterogeneous results, initial secrets, deferred guards, and dependent chance. Every complete run resolves every obligation and satisfies every retained guard. |
| Source to typed graph | `Vegas.Game.GraphCompilation`, `Vegas.Game.GraphSetup` | Exact decoded terminal-state and payout laws; every unilateral graph deviation has one exact source-policy preimage against unchanged opponents. Finite private setup uses shared policies and a state-independent backtranslation. Nash and same-error epsilon-Nash equivalence at compiled profiles, without failure-dominance or finite-domain premises. |
| Typed graph to message host | `Vegas.Graph.MessageApplication`: `GraphRuntime` | Every graph constructor, public-only guard evaluation, local graph-step laws, public-store invariants, and mixed-feature transport tests. Prescribed-policy translation and local execution laws are checked. The concrete service terminates under arbitrary player and wire policies, including private initial setup. **No whole-run honest or strategic certificate yet.** |
| Transaction/block execution, cryptography, VM deployment | Further target edges | No active end-to-end refinement to these targets. Passive VM reference code does not establish one. |

The graph is an independently executable strategic IR. Its ordered nodes retain
typed expression code and observations; the native host consumes that graph,
not a source program or a source-image witness. Source composition belongs
above the backend theorem.

The native host admits competing and unopenable candidates, arbitrary tagged
payloads, pending delivery, retries/replay, rejection receipts, and withholding.
Binding accepts an opaque handle without running guards. Resolution validates
an authenticated opening using public deferred checks. Authenticated guard
rejection, withholding, or deadline resolution produces explicit failure;
malformed traffic alone cannot force another player's failure. Initial private
fields have generated verification material and strategic disclosure. Chance
uses the graph's public conditional kernel and advances atomically.

`VegasTests.GraphMessages` runs the full source fixture through this host:
an initial private Boolean, an optional-Boolean commitment, a deferred relation,
reverse disclosure, chance, and failure-sensitive settlement. These are
operational witnesses, not a substitute for the missing arbitrary-policy law.

`GraphRuntime.servicedGame` uses the shared policy runner with graph-indexed
owner opportunities, adaptive wire/reaction slots, reserved inclusion, and
phase-gated expiry. It accepts every native player policy and every supplied
wire policy. Its full-language compilation objectives are expressible in
`Paper.lean`. `Setup.pendingGame_complete` proves completion of every supported
play, and `Paper.source_pending_complete` delegates to it. The honest and
deviation laws are not yet proved. `MessageProgress.run_completed_of_ticks` proves the separate
operational fact that enough actual ticks force completion despite arbitrary
intervening native traffic; it does not protect honest messages from expiry.

## Restricted candidate certificate

The active `WFProgram` / `Vegas.EventGraph` candidate backend has a checked
source-to-pending strategic theorem. It does **not** implement `SourceProgram`'s
failure-aware source semantics and cannot supply the missing full-language edge.
Its capstones remain in
[SourcePublicCandidate.lean](../Vegas/Game/SourcePublicCandidate.lean):

- `candidate_public_source_support`: each supported stopped native outcome
  decodes to a legal public source outcome. This requires no service, but may
  change source opponents and is not a deviation law.
- `candidate_public_source_law`: generated profiles preserve the exact public
  source outcome law under timely service, without an incentive premise.
- `candidate_public_deviation_bound`: every randomized unilateral native
  deviation is bounded by a legal source deviation against unchanged opponents,
  under the source quitting condition.
- `candidate_public_approximate_nash_iff`: same-error epsilon-Nash equivalence
  at generated profiles. Reflection uses honest utility agreement, not the
  quitting premise.

These results compose independently proved source/graph and graph/native
certificates. `SealedCompilation` requires one common node type, no samples,
universally accepting commitment guards, and commitment-produced disclosures.
These are restrictions of this backend, not impossibility results for the full
language. They remain explicit in `Paper.lean`.

Its source condition `VegasCore.QuitPrefixDominanceAgainst` compares legal
quitting settlements to supported unilateral continuations sharing the public
prefix before the relevant commitment. This pointwise condition is stronger
than ex-ante quit dominance. Separate quitting caps and support floors give a
quantitative bound weighted by the deviator's actual timeout probability.

## Information, service, and proof boundary

The wire environment sees the pending pool, public state, and its history,
not private candidate meanings. Players see delivered inboxes, sent messages,
public ledger/receipts, and own command history. Pending messages may be
delivered before inclusion; the pool is not thereby common knowledge.

The restricted certificate uses a bounded round driver with adaptive wire
choices, roster coverage, periodic inclusion capacity, and a sufficient timeout
window. This is deadline-relative service, not censorship resistance. The
environment is fixed across unilateral comparisons. Builder/player coalitions
would require a different strategy space.

For the full typed host, the immediate goal is an exact deviation-mixture law
under canonical order and deadline-relative service. The remaining work is
whole-program observation projection, protection of unchanged players' messages
from expiry, and the joint observation/probability argument with unchanged
opponents. Service completion is proved. The generic shared-prior predrawing
theorem supplies one joint player/environment response mixture before the
initial execution is sampled; it preserves the complete native execution law
but does not construct a graph deviation. Hiding an
accepted handle and matching local result stores do not alone prove that law.
The [proof plan](typed-message-edge.md) records the failed-opening information
test and the causal replay obligation.

Utilities may interpret decoded source outcomes independently of payout code.
Arbitrary preferences over native traffic, time, costs, or receipts need a
separate utility contract. Source-outcome correspondence does not preserve them
automatically.

## Audit and ownership

`Paper.lean` selects directly delegated proved capstones and three explicitly
admitted full-language pending-message objectives. All have axiom pins; the
three objectives explicitly include `sorryAx`.
It is not a supporting-lemma inventory. Build roots check all active modules
and tests. The manuscript registry explicitly records unverified claims;
`--allow-unverified` checks mapping consistency, not draft parity.

Generic mathematics belongs in `GameTheory`/`GameTheoryExtensions`, message and
service semantics in `Interaction`, and source/graph compilation in `Vegas`.
Chain/VM-specific semantics belong at separate target boundaries. Archives are
passive references, neither imported nor counted as proof coverage.
