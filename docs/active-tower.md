# Active compilation tower

This page records checked theorem scope. The [road ahead](a-road-ahead.md)
records the compiler goal; the [graph-to-message plan](typed-message-edge.md)
describes the implemented host and its strategic proof boundary.

## Full failure-aware language

| Boundary | Implementation | Checked result |
| --- | --- | --- |
| Source semantics | `Vegas.Source`: `SourceProgram` | Arbitrary binding and disclosure policies, own-action recall, heterogeneous results, initial secrets, deferred guards, and dependent chance. Every complete run resolves every obligation and satisfies every retained guard. |
| Source to typed graph | `Vegas.Game.GraphCompilation`, `Vegas.Game.GraphSetup` | Exact decoded terminal-state and payout laws; every unilateral graph deviation has one exact source-policy preimage against unchanged opponents. Finite private setup uses shared policies and a state-independent backtranslation. Nash and same-error epsilon-Nash equivalence at compiled profiles, without failure-dominance or finite-domain premises. |
| Typed graph to message host | `Vegas.Graph.MessageApplication`: `GraphRuntime` | Exact whole-run honest and arbitrary unilateral-deviation laws for the complete language, composed to the source with shared private initial setup. The concrete service terminates under arbitrary player and wire policies; compiled profiles satisfy same-error epsilon-Nash equivalence. |
| Transaction/block execution, cryptography, VM deployment | Further target edges | No active end-to-end refinement to these targets. Passive VM reference code does not establish one. |

The graph is an independently executable strategic IR. Its ordered nodes retain
typed expression code and observations; the native host consumes that graph,
not a source program or a source-image witness. Source composition belongs
above the backend theorem.

`Graph.BindingDiscipline` retains original payload identities across bind and
resolve; the source compiler proves it for every output, including shared
private setups. `MessageBindingProvenance` preserves the corresponding
field/handle invariant through arbitrary native policies. Successful
prescribed disclosures therefore have an exact accepted verifier. These
certificates require no additional law on the abstract expression types.
`MessageBindingSoundness` proves the converse needed for arbitrary senders:
every verified typed opening at an accepted address equals the immutable graph
cell. It holds from initial setup through arbitrary player and environment
policies, including failed, ill-typed, and repeated commitment preparations.
`MessageHistoryExtension` proves the compiler's whole-prefix own-action
projection laws. The deviation proof combines these facts with replay locality
and setup-wide probability coupling.

The shared runner proves authenticated sender-history provenance for all
retained messages. Reserved service inclusion uses it to identify the exact
protected envelope. `runPolicies_initial_preparationInvariant` proves that an
unchanged compiled player's preparation history exactly determines its
canonical candidate values, throughout arbitrary opponent and environment
behavior. Own commitments are canonical and have a prior preparation; this
prevents acceptance from freezing an unprepared slot of that player.
Within an unchanged graph phase, arbitrary native runs
preserve the typed values and accepted addresses; later commands also preserve
the history scan of earlier logical decisions. A proof-side residual law
accounts for choices sampled before their messages are included, and its
empty-cache case equals graph execution. `continuation_compiled_player_invoke`
proves the corresponding expectation equation for every graph constructor,
every preparation/submission stage, and any invoked player using its compiled
policy. Other player policies and the environment remain arbitrary. The
resulting continuation uses the actual extended own histories.
`MessageContinuationAt` packages this law at the actual native cursor, with
a proof that the state follows the compiled graph. It has no off-graph default
outcome. Its initial law is graph execution and its terminal law is the actual
ideal outcome. `continuationAt_initialized_wire` proves the expectation
equation for arbitrary adaptive wire invocations at every graph constructor,
deriving cache typing and packet provenance from initialized execution.
`MessageContinuationClock` proves the corresponding actual chance-tick and
waiting laws. `MessageHonestLaw` composes these invocation equations through
the full service schedule. The deviation continuation and replay-locality
modules separately cover an arbitrary focal policy without trusting its cache
markers.

`MessageBindingAcceptance` identifies any accepted current commitment of a
compiled owner with its canonical prepared handle and exact typed value,
including acceptance through the shared environment runner. The generic
`MessageApplicationSubmissionOrigin` reconstructs an actual supported
submission checkpoint for every pending message in an initially empty pool;
replay preserves the original sender and submission witness. These provenance
results connect accepted packets to actual policy execution, rather than to
an assumed well-formed message. Its history-entry origin theorem also recovers
the actual execution before and after a recorded command, including commands
whose packets are no longer pending.
`accepted_initial_compiled_resolve_packet` uses that reconstruction to prove
that an accepted disclosure in an actual initialized run installs exactly the
compiled owner's cached graph result. It covers successful opening, deliberate
withholding, and positive disclosure rejected by the guard precheck; other
players and the environment may use arbitrary policies.

For bindings, `runPolicies_bind_two_owner_calls_submitted` proves that the
service's two consecutive owner opportunities produce the canonical submission
from every preparation/submission state reachable under that compiled policy.
The proof uses actual command-history provenance: candidate agreement alone
would also admit fabricated histories containing the wrong message kind.
The analogous disclosure theorem covers every cache state and derives its
exact opening/withhold payload from the cached graph decision and binding
provenance. The bind and resolve service-block theorems start at an actually
reached current node, compose the two owner calls with reactions and reserved
inclusion, and prove strict progress beyond that node. They assume neither
prior submission nor pending packets, counters, or valid cache contents.
The real reaction block contains only wire and player instructions; the
whole-service proof must use that fact when excluding premature expiry.
`continuationAt_initialized_includeLatest` applies the wire law to the real
reserved service slot, retaining its complete plan and environment-history
cursor. `MessageServiceSafety` proves that every reached expiry slot either
waits at a completed phase or runs a chance node. Its graph induction retains
the complete environment policy and handles early advancement during reactions.
The runtime-general finite-run conservation theorem then composes the local
equations; completion identifies the final residual law with the actual outcome.

`servicePlan_unilateralDeviation_expirySafe` extends service protection to one
arbitrary native deviator: a reached expiry is stale, executes a chance node,
or belongs to that deviator. It cannot expire an unchanged player's live
decision. `MessageDeviationExtraction` identifies the first actual
phase-changing transition and proves that a bind or resolve transition has
the effect of a legal graph action. This extraction reads accepted immutable
values and verified packets, not the deviator's caches. Replay locality makes
the resulting action relation observation-local, and policy completion turns
it into the graph policy used by the proved deviation law.

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
operational regression witnesses rather than the proof of the arbitrary-policy
law.

`GraphRuntime.servicedGame` uses the shared policy runner with graph-indexed
owner opportunities, adaptive wire/reaction slots, reserved inclusion, and
phase-gated expiry. It accepts every native player policy and every supplied
wire policy. Its full-language compilation objectives are expressible in
`Paper.lean`. `Setup.pendingGame_complete` proves completion of every supported
play, and `Paper.source_pending_complete` delegates to it.
`Setup.pendingGame_honest_law` composes the graph-to-message honest law with
the source-to-graph law, and `Paper.source_pending_honest_law` delegates to it.
`Setup.pendingGame_deviation_law` gives one finite source-policy mixture for
each arbitrary native unilateral deviation. The mixture is selected before the
private initial state is sampled and preserves all opponents.
`Setup.pendingGame_approximate_nash_iff` combines this law with honest utility
equality to give same-error epsilon-Nash equivalence. In `MessageProgress`,
`run_completed_of_ticks` proves the separate
operational fact that enough actual ticks force completion despite arbitrary
intervening native traffic; it does not protect honest messages from expiry.

## Restricted candidate certificate

The active `WFProgram` / `Vegas.EventGraph` candidate backend has a checked
source-to-pending strategic theorem. It does **not** implement `SourceProgram`'s
failure-aware source semantics and does not itself supply the full-language edge.
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

For the full typed host, the exact deviation-mixture law is proved under
canonical order and deadline-relative service. Observation-local extraction,
whole-run coupling, service completion, and protection of unchanged players
from expiry are checked. The generic shared-prior predrawing theorem supplies
one joint player/environment response mixture before the initial execution is
sampled. The concrete
`exists_joint_service_response_mixture_runPolicies_setup` keeps reserved
inclusion and expiry live while predrawing only the focal player and adaptive
wire choices. It uses one response pair across the entire private initial law.
Hiding an
accepted handle and matching local result stores do not alone prove that law.
The [proof plan](typed-message-edge.md) records the failed-opening information
test and the causal replay obligation.

Utilities may interpret decoded source outcomes independently of payout code.
Arbitrary preferences over native traffic, time, costs, or receipts need a
separate utility contract. Source-outcome correspondence does not preserve them
automatically.

## Audit and ownership

`Paper.lean` selects directly delegated proved capstones, including the
full-language pending-message deviation and Nash laws. All have standard axiom
pins.
It is not a supporting-lemma inventory. Build roots check all active modules
and tests. The manuscript registry explicitly records unverified claims;
`--allow-unverified` checks mapping consistency, not draft parity.

Generic mathematics belongs in `GameTheory`/`GameTheoryExtensions`, message and
service semantics in `Interaction`, and source/graph compilation in `Vegas`.
Chain/VM-specific semantics belong at separate target boundaries. Archives are
passive references, neither imported nor counted as proof coverage.
