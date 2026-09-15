# Active compilation tower

This page records checked theorem scope. The [road ahead](a-road-ahead.md)
records the broader compiler goal and milestone acceptance tests; the
[typed protocol interface](typed-protocol-interface.md) describes the broader
operational model and the source-resolution implementation boundary.

The [deferred-guard mathematical specification](deferred-guards-semantics.tex)
has a checked publication component in `Interaction.GuardedPublication` and
immutable bindings in `Interaction.BoundPublication`. Its consistency and
honest-feasibility theorems are source-design results, not another compiled
tower edge.

Publication-result expressions are also checked: `Result A` distinguishes
failure from successful ordinary values, including `Option.none`, and has
total explicit eliminators. `Vegas.Source` supplies the complete failure-aware
source game and proves terminal resolution and guard satisfaction under
arbitrary source policies. The compiler below still consumes `Vegas.Core`;
its strategic results do not apply to `SourceProgram`. The
[source rationale](source-design-rationale.md) records the semantic choices,
and [the graph-edge design](source-graph-edge.md) specifies the next migration.

## Layers and results

| Layer | Main interface | Checked result and boundary |
| --- | --- | --- |
| Generic strategic transport | `GameTheoryExtensions`: `MixtureSimulationOn`, `UtilitySimulation` | Exact mixture and utility-specific deviation bounds compose. Honest agreement and unilateral bounds imply same-error epsilon-Nash equivalence at compiled profiles. These are generic rules, not compiler instances by themselves. |
| Failure-aware source | `Vegas.Source`: `SourceProgram`, `gameForm` | All four constructors, arbitrary binding/disclosure policies, own-action recall, heterogeneous results, initial secrets, deferred guards, and dependent chance. Complete runs resolve all resources and satisfy all guards. No compiler edge yet. |
| Checked sequential source | `Vegas.Core`: `WFProgram`, `sourceGameForm` | Written-order typed execution with guarded owner choices, public dependent samples, disclosures, and terminal environments. Utilities can interpret outcomes rather than identify payouts with utility. |
| Source to graph | `Vegas.Game.SourceGraph`: `WFProgram.sourceGraphSimulation` | Exact honest terminal-environment law and arbitrary unilateral declared-read graph-deviation backtranslation with unchanged opponents, for all checked core programs and finite player sets. Source/graph Nash and same-error epsilon-Nash equivalence. |
| Graph to sealed application | `Vegas.Compile`: `SealedShape`, `SealedFragment` | Concrete rules and strategy translation use the shared runner. `SealedShape` permits guards in code; the strategic certificate `SealedFragment` assumes they always accept. Both require one common node type, no samples, and commitment-produced disclosures. |
| Public pending-message host | `Interaction`: `MessageApplication`, `SealedResolution.candidateApplication` | Competing candidates, immutable accepted meaning, accepted-but-unopenable handles, delivery, inclusion, retries/replay, rejection, clock, and continuing default resolution. Arbitrary-policy invariants and finite completion are proved. |
| Graph to candidate game | `SealedFragment.CandidateRoundModel` | Independent graph-relative honest law and randomized unilateral utility bounds. The backend constructs its coupling and timeout attribution; it does not assume the desired deviation simulation. |
| Source to candidate game | `Vegas.Game.SourcePublicCandidate` | Composition gives the public source outcome law, a source-deviation utility bound, and same-error epsilon-Nash equivalence under the source quitting and service conditions below. |
| Typed ordered protocol | `Vegas.Protocol`, `Interaction.OrderedProtocol` | Retains heterogeneous graph operations, guard code, initial inputs, and conditional chance in the shared message application. Local operational laws only; no general source settlement, honest-law, or arbitrary-deviation certificate. |
| Transaction/block execution, concrete cryptography, VM deployment | Further target edges | No active end-to-end refinement to these targets. Reference VM code outside build roots does not establish one. |

The graph's behavioral-frontier presentation has additional exact strategic
results under information locality and readiness hypotheses. It is a game
presentation of the graph, not a second executable backend or a replacement
for the source-to-pending theorem.

## End-to-end candidate theorem

The principal source-relative declarations are in
[SourcePublicCandidate.lean](../Vegas/Game/SourcePublicCandidate.lean):

- `candidate_public_source_support`: every supported stopped native outcome
  decodes to a legal public source outcome. No service assumption is needed;
  this witness may change source opponents and is not deviation simulation.
- `candidate_public_source_law`: generated profiles preserve the exact law of
  the public terminal source environment under timely service. No incentive
  assumption is needed.
- `candidate_public_deviation_bound`: every observation-local randomized native
  unilateral deviation is bounded in expected utility by one legal source
  deviation against unchanged opponents, under the source quitting condition.
- `candidate_public_approximate_nash_iff`: same-error epsilon-Nash equivalence
  at the generated profile. Set epsilon to zero for Nash. Reflection needs
  honest utility agreement but no quitting incentive condition.

These results compose the source/graph certificate with graph-relative native
laws. The outcome interpretation may be any player-specific utility of the
public terminal source environment. Payout valuation is a special case.
Selective quitting generally prevents an exact deviation outcome-law theorem.
Separate source quitting caps and support floors give a quantitative utility
bound with their gap multiplied by the deviator's actual timeout probability.

The theorem's `SealedCompilation` certificate currently requires homogeneous,
sample-free graphs, universally accepting commitment guards, and reveals whose
values originate in source commitments. These are implementation restrictions,
not established impossibility conditions for the intended compiler.

## Information, service, and incentives

The wire policy sees the full pending pool and its declared history, but not
the private candidate table. Players see their delivered inbox, sent messages,
public ledger/receipts, and local command history. Delivery and inclusion are
distinct: a player may react to an opening while it is still pending. The
compiler checks the disclosure barrier before honest submission.

The strategic theorem uses the bounded round driver: player invocations,
wire-service invocations, then a clock tick. The wire choices are adaptive.
Roster coverage, periodic inclusion capacity, and a sufficient timeout window
protect unchanged players. This is an explicit deadline-relative service
contract, not a proof of censorship resistance or a theorem about every fair
network model. The wire environment is fixed when a player's unilateral
deviations are compared; builder/player coalitions are a different game.

`VegasCore.QuitPrefixDominanceAgainst` is entirely source-defined. It compares
legal quitting settlements to supported unilateral source continuations with
the same public environment before the relevant commitment. It is pointwise
and stronger than ordinary ex-ante quit dominance. The native proof derives
the required timeout utility comparison from it. More permissive conditional
source criteria remain a further result.

Malformed traffic is retryable rejection, not immediately a source quit.
Authoritative deadline resolution implements the designated source alternative
and continues. An outsider cannot force another player's resolution merely by
submitting garbage. Completion by default alone does not prove service or
strategic preservation.

## Language coverage and immediate work

| Feature | Operational/compiler support | Arbitrary-deviation/Nash coverage |
| --- | --- | --- |
| Competing candidates, failed openings, pending observations, retries, deadlines | Candidate host and compiler laws checked | Checked for the admitted fragment and service contract |
| Rejecting public guards | Source guard agreement, opening validation, candidate persistence/hiding, and legal completed settlement checked | Not yet included in the end-to-end strategic theorem |
| Heterogeneous node types | Checked source/graph support | Not supported by the sealed strategic backend |
| Dependent chance | Checked source/graph conditional kernels | Sealed lowering disables samples; no native chance theorem |
| Initial-field disclosure | Checked source/graph semantics | Requires setup and subsequent availability for deterministic disclosure; not supported by this backend. Setup refusal is pre-play, not an invented source quit. |
| Private guard evaluation | Legal source semantics | Needs an implemented public or private-verification capability; a proof-facing secret is insufficient |

The typed adapter represents these source features without disabling an
operation. This does not extend the candidate theorem's language coverage.
Its source failure interpretation is still unresolved: current source commits
are guard-valid and reveals deterministic, while the intended target admits
invalid candidates and maps failed publication to programmed quitting.
Local default insertion alone does not prove that correspondence.

The next acceptance test combines these source features in one real compiled
program and obtains the source-to-pending theorem through the same typed
protocol. The baseline uses canonical operation order, with arbitrary off-order
traffic still expressible. Operational representation does not yet establish
that strategic theorem or supersede the restricted backend.

## Audit and ownership

`Paper.lean` selects paper-visible theorems, directly delegated to their owning
modules. It is not a supporting-lemma inventory. Its axiom pins audit transitive
proof dependencies; build roots still compile the other active modules/tests.

The separate manuscript has broader and partly different claims. Its registry
records coverage gaps; `--allow-unverified` checks mapping consistency, not draft
parity. Full manuscript verification, executable EVM deployment, computational
security, and arbitrary trace-utility preservation do not follow from this build.

Generic mathematics belongs in `GameTheory`/`GameTheoryExtensions`, generic
interaction semantics in `Interaction`, source/graph compilation in `Vegas`,
and chain/VM-specific code at separate target boundaries. Archives are passive
references and are neither imported nor counted as proof coverage.
