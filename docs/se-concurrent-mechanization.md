# Concurrent sequential-equilibrium preservation

## Deliverable

The exact target is [`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
This is a checked proposition, **not a proved preservation theorem**. It fixes the
concurrent graph, concrete phase runtime, reserved service law and economics
before quantifying over intended source sequential equilibria. The conclusion
preserves the joint law of original inputs, typed terminal state, public results
and the whole realized net payoff vector, with no exclusions or audit charges.
The initial law has arbitrary correlation and finite support; binding types
are finite. Auctions with unbounded binding bid/value choices are outside this
contract.
There is no fixed-calendar target.
The literal `.concurrent` mode allows distinct owners' private commitments to
overlap between source-ordered public barriers. Independent concurrent reveals
belong to the separate `.concurrentReveals` mode and are outside this contract.

The external hypotheses are well-formed finite source data, complete pending
observation, bounded resources, one unconditional exogenous reserved tape prior
sampled for the entire execution, bounded gaps and timely deadlines, sufficient fresh candidates, state-based utilities and a global
exclusion floor, and authentic funded audit coverage. These are sufficient
conditions, not a claim of minimality or a chain implementation guarantee.
Tape coordinates may correlate across owners and time, but the prior is not
refreshed or selected from a public prefix at block entry. Scheduler posterior
updates condition the same sampled tape; adaptive block priors are not covered.
No posterior identity, counterpart, source cursor, gain comparison or consistency
sequence is a capstone assumption.

## Current proof boundary

Contract, joint satisfiability and waiting payoff bound are checked. The complete
qualified weighted derivation has independent agent mathematical review under
the original hypotheses. Its global source image, supported replay, inverses
and chronological atom calculation remain unproved in Lean. The source-site,
foreign-posterior pair and stopped-payoff primitives, and mechanical-weight representative
independence, use only standard Lean axioms. Weighted transport remains admitted.
The clean commitment gain comparison
and final assembly are checked conditional on `QualifiedBindingLaw`; its
transport and unconditional SE remain
unproved. An unrestricted prefix density theorem is not claimed.
Checked dependencies do not close the remaining Lean obligations.

The four primitive interfaces and their complete aggregation compile with
`lake build +Vegas.Game.ConcurrentRawEquilibrium`. One named `sorry` body
remains; the unconditional theorem depends on an admitted proof axiom.
No new source or runtime assumptions are introduced by these interfaces.
The [likelihood derivation](se-concurrent-likelihood.md) gives the mathematical
constructions to implement; the [review](se-concurrent-likelihood-review.md)
records their scope and dependencies. This is agent mathematical review, not
Lean verification or human certification.

| Remaining proof | Guarantee | Reviewed argument |
| --- | --- | --- |
| `qualified_annotation_pushforward` | Exact native/source weights across every qualified mechanical and full source-word fiber | Likelihood analysis: inverse, source fibers and weights |

Progress within that remaining proof:

| Work | Checked material | Still open |
| --- | --- | --- |
| Source-phase correspondence | Initial assignment; fixed-snapshot table reads paired at the pre-request cut and read at the final completion; unified actual selected clean/dirty intervals with the same drained decoder word; paired rows including accepted failures, selected-prefix and saved/restore adapters, and typed reference transport using the stored successful bindings | Complete visit and restore induction assembling source alignment; publication and query coverage |
| Supported runtime replay | Quantitative whole-trace construction, prescribed reach, original tape support, admission and foreign-good qualification; normalized native-history PMF with exact supported point masses and readback, conditional on source alignment; supported environment outcomes identified by their public results under complete pending observation | Produce source alignment to instantiate this law from the original hypotheses |
| Recovery and coverage | Original positive summands have the common full source site, Good/depth and encoded completion support; literal entry and structural-word comparison; factual script extraction, supported left inverse and replay injectivity; one actual replay law covers every positive original annotation in the same native information and mechanical fiber, conditional on source alignment, and the qualified law retains this coverage; current and historical value readbacks, including permanent historical acceptance receipts and the correlated input tuple | Derive the forward annotation readback for every supported reconstructed script and instantiate complete augmented coverage from the global source producer |
| Exact weights | Literal native/tape and whole indexed callback class × alias products with unique emitted-packet indices; proper callbacks supply their actual query and D × mechanical × alias atom; chronological lost-draw × alias script mass consumed by the native-history point mass; whole correlated initializer and selected-history Nature mass equality, including original public sample atoms, consumed by the actual native/mechanical factorization; actual query-to-source-origin identification and issued-cylinder mass updates at the actual queried law; zero cases, per-history summation and normalization consumed by the original theorem | Identify historical/current/lost products with source factors, including the foreign-only issued-cylinder telescope, proving the per-history atom balance and pointwise weighted rectangle |

The mathematical review gate for weighted mechanization is satisfied. The
derivation explicitly covers the simultaneous source invariant, every positive
original annotated summand, both supported recovery directions and chronological
atom accounting. Implementation proceeds against those arguments; a newly found
mathematical gap stops the affected work for review.

These rows track implementation work inside the unchanged weighted statement;
they introduce no extra admitted theorem or preservation assumption. Local
lemmas do not close a row's complete obligation.

**Remaining implementation checkpoints.** Each item below closes only when its
complete result is Lean-checked with standard axioms. Draft bodies and local
helpers do not close it. These refine the work above without changing the
contract or the asynchronous checklist. Detailed mathematical derivations for
all items have independent agent review; that is not Lean verification.

Already checked: whole initializer/Nature mass and its likelihood consumer
(`61a5fe94`); universal reverse coverage by the same replay law, conditional on
source alignment (`bfe581fb`). The forward direction below remains separate.

| Checkpoint | Current state | Owner |
| --- | --- | --- |
| Complete selected-entry chronology through clean/retry/exhausted closes and automatic phases, including reveal/sample public agreement | Draft, unchecked; reveal/sample branch bodies authored | Source correspondence |
| Derive and retain actual visit/Attempt/same-snapshot relations, signed origins, address words and issued ledgers | Open | Source correspondence |
| Derive final publication handling, fixed focal view/action, actual binding queries and proper/lost classification | Open | Source correspondence |
| Prove every supported replay has the original fixed source entry/structural word and positive annotation | Open; reverse coverage does not prove this | Replay correspondence |
| Factor the whole qualified native likelihood into mechanical, queried proper-value and alias products | Checked: `sourceReplay_prescribed_response_atom`; ordinary Concurrent build and exact standard-axiom audit | Weights |
| Match historical accepted, current issued and historical never-accepted callbacks bijectively to their source rows/lost draws | Open | Weights |
| Prove the full foreign issued-prefix probability product and its separation from the focal prefix | One-coordinate update and foreign-only next-row kernel checked (`issuedLedger_foreign_owned_word_conditional`); native-query identification and full telescope open | Weights |
| Prove the positive per-history weight identity using the original pair-law mixture; remove the original weighted admission | Open; zero cases and final summation already checked | Weights |
| Verify the weighted theorem and concurrent capstone have only standard axioms, and pass the final build/checks | Pending; conditional assembly already checked | Integration |

The source chronology supplies the retained relations and final image clauses;
these feed forward annotation readback and the callback/source-row matching.
Native factorization, row matching and the issued-prefix product then feed the
per-history identity. Its checked summation and existing equilibrium assembly
lead to the final admission-free audit. Updates must identify the checked
theorem and build/axiom evidence; no item closes from a smaller helper alone.

`qualified_source_site` proves one supported source information site and faithful
value encoding. `foreign_posterior_cut_pair` proves the source cut/completion law
under both issued-ledger and focal-only conditioning. `annotated_stopped_payoff`
proves the complete qualified payoff numerator, including rejected branches, on
the original tape. `mechanicalCoefficient_eq_of_anchor` proves representative
independence of the mechanical weight on actual supported histories. All four
have standard-axiom audit guards.

`CleanUnsentBinding` packages the shared ready-binding conditions;
`foreignBindingFailureFootprint` names their exclusion test.
`QualifiedBindingSource` ties the source information, encoding and supported
anchor to actual native decision cuts. The weighted primitive takes that same
package and the concrete `ForeignPosteriorCutPair` law. Its conclusion includes
the entry-to-decision weight conversion and common positive finite factors.
The payoff primitive covers all native branches and annotation mass, including
the complement at none, rather than only positive annotation fibers.

`qualified_reconstruction` actually supplies the source package and pair theorem
to weighted transport. `qualified_binding_law` actually applies reconstruction
and payoff transport and normalizes their measures. Both composition bodies
contain no proof holes and compile against the primitive statements. The unconditional
`concurrentRawSequentialPreservation` then applies the existing conditional
preservation theorem to that law; its composition body contains no additional
hole. Each mathematical argument has agent scope review, not human certification;
the source-site, pair and payoff arguments also have checked Lean proofs.
Closing an obligation means replacing its whole
`sorry` body without weakening its statement, then checking its axiom dependencies.
The source checker maintains the one allowed declaration location and its
review reference. A new hole requires an explicit change to that registry.
The unconditional assembly has an axiom guard that exposes its remaining
admitted dependency; it is not evidence of proved preservation.
Passing `pairLaw` to a primitive records an intended proof dependency. While
that primitive contains `sorry`, Lean does not establish that the pair law
suffices to prove it or that its proof needs the pair law. Compilation checks
that the downstream aggregation follows from the four complete primitive
statements. The weighted primitive still requires a proof.

The [concurrent hypothesis test](../VegasTests/ConcurrentRawHypotheses.lean)
discharges every operational, payoff and audit assumption together, and supplies
a source SE witness. Its actual concurrent graph has two simultaneously ready
owned Boolean bindings; its service supports both activation orders, with
nonconstant utility and a positive funded deposit. This establishes that the
contract's premises are jointly satisfiable, not preservation.

The [likelihood analysis](se-concurrent-likelihood.md) proposes the qualified
ready-information reconstruction. The [independent review](se-concurrent-likelihood-review.md)
records the mathematical review and the finite diagnostic's limits. These
are independent agent reviews and a root-agent model audit, not human review
or Lean verification.
The [code inventory](se-concurrent-code-inventory.md) identifies owning APIs and
which proposed intermediate statements exceed what the final gain proof needs.
The [reserved-service proposal](se-reserved-service-preservation.md) supplies
motivation and assumptions; the likelihood analysis supplies the detailed argument.

At a clean binding decision, the proposed transport is the qualified
source measure: weighting actual native continuations by the clean binding gate
must give one scalar times the genuine source conditional law, uniformly over
legal proper typed insertions. The same construction must identify the actual
causal payoff continuation. This is a theorem to derive, never a premise to add.
Unqualified branches use their separate floor/reset comparison. A product law
against every full mechanical history is not required by this comparison.

The proposed derivation retains the actual initializer, source labels and
archives. Its required qualified inverse must cover every good source history
at the common full information, preserving canceled preparations and the joint prior.
Normalized typed-steering kernels retain updated focal queries through the
same-tape payoff attachment. The finite-n source past and zero-flag future are
separated before normalization, including zero qualification. The global inverse
and weight identities have reviewed mathematical derivations and still require
Lean proofs.
The proposed route constructs raw support first, then prefix refinement and exact query atoms;
conditional laws given a supplied cursor alone do not establish coverage or weights. The scoped qualified identity,
not an unrestricted prefix density, determines the mechanization boundary.

## Owning components

| Responsibility | Existing boundary |
| --- | --- |
| Intended and enriched source assessment | `IntendedPreservation`, `ProposalRecoveryEquilibriumConstruction` |
| Reserved service and resources | `ReservedEpochResources`, `ReservedEpochCompletion` |
| Original initialized laws and common sequence | `PhaseProposalInitializedTerminal`, `PhaseProposalInitializedLawError`, `PhaseProposalConsistentSequence` |
| Source reach factors and source information | `ProposalRecoveryPublicClassFactorization`, `ProposalRecoveryPublicClassConstancy`, `PhaseProposalNativeSourceInformation` |
| Actual local incentives | `PhaseProposalCurrentBindingGain`, `PhaseProposalPublicationGain`, `PhaseProposalCleanBindingGain`; clean binding is checked assuming `QualifiedBindingLaw` |
| Equilibrium limit and raw enforcement | `LocalSimulationLimit`, `PhaseOnePacketExtension` |

Detailed consumers and their actual hypothesis scopes are listed in the inventory.
Keep original initialization joint with outcomes and settlement; the convenient
raw readout wrapper alone drops a history coordinate needed by final assembly.

## Implementation discipline

Use ordinary in-tree modules and `lake build`. Do not maintain private compiler
provider registries, alternate runners or artifact-manifest verification systems.
Keep one proof representation for each justified interface. Merge focused
helper fragments into their owning mathematical component when doing so reduces
transport obligations. Remove unused constructions rather than retaining aliases.
Do not import old private proofs solely because they were checked in isolation.

Source language semantics, runtime transitions and the asynchronous checklist
obligations remain fixed. A change to external assumptions or target semantics
requires the owner's decision. Internal proof architecture may be simplified.
Use original correlated initializer atoms; retain canceled own failures, accepted
canceled foreign values, all proposals, exact addresses and actual raw aliases.
A factor one is not absence of a preparation lock. A physical failed receipt
is not automatically a particular source failure label.

`Paper.lean` remains a short paper-facing interface. Configure Lean options
centrally. Stable verified public checkpoints are committed and pushed; local
handoff notes and research archives are not committed.

## Completion gate

Derive the actual weighted inverse and retain preparation provenance in the
mechanization, with the frozen actual qualified-payoff type. Prove transport
and instantiate the checked clean gain comparison and final assembly to prove
the exact capstone. Keep its
external hypotheses fixed. If the mathematical argument appears incorrect,
stop implementation and report the precise issue.

Track the remaining obligations directly:

| Required result | Checked status |
| --- | --- |
| Actual native qualified payoff law | Source site, foreign posterior pair and aggregate stopped payoff are checked. The exact source/native weight identity has an independently agent-reviewed mathematical derivation and remains admitted in Lean. |
| Clean binding deviation bound | Full gain bound, including discarded-branch floor/reset comparison, checked assuming `QualifiedBindingLaw`. That transport premise remains open. |
| Full raw concurrent SE preservation | `concurrentRawSequentialPreservation_of_qualified_binding_law` checks joint-law, limit and raw-audit assembly assuming `QualifiedBindingLaw`. That transport premise remains open. |

The checked reductions are in the [qualified experiment](../Vegas/Game/PhaseProposalQualifiedBinding.lean),
[binding comparison](../Vegas/Game/PhaseProposalCleanBindingGain.lean) and
[conditional assembly](../Vegas/Game/ConcurrentRawEquilibrium.lean) components.
None proves the unconditional preservation contract.

`Vegas.phaseProposal_unflagged_wait_finish_le` proves the waiting comparison:
at an authentic clean unsent binding, literal WAIT followed by the ordinary
zero-flag policy has no larger expected finishing payoff than that policy
starting immediately. It uses an original supported reserved tape, the actual
runtime trace and the exclusion floor. It does not establish the comparison
for arbitrary SEND deviations or the source/native probability transport.

Partial lemmas and conditional composition do not close these rows. State the
actual unproved premises of partial results. Review the shared interfaces before
delegating implementation; add a helper only for an identified consumer. Keep
probability, incentive and final composition work in cohesive owning components,
with one root-controlled in-tree build. Do not count new code as progress.
Work toward whole component statements in parallel, then compile the complete
batch. Add no modules for this integration. Stop before exceeding an agreed
component budget and identify the concrete missing API or mathematical step.

Only the checked capstone closes concurrent preservation. Protect it before
broader assumption minimization or porting existing NE/nonconcurrent SE to the
shared phase runtime.
