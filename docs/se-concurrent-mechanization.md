# Concurrent sequential-equilibrium preservation

## Deliverable

The exact target is [`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
Its preservation theorem is
[`Vegas.concurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawEquilibrium.lean).
The original theorem is Lean-checked using only `propext`, `Classical.choice`
and `Quot.sound`. The contract fixes the concurrent graph, concrete phase
runtime, reserved service law and economics before quantifying over intended
source sequential equilibria. The conclusion
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
sampled for the entire execution, bounded gaps and timely deadlines, sufficient
fresh candidates, state-based utilities and a global exclusion floor, and
authentic funded audit coverage. These are sufficient
conditions, not a claim of minimality or a chain implementation guarantee.
Tape coordinates may correlate across owners and time, but the prior is not
refreshed or selected from a public prefix at block entry. Scheduler posterior
updates condition the same sampled tape; adaptive block priors are not covered.
No posterior identity, counterpart, source cursor, gain comparison or consistency
sequence is a capstone assumption.

## Current proof boundary

The original weighted transport, reconstruction and concurrent preservation
capstone are Lean-checked. The exact axiom audit of
`qualified_annotation_pushforward`, `qualified_reconstruction`,
`qualified_binding_law` and `Vegas.concurrentRawSequentialPreservation` reports
only `propext`, `Classical.choice` and `Quot.sound`. The ordinary build of
`Vegas.Game.ConcurrentRawEquilibrium` passes. No admitted weighted proof or
source-alignment hypothesis remains.

The source-image construction, physical-close origins, supported replay, both
coverage directions, forward annotation positivity, chronological callback
products and original per-history weight identity are proved from the original
runtime inputs. The query relation has the required foreign-owner scope;
no all-owner historical query identity is used. The source-site, foreign
posterior pair and stopped-payoff primitives and the clean gain comparison feed
the proved `QualifiedBindingLaw` and the original capstone. An unrestricted
prefix density theorem is not claimed.

All nine implementation checkpoints are checked. The temporary heartbeat
increase is removed. The full ordinary build and repository checks pass at the
original proof budget, without adding a hypothesis or changing the theorem's
scope.

The [likelihood derivation](se-concurrent-likelihood.md) describes the proved
construction; the [review](se-concurrent-likelihood-review.md) explains its
mathematical scope and the finite diagnostic's limits.

| Checked weighted statement | Guarantee | Owning proof |
| --- | --- | --- |
| `qualified_annotation_pushforward` | Exact native/source weights across every qualified mechanical and full source-word fiber | `sourceRawReplay_annotation_atom` and the normalized replay balance |

Progress within the weighted proof:

| Work | Checked material | Status |
| --- | --- | --- |
| Source-phase correspondence | Initial assignment; fixed-snapshot table reads paired at the pre-request cut and read at the final completion; unified actual selected clean/dirty intervals with the same drained decoder word; paired rows including accepted failures, selected-prefix and saved/restore adapters, and typed reference transport using the stored successful bindings; original-data selected-entry and completed-visit correspondence through all phase branches; complete publication, focal, foreign-query and proper/lost alignment fields; actual physical-close signed origins and source address/issued-ledger relations | Complete |
| Supported runtime replay | Quantitative whole-trace construction, prescribed reach, original tape support, admission and foreign-good qualification; normalized native-history PMF with exact supported point masses and readback from the original runtime data; supported environment outcomes identified by their public results under complete pending observation | Complete; consumed by `sourceRawReplay_qualified` without an alignment hypothesis |
| Recovery and coverage | Original positive summands have the common full source site, Good/depth and encoded completion support; literal entry and structural-word comparison; factual script extraction, supported left inverse and replay injectivity; one actual replay law covers every positive original annotation in the same native information and mechanical fiber, and the original-data qualified law retains this coverage; current and historical value readbacks, including permanent historical acceptance receipts and the correlated input tuple; every supported reconstructed script has the original fixed entry and structural word with positive original annotation | Complete |
| Exact weights | Literal native/tape and whole indexed callback class × alias products with unique emitted-packet indices; proper callbacks supply their actual query and D × mechanical × alias atom; chronological lost-draw × alias script mass consumed by the native-history point mass; whole correlated initializer and selected-history Nature mass equality, including original public sample atoms, consumed by the actual native/mechanical factorization; actual query-to-source-origin identification and issued-cylinder mass updates at the actual queried law; zero cases, per-history summation and normalization consumed by the original theorem | Complete: `sourceRawReplay_foreign_draw_products`, `sourceRawReplay_current_issued_mass` and `sourceRawReplay_annotation_atom` prove the original per-history balance and weighted rectangle |

The complete source producer is consumed by the qualified replay law from the
original runtime data. The same replay law supplies forward annotation readback,
reverse coverage and exact weights, retaining the same selected histories,
physical drains, signed occurrences, source entry and tape.

These checkpoints refine implementation work inside the unchanged weighted
statement and preservation contract. Each checked item denotes its complete
result and exact standard-axiom audit; local helpers alone do not close an item.

| Checkpoint | Current state | Owner |
| --- | --- | --- |
| Complete selected-entry chronology through clean/retry/exhausted closes and automatic phases, including reveal/sample public agreement | Checked: `sourceReplayCorrespondence` derives selected-entry agreement and literal completed visits from the original runtime inputs; owning build and standard-axiom audit passed | Source correspondence |
| Derive and retain actual visit/Attempt/same-snapshot relations, signed origins, address words and issued ledgers | Checked: `source_commit_row_closing_origin` and `sourceRawReplay_ordinary_completion` retain the actual physical close, signed origin, canonical interval and current issued ledgers; owning build and exact standard-axiom audit passed | Source correspondence |
| Derive final publication handling, fixed focal view/action, actual binding queries and proper/lost classification | Checked: `sourceReplayAlignment` assembles all fields; `sourceRawReplay_qualified` constructs and consumes it from the original runtime inputs, with ordinary build and standard-axiom audit | Source correspondence |
| Prove every supported replay has the original fixed source entry/structural word and positive annotation | Checked: `sourceRawReplay_closed_key`, `sourceRawReplay_ordinary_completion` and `sourceRawReplay_forward_annotation` use the same fixed entry and supported script; ordinary owning builds and exact standard-axiom audits passed | Replay correspondence |
| Factor the whole qualified native likelihood into mechanical, queried proper-value and alias products | Checked: `sourceReplay_prescribed_response_atom`; ordinary Concurrent build and exact standard-axiom audit | Weights |
| Match historical accepted, current issued and historical never-accepted callbacks bijectively to their source rows/lost draws | Checked: `sourceRawReplay_foreign_draw_products` identifies the actual historical/current/lost and alias products; ordinary owning build and exact standard-axiom audit passed | Weights |
| Prove the full foreign issued-prefix probability product and its separation from the focal prefix | Checked: `sourceRawReplay_current_issued_mass` identifies the actual queried-draw product with the original foreign cylinder mass; `sourceRawReplay_annotation_atom` separates the focal prefix using the original pair-law mixture; ordinary owning build and exact standard-axiom audit passed | Weights |
| Prove the positive per-history weight identity using the original pair-law mixture; remove the original weighted admission | Checked: `sourceRawReplay_annotation_atom` supplies the original per-history identity; `qualified_annotation_pushforward` consumes it with zero cases and full summation; owning build and exact standard-axiom audit passed | Weights |
| Verify the weighted theorem and concurrent capstone have only standard axioms, and pass the final build/checks | Checked: original weighted theorem and capstone have only standard axioms; the full ordinary build at the original proof budget and source-policy, module-boundary, documentation and SE-evidence checks passed | Integration |

The source chronology supplies the retained relations and final image clauses;
these feed forward annotation readback and the callback/source-row matching.
Native factorization, row matching and the issued-prefix product then feed the
per-history identity. Its checked summation and equilibrium assembly establish
the original capstone with only standard axioms. Updates must identify the checked
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

`qualified_reconstruction` supplies the source package and original pair theorem
to the proved weighted transport. `qualified_binding_law` applies reconstruction
and payoff transport and normalizes their measures.
`concurrentRawSequentialPreservation` then applies the gain and equilibrium
assembly to this derived law. All three complete proofs and the original
weighted theorem pass the standard-axiom audit. The full pair-law mixture,
including zero fibers and unqualified branches, remains in the proof.

The [concurrent hypothesis test](../VegasTests/ConcurrentRawHypotheses.lean)
discharges every operational, payoff and audit assumption together, and supplies
a source SE witness. Its actual concurrent graph has two simultaneously ready
owned Boolean bindings; its service supports both activation orders, with
nonconstant utility and a positive funded deposit. This establishes that the
contract's premises are jointly satisfiable, not preservation.

The [likelihood analysis](se-concurrent-likelihood.md) describes the qualified
ready-information reconstruction. The [independent review](se-concurrent-likelihood-review.md)
records the mathematical scope and the finite diagnostic's limits. The checked
Lean theorems, rather than the diagnostic or mathematical review, establish
preservation.
The [code inventory](se-concurrent-code-inventory.md) identifies owning APIs and
which proposed intermediate statements exceed what the final gain proof needs.
The [reserved-service proposal](se-reserved-service-preservation.md) supplies
motivation and assumptions; the likelihood analysis supplies the detailed argument.

At a clean binding decision, the proved transport is the qualified
source measure: weighting actual native continuations by the clean binding gate
gives one scalar times the genuine source conditional law, uniformly over
legal proper typed insertions. The same construction identifies the actual
causal payoff continuation. Both conclusions are derived internally.
Unqualified branches use their separate floor/reset comparison. A product law
against every full mechanical history is not required by this comparison.

The derivation retains the actual initializer, source labels and
archives. Its qualified inverse covers every good source history
at the common full information, preserving canceled preparations and the joint prior.
Normalized typed-steering kernels retain updated focal queries through the
same-tape payoff attachment. The finite-n source past and zero-flag future are
separated before normalization, including zero qualification. The global inverse
and weight identities have checked Lean proofs. The construction establishes raw
support first, then prefix refinement and exact query atoms. Conditional laws
given a supplied cursor alone do not establish coverage or weights. The scoped
qualified identity determines the mechanization boundary.

## Owning components

| Responsibility | Existing boundary |
| --- | --- |
| Intended and enriched source assessment | `IntendedPreservation`, `ProposalRecoveryEquilibriumConstruction` |
| Reserved service and resources | `ReservedEpochResources`, `ReservedEpochCompletion` |
| Original initialized laws and common sequence | `PhaseProposalInitializedTerminal`, `PhaseProposalInitializedLawError`, `PhaseProposalConsistentSequence` |
| Source reach factors and source information | `ProposalRecoveryPublicClassFactorization`, `ProposalRecoveryPublicClassConstancy`, `PhaseProposalNativeSourceInformation` |
| Actual local incentives | `PhaseProposalCurrentBindingGain`, `PhaseProposalPublicationGain`, `PhaseProposalCleanBindingGain`; clean binding consumes the derived `QualifiedBindingLaw` |
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

The original weighted transport and concurrent capstone are proved with the
external hypotheses fixed. The exact standard-axiom audit passes for the
original weighted, reconstruction, payoff-law and preservation roots.

| Required result | Checked status |
| --- | --- |
| Actual native qualified payoff law | Source site, foreign posterior pair, original weighted rectangle and aggregate stopped payoff are checked; `qualified_binding_law` derives the complete law. |
| Clean binding deviation bound | Full gain bound, including discarded-branch floor/reset comparison, is checked and instantiated with the derived qualified law. |
| Full raw concurrent SE preservation | `Vegas.concurrentRawSequentialPreservation` proves the original contract using only standard axioms. |
| Final acceptance | Checked: the temporary heartbeat increase is removed; the full ordinary build at the original proof budget, exact standard-axiom audit and repository checks passed. |

The [qualified experiment](../Vegas/Game/PhaseProposalQualifiedBinding.lean),
[binding comparison](../Vegas/Game/PhaseProposalCleanBindingGain.lean) and
[preservation assembly](../Vegas/Game/ConcurrentRawEquilibrium.lean) retain the
original source inputs, full pair-law mixture and economics.

`Vegas.phaseProposal_unflagged_wait_finish_le` proves the waiting comparison:
at an authentic clean unsent binding, literal WAIT followed by the ordinary
zero-flag policy has no larger expected finishing payoff than that policy
starting immediately. It uses an original supported reserved tape, the actual
runtime trace and the exclusion floor. Other SEND deviations and probability
transport use their separate checked comparisons.

The final checkpoint closes only after its complete gates pass. Protect the
checked capstone before broader assumption minimization or porting existing
NE/nonconcurrent SE to the shared phase runtime. No acceptance step changes the
source semantics, reserved tape law or external preservation hypotheses.
