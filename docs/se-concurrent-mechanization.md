# Concurrent sequential-equilibrium preservation

## Statement

The exact target is [`Vegas.ConcurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).
Its preservation theorem is
[`Vegas.concurrentRawSequentialPreservation`](../Vegas/Game/ConcurrentRawEquilibrium.lean),
pinned in Paper as `Vegas.Paper.concurrent_source_raw_sequential_equilibrium`
with only `propext`, `Classical.choice` and `Quot.sound`. The contract fixes the
concurrent graph, concrete phase runtime, reserved service law and economics
before quantifying over intended source sequential equilibria. The conclusion
preserves the joint law of original inputs, typed terminal state, public results
and the whole realized net payoff vector, with no exclusions or audit charges.
The initial law has arbitrary correlation and finite support; binding types are
finite. Auctions with unbounded binding bid/value choices are outside this
contract. The literal `.concurrent` mode allows distinct owners' private
commitments to overlap between source-ordered public barriers. Independent
concurrent reveals belong to the separate `.concurrentReveals` mode and are
outside this contract.

The external hypotheses are well-formed finite source data, complete pending
observation, bounded resources, one unconditional exogenous reserved tape prior
sampled for the entire execution, bounded gaps and timely deadlines, sufficient
fresh candidates, state-based utilities and a global exclusion floor, and
authentic funded audit coverage. These are sufficient conditions, not a claim of
minimality or a chain implementation guarantee. Tape coordinates may correlate
across owners and time, but the prior is not refreshed or selected from a public
prefix at block entry. Scheduler posterior updates condition the same sampled
tape; adaptive block priors are not covered. No posterior identity, counterpart,
source cursor, gain comparison or consistency sequence is a hypothesis. An
unrestricted prefix density theorem is not claimed.

The [concurrent hypothesis test](../VegasTests/ConcurrentRawHypotheses.lean)
discharges every operational, payoff and audit assumption together, and supplies
a source SE witness. Its concurrent graph has two simultaneously ready owned
Boolean bindings; its service supports both activation orders, with nonconstant
utility and a positive funded deposit. This shows that the premises are jointly
satisfiable; it does not apply the theorem to a game with strategic content.

## Proof structure

At a clean binding decision the proof needs the qualified source measure:
weighting actual native continuations by the clean binding gate gives one scalar
times the genuine source conditional law, uniformly over legal proper typed
insertions. The same construction identifies the actual causal payoff
continuation. Unqualified branches use a separate floor and reset comparison. A
product law against every full mechanical history is not required.

The [likelihood derivation](se-concurrent-likelihood.md) gives the mathematics;
the [review](se-concurrent-likelihood-review.md) explains its scope and the
finite diagnostic's limits. The Lean proof follows it in five parts.

1. **Source correspondence.** `sourceReplayCorrespondence` derives
   selected-entry agreement and literal completed visits from the original
   runtime inputs. `source_commit_row_closing_origin` and
   `sourceRawReplay_ordinary_completion` retain the actual physical close,
   signed origin, canonical interval and current issued ledgers.
   `sourceReplayAlignment` assembles publication handling, the focal view and
   action, actual binding queries and the proper or lost classification, and
   `sourceRawReplay_qualified` consumes it.
2. **Replay correspondence.** `sourceRawReplay_closed_key`,
   `sourceRawReplay_ordinary_completion` and `sourceRawReplay_forward_annotation`
   show that every supported replay has the original fixed source entry and
   structural word, with positive annotation.
3. **Weights.** `sourceReplay_prescribed_response_atom` factors the qualified
   native likelihood into mechanical, queried proper-value and alias products.
   `sourceRawReplay_foreign_draw_products` matches historical accepted, current
   issued and never-accepted callbacks to their source rows and lost draws.
   `sourceRawReplay_current_issued_mass` identifies the queried-draw product with
   the original foreign cylinder mass, and `sourceRawReplay_annotation_atom`
   separates the focal prefix with the original pair-law mixture, giving the
   per-history weight identity. `qualified_annotation_pushforward` sums it,
   zero cases included, into exact native and source weights across every
   qualified mechanical and full source-word fiber.
4. **Primitives.** `qualified_source_site` proves one supported source
   information site and faithful value encoding. `foreign_posterior_cut_pair`
   proves the source cut and completion law under both issued-ledger and
   focal-only conditioning. `annotated_stopped_payoff` proves the complete
   qualified payoff numerator, including rejected branches, on the original
   tape. `mechanicalCoefficient_eq_of_anchor` proves that the mechanical weight
   does not depend on the representative history.
5. **Assembly.** `qualified_reconstruction` supplies the source package and the
   pair theorem to the weighted transport. `qualified_binding_law` applies
   reconstruction and payoff transport and normalizes their measures, deriving
   `QualifiedBindingLaw`. `concurrentRawSequentialPreservation` applies the gain
   comparisons and equilibrium assembly to this law.

`CleanUnsentBinding` packages the shared ready-binding conditions, and
`foreignBindingFailureFootprint` names their exclusion test.
`QualifiedBindingSource` ties the source information, encoding and supported
anchor to actual native decision cuts. The weighted primitive takes that package
and the concrete `ForeignPosteriorCutPair` law; its conclusion includes the
entry-to-decision weight conversion and common positive finite factors. The
payoff primitive covers all native branches and annotation mass, including the
complement at none, rather than only positive annotation fibers.

The derivation retains the actual initializer, source labels and archives. Its
qualified inverse covers every good source history at the common full
information, preserving canceled preparations and the joint prior. Normalized
typed-steering kernels retain updated focal queries through the same-tape payoff
attachment. The finite past and the zero-flag future are separated before
normalization, including zero qualification. The construction establishes raw
support first, then prefix refinement and exact query atoms. Conditional laws
given a supplied cursor alone do not establish coverage or weights.

`Vegas.phaseProposal_unflagged_wait_finish_le` proves the waiting comparison: at
an authentic clean unsent binding, literal WAIT followed by the ordinary
zero-flag policy has no larger expected finishing payoff than that policy
starting immediately. It uses an original supported reserved tape, the actual
runtime trace and the exclusion floor. Other SEND deviations and probability
transport use their separate comparisons.

## Owning components

| Responsibility | Modules |
| --- | --- |
| Intended and enriched source assessment | `IntendedPreservation`, `ProposalRecoveryEquilibriumConstruction` |
| Reserved service and resources | `ReservedEpochResources`, `ReservedEpochCompletion` |
| Original initialized laws and common sequence | `PhaseProposalInitializedTerminal`, `PhaseProposalInitializedLawError`, `PhaseProposalConsistentSequence` |
| Source reach factors and source information | `ProposalRecoveryPublicClassFactorization`, `ProposalRecoveryPublicClassConstancy`, `PhaseProposalNativeSourceInformation` |
| Actual local incentives | `PhaseProposalCurrentBindingGain`, `PhaseProposalPublicationGain`, `PhaseProposalCleanBindingGain`; clean binding consumes the derived `QualifiedBindingLaw` |
| Qualified binding law | [`PhaseProposalQualifiedBinding`](../Vegas/Game/PhaseProposalQualifiedBinding.lean) |
| Equilibrium limit and raw enforcement | `LocalSimulationLimit`, `PhaseOnePacketExtension`, [assembly](../Vegas/Game/ConcurrentRawEquilibrium.lean) |

The [code inventory](se-concurrent-code-inventory.md) lists the consumers and
their hypothesis scopes. Keep original initialization joint with outcomes and
settlement: the convenient raw readout wrapper alone drops a history coordinate
that the final assembly needs. The
[reserved-service note](se-reserved-service-preservation.md) motivates the
assumptions.

The source semantics, runtime transitions, reserved tape law and external
hypotheses change only with the owner's decision; the internal proof
architecture may be simplified.
