# Sequential-equilibrium proof interfaces

Use the [checklist](se-proof-checklist.md) for validation status, the
[completion plan](se-completion-plan.md) for dependency order, and the
[stack](se-compilation-stack.md) for theorem scope and backend assumptions.
The complete fixed-calendar decision-packet composition passes the strict
project build and capstone axiom pins. The checklist tracks checkpoint validation.
The general arbitrary-builder preservation theorem remains open.

## Semantic boundary

The runtime is compiled source execution with partial pending-message
observations. Readiness starts the event timer; only explicit clock commands
advance it. A selected source resolution FALSE emits authenticated
evidence-free withholding, TRUE emits an authentic effective opening, and
silence defers the choice. Expiry without a decision leaves a public miss.

The fixed calendar requires a packet at the final owner visit for every owned
event. The general retained menu allows waiting and expands to bounded raw
continuation at late unrecorded opportunities or persistent owner risk.
One collected deposit is sunk; later continuation must be rational under the
remaining payoff and information, rather than assumed compliant.

The backend observes authentic evidence partially and models conditional report
delivery. No certain watcher knowledge or independent collection coins are
assumed. Challenge-window coverage needs a concrete backend implementation.
Utilities for native repair depend on initial parameters and public outcomes;
future private values changed by repair are outside the claim.

## Interfaces to reuse

- [SourceServiceRuntime](../Vegas/Game/SourceServiceRuntime.lean) supplies the
  application and initialization; [SourceServiceReadout](../Vegas/Game/SourceServiceReadout.lean)
  supplies the typed terminal readout and base utility.
- [SourceServiceAlignedConstructors](../Vegas/Game/SourceServiceAlignedConstructors.lean)
  supplies aligned commitment and disclosure data. Calendar reachability lives
  separately in [SourceServiceBindingSource](../Vegas/Game/SourceServiceBindingSource.lean).
- [SourceServiceBayes](../Vegas/Game/SourceServiceBayes.lean),
  [SourceServiceAssessment](../Vegas/Game/SourceServiceAssessment.lean) and
  [SourceServiceOwnerComparison](../Vegas/Game/SourceServiceOwnerComparison.lean)
  transport native comparisons to the original source assessment. Preserve
  original private intentions; do not assume a normalized source equilibrium.
- [SourceServiceUnsentBinding](../Vegas/Game/SourceServiceUnsentBinding.lean) and
  [SourceServiceUnsentResolution](../Vegas/Game/SourceServiceUnsentResolution.lean)
  provide exact calendar owner comparisons. Earlier silence excludes passed
  timing indices for both event types; it does not select source FALSE.
- [SourceServiceRecordedPlan](../Vegas/Game/SourceServiceRecordedPlan.lean)
  identifies physical reserved-inclusion settlement of the original packet,
  separately from strategic continuation comparisons.
- [SourceServiceSiteBridge](../Vegas/Game/SourceServiceSiteBridge.lean) supplies
  completion-stopped readout bridges for arbitrary schedulers. Its initialized
  error bound does not by itself imply conditional incentives.
- [AsyncServiceCleanCompletionLaw](../Vegas/Game/AsyncServiceCleanCompletionLaw.lean)
  preserves actual clean-prefix probabilities under arbitrary completion away
  from source-compatible information. It neither constructs that completion nor
  controls escaped histories at the same native information value.
- [SourceServiceRecordedDecisionCompletion](../Vegas/Game/SourceServiceRecordedDecisionCompletion.lean)
  gives acceptance of the exact original recorded packet and no public miss
  under the asynchronous contract. [SourceServiceRecordedBindingCompletion](../Vegas/Game/SourceServiceRecordedBindingCompletion.lean)
  and [SourceServiceRecordedResolutionAlignment](../Vegas/Game/SourceServiceRecordedResolutionAlignment.lean)
  derive the exact typed source successor from the actual recalled choice.
  These are support and alignment laws, without a source-draw marginal or a
  native belief-transport premise.
- [SourceServiceProtectedDecisionLaw](../Vegas/Game/SourceServiceProtectedDecisionLaw.lean)
  derives the geometric response marginal at any actual protected unrecorded
  turn from full own recall, including earlier benign deferrals.
- [SourceServiceBindingResponseCompletion](../Vegas/Game/SourceServiceBindingResponseCompletion.lean)
  joins the actual transmitting draw to its typed successor and full stopped
  traffic. Waiting remains separate; prescribed foreign continuations are
  required for the probability factorization.
  [SourceServiceBindingPrefixCompletion](../Vegas/Game/SourceServiceBindingPrefixCompletion.lean)
  identifies the whole source step, including the actual unfinished decoder
  result on waiting.
- [SourceServiceReachedDecoding](../Vegas/Game/SourceServiceReachedDecoding.lean)
  derives source residuals with partial view recovery from their actual
  transport maps. [SourceServiceDecoderSlice](../Vegas/Game/SourceServiceDecoderSlice.lean)
  fixes a shared tail, lift and recovery from source syntax and rank, with
  decoder splitting for every store and history. Native Bayes transport
  still needs the actual source-prefix likelihood.
- [AsyncServiceCounterfactualBeliefs](../Vegas/Game/AsyncServiceCounterfactualBeliefs.lean)
  cancels the entire focal owner's recalled-action likelihood from native
  Bayes normalization. Relative escape still needs a bound against the actual
  opponent-and-nature denominator, including foreign waiting probabilities.
- [SourceServiceResolutionIntentionFactorization](../Vegas/Game/SourceServiceResolutionIntentionFactorization.lean)
  carries original and effective disclosure histories through the actual
  response traffic law. FALSE packets can represent failed TRUE intentions;
  source-relative beliefs must retain that distinction.
- [SourceServiceResolutionMemoryFactorization](../Vegas/Game/SourceServiceResolutionMemoryFactorization.lean)
  restores the current owner's original memory using the actual source
  normalizer and joins waiting and transmission to full traffic. Its native
  traffic marginal is the real protected policy; whole-source prefix and
  belief assembly remain separate.
- [SourceServiceResolutionMemoryCompletion](../Vegas/Game/SourceServiceResolutionMemoryCompletion.lean)
  carries that same response joint law through actual stopped execution.
  The native marginal uses the same stopping kernel; transmission retains
  effective and current-owner intended successors, while waiting stays at
  its post-response boundary. Other owners' original histories and source
  assessment transport remain separate.
- [DisclosureProfilePrefix](../Vegas/Game/DisclosureProfilePrefix.lean)
  composes all owners' actual memory kernels and recovers the complete
  original source law at every finite normalized source prefix, including
  correlated initial parameters. The effective-source conditional-prefix
  bridge to native information remains separate.
- [DisclosureProfileRetraction](../Vegas/Game/DisclosureProfileRetraction.lean)
  proves supported original memories compress back to the same effective
  source prefix. Its view law carries an effective source-view channel
  through the restoration without assuming a posterior equation. Actual
  native traffic still needs to be identified with that channel.
- [SourceServiceRiskExtension](../Vegas/Game/SourceServiceRiskExtension.lean)
  extends an audited risk-menu equilibrium after classified packet coverage
  and other-exclusion comparisons are supplied. It does not embed a source
  equilibrium into that auxiliary game.
- [SourceServiceAliasEquilibrium](../Vegas/Game/SourceServiceAliasEquilibrium.lean)
  supplies the final private raw-alias transport, retaining correlated
  collection and prior charges.

## Proof and build discipline

Read `AGENTS.md` and inspect the actual Git state before editing. Generic
mathematics belongs in `GameTheoryExtensions`, generic execution in
`Interaction`, pending semantics in `Vegas/Pending`, and source/compiler proofs
in `Vegas/Game`. Lean options belong in `lakefile.toml`. Keep the pinned
GameTheory submodule unchanged.

One coordinator writes build artifacts. Other checks may run read-only with
an existing module setup JSON and no artifact-output flags. A missing imported
artifact during its replacement is not a source failure. Bare
`lake env lean file.lean` omits central options. Verify the full coherent
checkpoint and capstone dependency evidence before marking strategic checklist
items complete. Commit and push stable verified snapshots; no admissions,
assumed posterior equations or unproved runtime-comparison bundles discharge
the public theorem.
