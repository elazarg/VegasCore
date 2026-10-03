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
- [AsyncServicePrescribedCompletion](../Vegas/Game/AsyncServicePrescribedCompletion.lean)
  constructs a consistent assessment for each fixed admitted effective source
  profile, with immediate decisions at source-compatible sites and optimal
  continuation at every free site under the actual audited utility. Its complete
  initialized history law and joint typed readout/realized settlement law equal
  first-turn play. Prescribed-site rationality remains open; the varying-source
  construction below handles actual approximants without assuming off-path
  normalization continuity.
- [AsyncServiceInitializedDomination](../Vegas/Game/AsyncServiceInitializedDomination.lean)
  bounds the whole initialized history law of uniformly perturbed geometric
  pins with arbitrary free continuation. Every first-turn history retains
  at least `((1 - δ)(1 - ε))^(card Player * fuel)` of its mass, so total variation
  loss vanishes uniformly over source profiles and free play. This supports
  varying original source approximants without off-path normalization continuity.
  Conditional rare-input beliefs and incentive-compatible waiting rates remain
  separate obligations.
- [AsyncServiceCompatibleWait](../Vegas/Game/AsyncServiceCompatibleWait.lean)
  derives exact WAIT likelihood at actual compatible inputs. The native pin
  has mass `δ * uniformWait + (1 - δ) * w(who, info)`. Real bounded traces rule
  out a truncated last turn.
  Foreign WAIT likelihoods still enter another player's posterior.
- [AsyncServiceInformationWait](../Vegas/Game/AsyncServiceInformationWait.lean)
  constructs native pins whose WAIT rates depend on complete actual information.
  [AsyncServiceInformationWaitDomination](../Vegas/Game/AsyncServiceInformationWaitDomination.lean)
  derives initialized loss from a common upper bound at compatible sites using
  the shared finite induction. No incentive-compatible rate selection is proved.
- [SourceServiceClearAudit](../Vegas/Game/SourceServiceClearAudit.lean)
  derives no owner miss and zero current audit charge from focal persistent
  clarity at a real risk-menu prefix. Own recall, public state and receipts
  transfer the verdict to every initialized RAW history at compatible
  information. Its fiber consumer covers any actual response menu, including
  the full effective game, without original risk support or restrictions on
  foreign deviations. Only sample authenticity is needed; future charges and
  unfinished verdicts may change.
- [AsyncServiceCompatibleRecall](../Vegas/Game/AsyncServiceCompatibleRecall.lean)
  derives compatibility of every earlier own recalled decision and equality of
  the complete focal likelihood for profiles agreeing on compatible inputs.
  Own WAITs cancel by the existing counterfactual Bayes law even when rare;
  foreign WAIT likelihoods and conditional escape remain separate obligations.
- [AsyncServiceOriginalCompletion](../Vegas/Game/AsyncServiceOriginalCompletion.lean)
  constructs a fully mixed native Bayes sequence from actual original source
  approximants, with one common strategy/belief subsequence and consistent limit.
  Free sites are rational; initialized support is source-compatible; the full
  typed outcome and realized sampled settlement law equal the original source
  strategy's law. Local WAIT rates have a common vanishing upper bound at
  compatible sites. Actual normalized pin limits are retained. Source-relative
  conditional beliefs, prescribed-site rationality and suitable waiting rates
  remain open. Prescribed uniform trembles and free-agent reference trembles
  have independent vanishing rates; initialized loss uses only the prescribed rate.
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
- [SourceServiceFirstActivation](../Vegas/Game/SourceServiceFirstActivation.lean)
  reaches the first ready owner input from an untouched completion boundary
  within the contract horizon. The configuration is unchanged and the turn
  has protected inclusion. Actual recall recovers its before-response input;
  integrating the response lottery preserves that same passive sample.
- [SourceServiceFirstActivationFactorization](../Vegas/Game/SourceServiceFirstActivationFactorization.lean)
  carries a prior source-view/full-traffic factorization through the whole
  binding or resolution wait to the actual first owner input, with total mass
  on real inputs at every supported prior view. The source carrier may retain
  original and effective states together. It preserves the given carrier
  marginal. The initialized rank law supplies the source marginal separately;
  the actual pure-first-turn source/traffic induction is assembled below.
- [SourceServiceFirstTurnCompletes](../Vegas/Game/SourceServiceFirstTurnCompletes.lean)
  identifies the actual next-prefix decoder law of the local first-turn
  completion phase with the whole source behavioral step. This includes
  samples, commitments and explicit withholding, before applying a source
  continuation. It does not transport original disclosure intentions.
- [SourceServiceFirstTurnPrefix](../Vegas/Game/SourceServiceFirstTurnPrefix.lean)
  derives that local law for the actual global first-turn policy.
  [SourceServiceFirstTurnRanks](../Vegas/Game/SourceServiceFirstTurnRanks.lean)
  composes actual rank stops and identifies the initialized effective source
  prefix at every rank, jointly with any reading of the same initial draw.
  The ordered stopping identity in
  [ReactiveStopping](../Interaction/ReactiveStopping.lean) supplies the actual
  evaluator composition; no source marginal is assumed.
- [SourceServiceFirstTurnInformation](../Vegas/Game/SourceServiceFirstTurnInformation.lean)
  proves equal current physical observations at two actual first-turn rank
  endpoints determine equal whole effective source views, including across
  different supported initial draws. Successful decoders and checkpoints are
  derived internally. It does not recover erased original intentions.
- [SourceServiceOriginalPrefix](../Vegas/Game/SourceServiceOriginalPrefix.lean)
  binds the same all-owner memory restoration to the actual normalized rank
  decoder. The resulting auxiliary carrier has the complete original source
  prefix law, with correlated initial parameters retained. Effectiveness is
  derived internally. This does not identify physical own recall or native
  information posteriors with restored intentions.
- [SourceServiceOriginalPrefixRetraction](../Vegas/Game/SourceServiceOriginalPrefixRetraction.lean)
  proves every supported restored carrier compresses to that exact native
  decoder. Its joint retraction retains the same full traffic and physical
  own recall/input. It assumes no traffic factorization or posterior law.
- [SourceServiceFirstActivationResources](../Vegas/Game/SourceServiceFirstActivationResources.lean)
  derives actual first-input trace, protection, fresh slot and earlier-call
  conformance for either owned decision kind. Binding traffic consumes these
  shared facts. [SourceServiceResolutionPhaseTraffic](../Vegas/Game/SourceServiceResolutionPhaseTraffic.lean)
  supplies command-level silent traffic coupling tied to the actual scheduler's
  traces; its round theorem consumes that same proof.
- [SourceServiceFirstBindingTraffic](../Vegas/Game/SourceServiceFirstBindingTraffic.lean)
  joins the actual first-turn source draw, whole next-prefix decoder and full
  stopped traffic. Fixed-draw traffic coupling preserves original/effective
  successor pairs and an unchanged parameter from a prior source-view/traffic
  factorization. The law
  applies to initialized exact first-turn phases. The whole-prefix consumer
  below supplies that induction; retained-waiting incentives remain separate.
- [SourceServiceFirstTurnBindingFactorization](../Vegas/Game/SourceServiceFirstTurnBindingFactorization.lean)
  lifts the actual global commitment phase through one fixed aligned slice.
  It derives the source choice and next-prefix decoder and retains the same
  parameter and full traffic through the whole behavioral source step.
- [SourceServiceFirstResolutionTraffic](../Vegas/Game/SourceServiceFirstResolutionTraffic.lean)
  joins the actual global first-turn resolution kernel with the whole next
  prefix and the same full stopped traffic. Effective source disclosures
  supply supported TRUE realizability; FALSE is an explicit packet.
- [SourceServiceFirstResolutionCoupling](../Vegas/Game/SourceServiceFirstResolutionCoupling.lean)
  couples the untouched wait, first protected resolution response and actual
  completion stop. It derives trace, protection, fresh-slot and conformance
  resources from initialized play. From the prior pair-view/traffic law it
  retains original and effective successors and an unchanged parameter with
  the same stopped traffic.
  The whole-view consumer below identifies actual global effective choices;
  the pure-first-turn rank law below assembles those phases. The common
  original-memory carrier is restored through the same actual traffic.
- [SourceServiceFirstTurnResolutionFactorization](../Vegas/Game/SourceServiceFirstTurnResolutionFactorization.lean)
  lifts the actual global resolution phase through the shared source slice.
  Tail effectiveness supplies supported normalization and realizability;
  actual completion derives the whole successor decoder. The same parameter
  and full traffic are retained through the whole effective source step.
- [SourceServiceSampleCompletion](../Vegas/Game/SourceServiceSampleCompletion.lean)
  derives silence and exact stopped sample/configuration laws for any turn
  timing from an actual boundary and complete play.
  [ReactiveSamplePhase](../Vegas/Pending/ReactiveSamplePhase.lean) couples full
  focal traffic through one real silent sample round under the public
  scheduler. [SourceServiceStoppedSampleTraffic](../Vegas/Game/SourceServiceStoppedSampleTraffic.lean)
  carries that coupling through the entire stopped sample run, retaining the
  same public sample value and full traffic.
  [SourceServiceStoppedSampleFactorization](../Vegas/Game/SourceServiceStoppedSampleFactorization.lean)
  joins the actual public draw, both source successors, an unchanged parameter
  and that same traffic
  channel from the prior source-view factorization. Pure-first-turn induction
  is assembled below; native assessment transport remains separate.
  [SourceServiceFirstTurnSampleFactorization](../Vegas/Game/SourceServiceFirstTurnSampleFactorization.lean)
  lifts that actual sample law through one fixed aligned source slice,
  preserving the same parameter and full traffic through the whole source
  behavioral step. The whole endpoint decoder is derived from completion.
- [SourceServiceBindingResponseCompletion](../Vegas/Game/SourceServiceBindingResponseCompletion.lean)
  joins the actual transmitting draw to its typed successor and full stopped
  traffic. Waiting remains separate; prescribed foreign continuations are
  required for the probability factorization.
  [SourceServiceBindingPrefixCompletion](../Vegas/Game/SourceServiceBindingPrefixCompletion.lean)
  identifies the whole source step, including the actual unfinished decoder
  result on waiting.
- [SourceServiceReachedDecoding](../Vegas/Game/SourceServiceReachedDecoding.lean)
  derives source residuals with a forward view map and partial view recovery
  from their actual transport maps.
  [SourceServiceDecoderSlice](../Vegas/Game/SourceServiceDecoderSlice.lean)
  fixes a compiler-aligned tail, embedding, reference-order certificate, lift
  and recovery from source syntax and rank. Effectiveness inherits through the
  same recursion, with decoder splitting for every store and history. Native
  Bayes transport
  still needs the actual source-prefix likelihood.
- [SourceServiceFirstTurnSharedCheckpoint](../Vegas/Game/SourceServiceFirstTurnSharedCheckpoint.lean)
  derives actual typed checkpoints in one shared aligned slice at every
  initialized first-turn rank endpoint. Typed states and action histories
  are read from the real store and completion history, without an endpoint
  or source-likelihood premise.
- [SourceServiceFirstTurnRankFactorization](../Vegas/Game/SourceServiceFirstTurnRankFactorization.lean)
  derives the actual initialized whole source-prefix/full-traffic law at every
  pure-first-turn rank, preserving the same initial parameter. The marginal
  is the true source behavioral iteration; traffic factors through the whole
  effective source observation.
- [SourceServiceOriginalRankTraffic](../Vegas/Game/SourceServiceOriginalRankTraffic.lean)
  restores all original histories once, with the same initial parameter and
  actual full traffic. Its channel reads the compressed original focal view;
  no marginal or likelihood equation is supplied.
- [SourceServiceOriginalFirstInput](../Vegas/Game/SourceServiceOriginalFirstInput.lean)
  derives the true original prefix/parameter joint law with the actual first
  ready owner input for bindings and resolutions. The source-view channel is
  total on actual inputs, read before the response. These pure-first-turn laws
  do not replace physical recall or supply native Bayes/retained-waiting proofs.
- [SourceServiceOriginalFirstInputPosterior](../Vegas/Game/SourceServiceOriginalFirstInputPosterior.lean)
  derives the compressed source observation from each actual supported input.
  Its conditional full original-source/initial-parameter law equals the true
  source posterior on that compressed observation. Uncompressed intentions,
  native assessment history identification and perturbed beliefs remain distinct.
- [PassageBayes](../GameTheoryExtensions/Analysis/Protocol/PassageBayes.lean)
  derives actual terminal ancestor weights and conditional Bayes beliefs at
  information antichains with variable depths, including the same stochastic
  readout or original-memory lottery on the actual earlier history.
  [ReactivePassageBayes](../Interaction/ReactivePassageBayes.lean) projects the
  earlier observed control to the native state posterior; it does not use the
  final control or assume a stopping likelihood.
- [SourceServiceFirstInputPassage](../Vegas/Game/SourceServiceFirstInputPassage.lean)
  identifies the terminal chronological first event input with actual passage
  through a first-event native information site. Later turns cannot overwrite
  this readout; its mass is the true native information mass at variable depths.
  [AsyncServiceFirstInputPassage](../Vegas/Game/AsyncServiceFirstInputPassage.lean)
  identifies the normalized first-turn profile's initialized complete input law
  with the actual rank and first-activation stopped law. The joint ancestor
  restoration is supplied by the terminal and native posterior laws below.
- [SourceServiceInitialReadout](../Vegas/Game/SourceServiceInitialReadout.lean)
  decodes the same initial source environment from persistent graph inputs at
  arbitrary initialized descendants and legal native histories. The input
  encoding is injective, and terminal source readout has the same initial
  state. This is an analysis readout, not a new private or public observation.
- [SourceServiceFirstInputSourceLaw](../Vegas/Game/SourceServiceFirstInputSourceLaw.lean)
  joins the real stopped configuration's original-prefix restoration, same
  decoded initial parameter and actual input in one common memory draw.
  [SourceServiceFirstInputReadoutPosterior](../Vegas/Game/SourceServiceFirstInputReadoutPosterior.lean)
  derives its true source posterior on the recovered compressed view.
  [SourceServicePastPrefix](../Vegas/Game/SourceServicePastPrefix.lean) recovers
  that earlier prefix from persistent fields and lower-rank completions under
  arbitrary legal continuations. Perturbed waiting transport remains open.
- [SourceServiceFirstInputAncestor](../Vegas/Game/SourceServiceFirstInputAncestor.lean)
  derives the actual owned ancestor's prefix from readiness and sequential
  order, then preserves its readout through every legal native descendant.
  It requires neither clean play nor a common information-history depth.
- [SourceServiceFirstInputTerminalLaw](../Vegas/Game/SourceServiceFirstInputTerminalLaw.lean)
  identifies the represented first-turn terminal source-restoration/input
  joint law with the genuine stopped law. Its same-draw restoration kernel is
  preserved along actual continuations.
- [SourceServiceFirstInputNativePosterior](../Vegas/Game/SourceServiceFirstInputNativePosterior.lean)
  derives the actual native ancestor belief's true original source-prefix and
  initial-parameter posterior at every positive-mass first owned site. It uses
  one common memory draw and one recovery function across sites and assessments;
  the antichain is derived from native recall. No clean-history or likelihood
  premise is assumed.
  [AsyncServiceFirstTurnBeliefResources](../Vegas/Game/AsyncServiceFirstTurnBeliefResources.lean)
  derives physical support and clear owner risk on each actual Bayes history.
  Perturbed waiting beliefs and sequential rationality remain open.
- [SourceServiceInitialTraffic](../Vegas/Game/SourceServiceInitialTraffic.lean)
  derives the actual initialized parameter/source/full-traffic factor through
  the whole source view. Correlated initial private types are retained; the
  initial candidate catalogue is determined by the same source view.
- [AsyncServiceCounterfactualBeliefs](../Vegas/Game/AsyncServiceCounterfactualBeliefs.lean)
  cancels the entire focal owner's recalled-action likelihood from native
  Bayes normalization. Relative escape still needs a bound against the actual
  opponent-and-nature denominator, including foreign waiting probabilities.
- [AsyncServiceForeignEscape](../Vegas/Game/AsyncServiceForeignEscape.lean)
  proves focal clarity at every compatible hidden history and identifies
  escape exactly with foreign private recalled submission or opportunity risk.
  The actual clean witness has positive counterfactual mass under full mixing;
  conditional escape is bounded by summed foreign private-risk mass divided
  by that clean mass. The required vanishing ratio is still unproved.
- [SourceServiceWaitRiskConfounding](../Vegas/Game/SourceServiceWaitRiskConfounding.lean)
  proves actual accepted typed-success branches with identical foreign input
  but different sender opportunity-risk recall. Its separate finite path law
  has conditional risk one half. Initialization, an all-history contract and
  actual native likelihood identification are not supplied by this calculation.
- [SourceServiceLateTurnCompletion](../Vegas/Game/SourceServiceLateTurnCompletion.lean)
  transfers the timely canonical call's accepted-step/public-miss dichotomy to
  the actual turn-counted continuation. Real recorded recall suppresses calls
  until this event completes; future-event policy is retained. Acceptance
  probabilities and waiting incentives remain separate.
- [LateResolutionService](../Vegas/Examples/LateResolutionService.lean)
  proves the asynchronous contract at every raw history of a concrete compiled
  resolution. Its public scheduler can censor late TRUE while including late
  FALSE before expiry.
- [LateResolutionContinuation](../Vegas/Examples/LateResolutionContinuation.lean)
  reaches an initialized legal late turn and computes the actual terminal
  typed payoff and collected audit. TRUE and silence yield `−D`; accepted
  FALSE yields `0` for every authentic partial audit. Every current timing
  policy is silent at this input because protection has ended. Preservation
  remains possible through rational free continuation there.
- [LateResolutionSourceEquilibrium](../Vegas/Examples/LateResolutionSourceEquilibrium.lean)
  constructs a consistent source assessment with TRUE as its strategy and
  proves SE for the declared source payoff. Actual source histories supply the
  single strategic resolution, finiteness and full-mixing resources.
- [LateResolutionNativeSite](../Vegas/Examples/LateResolutionNativeSite.lean)
  supplies a real bounded risk-menu decision site and legal FALSE at the same
  input as the forced-silence regret. Its late prefix is supported by the actual
  geometric turn policy for every positive deferral weight below one, when
  later timing slots exist. This is physical policy reach; identifying its
  finite-menu representation also needs whole-law coverage.
- [LateResolutionNativeInformation](../Vegas/Examples/LateResolutionNativeInformation.lean)
  derives the audited suffix resources at every actual history sharing that
  native input. Authentic provenance and silent own recall force the entire
  network empty in this one-player fixture; public observation identifies
  readiness, clock and remaining commands. No Bayes premise is supplied.
- [LateResolutionNativeContinuation](../Vegas/Examples/LateResolutionNativeContinuation.lean)
  proves the actual native terminal-state law is the current response followed
  by four passive commands, independently of all future player policies.
- [LateResolutionNativeRationality](../Vegas/Examples/LateResolutionNativeRationality.lean)
  proves native WAIT value `−D` and legal FALSE value `0` under every belief
  at the entire late information fiber. For a positive deposit, the entire
  current turn prescription fails native sequential rationality and SE for
  every timing lottery. Consistent native beliefs exist but do not remove
  this regret. Rational free late completion remains available.
- [LateResolutionNativePerturbation](../Vegas/Examples/LateResolutionNativePerturbation.lean)
  proves regret at least `(1 − ε)D − ε` under the actual fully mixed native
  Bayes assessment. At one fixed site it is eventually at least `D/2` as
  trembles vanish, even for varying source and timing approximants. Every
  actual fiber history is supported. This concerns the waiting prescription;
  source-preserving rational free completion remains possible.
- [LateResolutionFreeLate](../Vegas/Examples/LateResolutionFreeLate.lean)
  proves every raw response at the concrete late fiber has terminal typed
  failure and audited value at most zero for a nonnegative deposit. Legal
  FALSE attains zero and is locally optimal under any beliefs. This is a
  free late continuation; the whole native equilibrium remains separate.
- [LateResolutionFirstActivation](../Vegas/Examples/LateResolutionFirstActivation.lean)
  derives the deterministic actual first native input under every profile,
  identifies its entire information fiber and proves its clear menu admits
  only WAIT or canonical FALSE/TRUE. TRUE availability uses actual message
  bounds coverage.
- [LateResolutionFirstDecision](../Vegas/Examples/LateResolutionFirstDecision.lean)
  proves actual first FALSE/TRUE acceptance and the forced silent completed
  second menu.
- [LateResolutionNativeSites](../Vegas/Examples/LateResolutionNativeSites.lean)
  exhaustively classifies actual initialized decision sites as first, late
  unrecorded, or late completed.
- [LateResolutionFirstPayoff](../Vegas/Examples/LateResolutionFirstPayoff.lean)
  derives the accepted first decision's full typed source readout and zero
  authentic partial-audit charge.
- [LateResolutionFirstOptimality](../Vegas/Examples/LateResolutionFirstOptimality.lean)
  proves TRUE optimal at the entire protected first fiber and forced silence
  optimal at both completed second fibers, under any beliefs.
- [LateResolutionFreeEquilibrium](../Vegas/Examples/LateResolutionFreeEquilibrium.lean)
  constructs a native risk-menu SE: TRUE first, FALSE late after WAIT, forced
  silence after completion. It preserves the source opening equilibrium's
  initialized joint full typed readout and realized settlement vector under
  any authentic partial sampler and nonnegative deposit. The concrete larger
  menu extension below supplies rational completion; arbitrary-service
  preservation remains open.
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
  through the restoration without assuming a posterior equation. The original
  rank law identifies it with actual pure-first-turn native traffic.
- [DisclosureProfileJointChannel](../Vegas/Game/DisclosureProfileJointChannel.lean)
  retains correlated initial parameters, the complete original source state
  and the same source-view channel draw through the common memory lottery.
  The original rank and first-input laws above identify the actual channel
  for pure-first-turn execution. Perturbed timing remains separate.
- [SourceServiceAuthorizationBreach](../Vegas/Game/SourceServiceAuthorizationBreach.lean)
  proves final rejection of actual invalid-token and foreign-actor packets.
  [SourceServiceAuditableCollection](../Vegas/Game/SourceServiceAuditableCollection.lean)
  includes these in its information-local classifier and derives collection
  from partial observation and conditional reporting coverage. Valid-token
  off-turn packets are not automatically forbidden.
- [SourceServiceNodeKindBreach](../Vegas/Game/SourceServiceNodeKindBreach.lean)
  derives final rejection of commitments at non-binding nodes and opening or
  withholding at non-resolution nodes. The same auditable classifier uses
  it with the existing collection bound. Other unclassified packets retain
  their own obligations.
- [SourceServiceCompletedPacket](../Vegas/Game/SourceServiceCompletedPacket.lean)
  derives final rejection of a fresh identifier allocated after its named
  event completed. The actual committed response supplies that identifier,
  and the auditable classifier uses the same collection bound. An original
  accepted envelope remains permitted. Repeated calls before completion need
  the distinct pair argument below; the newer packet can be accepted.
- [SourceServiceDuplicatePackets](../Vegas/Game/SourceServiceDuplicatePackets.lean)
  derives at least one final forbidden verdict from two actual distinct
  same-event envelopes. Partial coverage gives the total collection bound
  across arbitrary behavioral continuations, choosing the forbidden packet
  at each final history. A clear recorded risk-menu prefix plus another
  transmission reconstructs that actual pair.
- [SourceServiceRecordedCollection](../Vegas/Game/SourceServiceRecordedCollection.lean)
  classifies that extra response from own recall and derives collection after
  its actual information-site commitment. The risk extension includes it with
  the fixed clean comparator and deposit. This removes the class from the
  other-exclusion comparison hypothesis; it gives no renewed-charge claim
  after an earlier fine.
- [SourceServicePublicRejection](../Vegas/Game/SourceServicePublicRejection.lean)
  proves persistent rejection from actual public handler conditions. The
  auditable classifier uses it for openings with wrong candidate ownership
  or public binding association at the owner's ready resolution. These
  collection comparisons use the existing partial-evidence backend; private
  binding capability repair remains separate.
- [SourceServiceRiskExtension](../Vegas/Game/SourceServiceRiskExtension.lean)
  extends an audited risk-menu equilibrium after classified packet coverage
  and other-exclusion comparisons are supplied. It does not embed a source
  equilibrium into that auxiliary game.
- [SourceServiceResolutionComplement](../Vegas/Game/SourceServiceResolutionComplement.lean)
  proves effective responses outside both charged classifiers are retained
  at a clear actual resolution prefix. Tokens, public checks and trace
  invariants derive conformance; no fresh-envelope premise is supplied.
  [SourceServiceUnusableBinding](../Vegas/Game/SourceServiceUnusableBinding.lean)
  completes the clear-prefix partition: every other effective response is
  retained or a canonical binding with absent or mistyped private opening.
  The risk extension confines its remaining upper comparison to that exact
  information-local residual. The continuation comparison remains unproved.
- [ReactiveBindingPendingExpiry](../Vegas/Pending/ReactiveBindingPendingExpiry.lean)
  proves the pending unusable binding's actual due-expiry frame law. Both
  executions complete with the remembered original failure and retain the
  public miss, service recall, traffic and reconstructed owner input. It
  supplies no whole-policy settlement comparison or additional fine.
- [ReactiveBindingRiskResolve](../Vegas/Pending/ReactiveBindingRiskResolve.lean)
  admits a first timely FALSE decision in the actual repaired risk menu and
  couples a supported waiting/FALSE mixture through the retained implementation.
  It preserves the full frame and private memory without fallback, protection
  or a blanket menu-coverage premise. Later inclusion, certificate-dependent
  raw responses and the whole-policy comparison remain separate.
- [ReactiveBindingCertificateRepair](../Vegas/Pending/ReactiveBindingCertificateRepair.lean)
  proves that the actual mistyped bare commitment installs an owned certificate
  capability its typed-default replacement cannot reproduce, despite equal
  networks. This identifies a coupling gap, not an SE counterexample. Later
  public misses can occur without another owner turn, their deposit is sunk,
  and late canonical acceptance can remain uncharged. A stopped repair needs
  the genuine shared waiting and continuation comparisons.
- [ReactiveMissingBindingTransport](../Vegas/Pending/ReactiveMissingBindingTransport.lean)
  derives one-step packet transport after an actual absent opening is replaced.
  Original effective responses remain available; bounded raw responses can be
  copied after original-input normalization. The blocked candidate loses no
  original owned capability. Later handler acceptance can still differ for
  an uncertified opening, so whole-policy frame closure remains open.
- [ReactiveMissingOpeningEvidence](../Vegas/Pending/ReactiveMissingOpeningEvidence.lean)
  keeps the actual missing commitment's candidate blocked under arbitrary
  continuations. Every later opening claim for that handle lacks matching
  authentic evidence, including forwarding, and is an existing signed-content
  breach. Its final verdict and partial collection laws apply without a new
  backend premise; whole-policy dominance remains separate.
- [ReactiveBindingAcceptedOpening](../Vegas/Pending/ReactiveBindingAcceptedOpening.lean)
  derives full inclusion-frame preservation from actual original opening
  acceptance, including publication failure. A matching authentic certificate
  transfers repaired acceptance to the original state; repaired-only
  acceptance identifies an actual signed-content breach. Policy reconstruction
  and the stopped terminal comparison remain open.
- [ReactiveBindingInertWindow](../Vegas/Pending/ReactiveBindingInertWindow.lean)
  couples actual finite waiting and activation windows, retaining the full
  frame, input recall and original opening capabilities. Owner policies use
  normalized bounded responses without new commitments; foreign raw policies
  and public scheduler choices retain their joint law. Inclusion, the first
  breach stopping argument and terminal dominance remain open.
  The implementation uses the complete bounded effective menu; membership in
  the narrower service risk menu is a separate obligation.
- [ReactiveBindingOpeningStep](../Vegas/Pending/ReactiveBindingOpeningStep.lean)
  classifies actual opening inclusion as full-frame preservation or a concrete
  owner-authored signed breach in the same pending envelope. Invalid tokens
  and paired rejections preserve the frame; foreign catalogue equality
  identifies the author of repaired-only acceptance.
- [SourceServicePastCommitmentTraffic](../Vegas/Game/SourceServicePastCommitmentTraffic.lean)
  derives old commitment ranks from issued readiness tokens in an actual
  ready sequential prefix. A policy sending no new owner commitments preserves
  the bound under arbitrary foreign responses and scheduler commands. Once
  this event completes, all old token-valid owner commitments name completed
  events. The noncommitment stopped evaluator below uses this resource;
  later commitments and terminal comparison remain separate.
- [ReactiveBindingCommitmentStep](../Vegas/Pending/ReactiveBindingCommitmentStep.lean)
  preserves the full inclusion frame for old owner commitments addressed to
  completed events and foreign commitments using their actual fixed candidate
  meaning. Invalid tokens and public rejections retain matching false receipts.
- [ReactiveBindingPacketStep](../Vegas/Pending/ReactiveBindingPacketStep.lean)
  combines all packet constructors and every actual scheduler command into
  an exact frame-or-owner-breach environment coupling. It preserves the same
  pending envelope and common partial observation draw.
- [ReactiveBindingInertClosure](../Vegas/Pending/ReactiveBindingInertClosure.lean)
  derives environment preservation of opening capabilities and fixed actual
  implementation shadow under the noncommitment owner slice.
- [ReactiveImplementationInvariant](../Interaction/ReactiveImplementationInvariant.lean)
  preserves unrestricted service invariants in the actual private-memory
  joint evaluator.
- [SourceServiceMissingStoppedCoupling](../Vegas/Game/SourceServiceMissingStoppedCoupling.lean)
  couples the actual whole continuation and the same implementation's joint
  memory law when the owner sends noncommitment responses or registers later
  fresh bare bindings with arbitrary private material. The completed preparation
  still excludes additional owner commitments. Endpoints preserve the current frame, memory, actual
  candidate provenance, opening capabilities and actual risk records, or the
  same owner-authored signed breach in both inputs. Clean branches have equal
  service risk for every inclusion bound. Initialized traces discharge ordinary service
  invariants. One common finite induction serves both the complete effective
  and risk menus; repaired risk admission is derived from actual original
  support, current binding invariants and recalled records. Reused
  later bindings and terminal utility domination remain open.
  Fresh copied bindings use candidate-only memory, preserving actual
  acceptance or expiry. The fixed-calendar repair induction carries
  `BindingShadow.CompletedAt` from empty initial memory through actual
  completed blocks, ruling out stale ready-event overrides without an extra
  capstone assumption. Reused handles use fixed material. Fresh copied mistyped
  registrations retain their actual raw capability; the candidate changed by
  the initial repair still requires a separate continuation argument.
- [ReactiveBindingRiskRecall](../Vegas/Pending/ReactiveBindingRiskRecall.lean)
  derives equal complete risk records from both actual raw traces and their
  common public activation history. It accounts for a pending activation whose
  response is not recorded yet. Paired owner responses preserve these records
  when they name the same event. Risk equality alone does not admit arbitrary
  effective responses at clear canonical-menu sites.
- [ReactiveBindingRiskAdmission](../Vegas/Pending/ReactiveBindingRiskAdmission.lean)
  derives same-response repaired risk-menu admission at whole inputs from
  actual original risk support and invariants. Clear binding/resolution inputs
  derive fresh typed slots, protected windows and TRUE certificate/guard
  success; expanded inputs transport effective responses. The same retained
  implementation realizes invocation and resume coupling on the explicit
  noncommitment/fresh-copy/fixed-reuse slice. The stopped coupling composes fresh
  copies and, for actual missing-registration origins, fixed reuses outside the
  changed slot or with public associations. Changed unassociated slots, initial
  mistyped certificates and terminal utility domination remain separate.
- [SourceServiceAliasEquilibrium](../Vegas/Game/SourceServiceAliasEquilibrium.lean)
  supplies the final private raw-alias transport, retaining correlated
  collection and prior charges.
- [ReactiveBindingPublicTraffic](../Vegas/Pending/ReactiveBindingPublicTraffic.lean)
  retains public scheduler data and all foreign inputs jointly when private
  binding meanings differ. Canonical binding transmission, arbitrary foreign
  raw responses and arbitrary inclusion at a sole-ready binding preserve the
  readout.
- [ReactiveBindingPublicRounds](../Vegas/Pending/ReactiveBindingPublicRounds.lean)
  retains this whole joint readout through actual scheduler rounds and common
  partial observation draws. Foreign raw policies remain arbitrary; only the
  binding owner is silent.
- [SourceServiceBindingSelection](../Vegas/Game/SourceServiceBindingSelection.lean)
  identifies that silence with actual recorded turn policy for any timing.
  Its complete stopped law preserves public selection, misses and all foreign
  inputs under changes to the canonical binding's private value, jointly with
  the same correlated prefix parameter. Finite-budget exhaustion is allowed.
  The actual unique-call acceptance/miss classification is composed below;
  waiting incentives remain separate.
- [SourceServiceBindingChoiceSelection](../Vegas/Game/SourceServiceBindingChoiceSelection.lean)
  joins the actual source commitment draw with this private-value-independent
  selection law at the same physical prefix and initial parameter. The failure
  reference packet is only a physical proof experiment. Completion and
  acceptance probabilities are not premises of this factorization.
- [SourceServiceBindingFirstPacket](../Vegas/Game/SourceServiceBindingFirstPacket.lean)
  identifies every owner packet naming an initially unrecorded current event
  with the exact manual canonical call, throughout its recorded-policy stop.
  Actual recall and provenance exclude an earlier packet; arbitrary foreign
  responses and scheduler commands preserve the whole envelope.
- [ReactiveBindingAcceptanceReceipts](../Vegas/Pending/ReactiveBindingAcceptanceReceipts.lean)
  derives an actual owner-authored ledger commitment and accepting receipt
  for each accepted binding association on every initialized raw history.
  This closes receipt origin.
- [SourceServiceBindingAttemptCompletion](../Vegas/Game/SourceServiceBindingAttemptCompletion.lean)
  derives the exact typed dichotomy for a manual timely first binding call at
  an initialized raw prefix with a fresh counted candidate: this identifier
  accepted, unmarked and exact chosen successor, or actual public miss, no
  accepting receipt and typed failure.
  Initialization and complete play derive all endpoint resources. Selected-input
  resources derive freshness from the actual trace, without global risk clarity.
  The owner subsequently follows any recorded timing policy, against arbitrary
  foreign raw policies. The current call need not be protected or policy-supported.
- [SourceServiceBindingAttemptLaw](../Vegas/Game/SourceServiceBindingAttemptLaw.lean)
  joins the actual residual source commitment draw, typed output and the same
  public/foreign traffic with the prefix parameter retained. The actual
  failure-reference selection kernel's receipt for this identifier selects
  the drawn value or typed failure. The miss marker remains in public traffic.
- [SourceServiceBindingNoAttempt](../Vegas/Game/SourceServiceBindingNoAttempt.lean)
  derives actual public miss, typed failure and absence of every owner event
  packet when an initialized unrecorded binding's protection has closed.
  Activation persistence and clock monotonicity keep the gate closed, so any
  timing lottery is silent until complete play ends the event. Foreign raw
  policies are arbitrary; waiting incentive comparisons remain open.
- [SourceServiceTimingMixture](../Vegas/Game/SourceServiceTimingMixture.lean)
  derives the original finite timing prior from actual untouched recall and
  decomposes the whole completion-stopped strategic execution into real
  owner-only turn-family runs. Private recall and all traffic stay joint;
  binding and resolution consumers retain the same prefix parameter. Absent
  selected turns, lost protection and finite-budget exhaustion remain real
  outcomes; the selected-family strategic comparison remains separate.

- [SourceServiceBindingSelectedInput](../Vegas/Game/SourceServiceBindingSelectedInput.lean)
  derives the actual chronological selected input and supported canonical
  response, or completion before it with no owner event packet, a public miss
  and typed failure. No selected-slot visit or source admission is assumed.
- [SourceServiceBindingStoppedResponse](../Vegas/Game/SourceServiceBindingStoppedResponse.lean)
  decomposes an actual protected geometric response and its full stopped
  continuation into real waiting and receipt-driven source commitment
  selection. Earlier waits remain in the original input. The full selected
  family laws below supply actual source-choice factorization; the strategic
  waiting comparison remains open.
- [ReactiveBindingUsableStep](../Vegas/Pending/ReactiveBindingUsableStep.lean)
  derives full-frame inclusion closure for matching fixed owner candidates,
  including rejected and late calls. Fresh usable submission establishes
  those matching meanings with actual completed-boundary memory.
- [ReactiveUsedBindingOpening](../Vegas/Pending/ReactiveUsedBindingOpening.lean)
  proves every opening of a used mistyped candidate is rejected. An authentic
  certificate can violate public association or typed guards.
- [SourceServiceUsedBindingOpening](../Vegas/Game/SourceServiceUsedBindingOpening.lean)
  derives the used association from an actual recalled protected sole
  commitment before a later owned resolution and classifies its mistyped
  opening under existing partial collection. Whole-policy repair and payoff
  domination remain open.

- [SourceServiceBindingSelectedAssembly](../Vegas/Game/SourceServiceBindingSelectedAssembly.lean)
  composes the original timing prior, actual selected-input stop and real
  completion into one joint law, whose physical marginal is the actual
  completed binding law. The auxiliary input is the original chronological
  before-response recall. No selected visit or acceptance mass is assumed.
- [ReactiveBindingCommitmentProvenance](../Vegas/Pending/ReactiveBindingCommitmentProvenance.lean)
  preserves actual owner commitments that address completed events, use a
  publicly associated handle or have matching fixed candidate meanings, across
  foreign/noncommitment responses, shared fresh registration and all environment
  commands. Later
  Fresh usable whole-run repair is proved by the stopped coupling below.

- [LateResolutionPreservation](../Vegas/Examples/LateResolutionPreservation.lean)
  preserves EVERY source SE of the concrete fixture in the native risk menu,
  with the same full typed terminal state and realized settlement vector.
  Actual source rationality derives its TRUE law.
- [LateResolutionEffectiveExtension](../Vegas/Examples/LateResolutionEffectiveExtension.lean)
  bounds every effective continuation at each retained history by an actual
  clean retained continuation. It extends every audited risk-menu SE to the
  complete effective menu and preserves the whole terminal control law.
- [LateResolutionRawPreservation](../Vegas/Examples/LateResolutionRawPreservation.lean)
  preserves EVERY original source SE of this fixture in the full bounded raw
  runtime, with the same joint typed terminal state and realized sampled
  settlement vector. It needs authentic partial observation and a nonnegative
  deposit, without a detection bound. Arbitrary-service preservation remains
  open.
- [ReactiveCompletedConfig](../Vegas/Pending/ReactiveCompletedConfig.lean)
  proves that arbitrary raw submissions and environment commands preserve the
  entire graph configuration once all events complete. Further traffic and
  charges remain possible.
- [ReactiveBindingCopiedWindow](../Vegas/Pending/ReactiveBindingCopiedWindow.lean)
  couples one actual effective owner response law to the same retained private
  implementation, permitting noncommitments, fresh bare registrations with
  arbitrary private material and fixed reuses with matching meanings or actual
  public associations.
  It preserves current memory, the full frame, commitment provenance
  and original opening capabilities.
- [ReactiveBindingCopiedResume](../Vegas/Pending/ReactiveBindingCopiedResume.lean)
  extends this real one-policy response law to arbitrary foreign raw actions
  and inactive resumptions.
  [ReactiveBindingPacketStep](../Vegas/Pending/ReactiveBindingPacketStep.lean)
  also admits actual fixed matching owner candidates at inclusion. The complete
  fresh-copy suffix is composed by both effective and risk-menu stopped couplings;
  utility comparison and finite reused-candidate closure remain open.
- [SourceServiceBindingSelectedResources](../Vegas/Game/SourceServiceBindingSelectedResources.lean)
  derives fresh counted candidates, actual owner turn/slot invariants and no
  earlier owner packet at the real selected raw input. Its aligned source
  configuration is unchanged; protection gives the actual source commitment
  kernel, and a closed gate gives silence. Other owners may use raw actions.
- [SourceServiceBindingSelectedReference](../Vegas/Game/SourceServiceBindingSelectedReference.lean)
  derives the silent reference's actual selected before-response input, raw
  trace, unchanged source configuration, fresh slot and original commitment
  lottery from the actual completion boundary and horizon bound. It assumes
  neither a selected visit nor global risk clarity.
- [SourceServiceSelectedReference](../Vegas/Game/SourceServiceSelectedReference.lean)
  supplies the same actual before-response trace, source configuration and
  recalled turn resources for both strategic event kinds. A missing selected
  input derives actual completion, a public miss and no owner packet.
  [ReactiveResolutionMiss](../Vegas/Pending/ReactiveResolutionMiss.lean) derives
  immutable typed publication failure from the actual marker on all initialized
  raw histories, independently of watcher evidence.
- [SourceServiceResolutionSelectedCompletionLaw](../Vegas/Game/SourceServiceResolutionSelectedCompletionLaw.lean)
  joins the original timing prior to the actual resolution input and completion.
  Protected FALSE/TRUE draws use their own full traffic kernels; closed hits and
  absent selection give actual misses and typed failure.
  [SourceServiceResolutionProtectedCompletion](../Vegas/Game/SourceServiceResolutionProtectedCompletion.lean)
  derives acceptance from effective compiler-aligned disclosures through
  [SourceServiceProtectedDecisionCompletion](../Vegas/Game/SourceServiceProtectedDecisionCompletion.lean).
  Waiting incentives remain open.
- [SourceServiceSelectedResponse](../Vegas/Game/SourceServiceSelectedResponse.lean)
  proves the exact stopped execution law by replacing the actual silent
  reference response with the original selected input's canonical lottery.
  Removing its last own recall entry recovers the same before-response
  execution; no assumed selection probability or support redraw is used.
- [SourceServiceSelectedContinuation](../Vegas/Game/SourceServiceSelectedContinuation.lean)
  proves the full selected-family stopped continuation equals actual owner
  silence after its selected response, including closed-gate silence. This
  literal timing-policy law does not supply rational free late completion.
  [SourceServiceBindingProtectedAttempt](../Vegas/Game/SourceServiceBindingProtectedAttempt.lean)
  derives acceptance of the actual canonical packet and its exact typed successor
  at a protected raw input. Fresh-call settlement and packet provenance exclude
  the miss branch; no acceptance probability is assumed.
  [SourceServiceBindingSelectedAttemptLaw](../Vegas/Game/SourceServiceBindingSelectedAttemptLaw.lean)
  composes the selected family's actual source draw and stopped continuation,
  retaining typed output, the prefix parameter and all public/foreign traffic.
  [SourceServiceBindingSelectedCompletionLaw](../Vegas/Game/SourceServiceBindingSelectedCompletionLaw.lean)
  joins the original timing prior to that same actual reference prefix.
  Protected hits use the source lottery and actual accepted typed outcome;
  closed hits and earlier completion use real misses and typed failure.
  Selected input, prefix parameter and all public/foreign traffic stay joint.
  This operational decomposition does not establish rational free continuation.
  [SourceServiceBindingSelectedClosedCompletion](../Vegas/Game/SourceServiceBindingSelectedClosedCompletion.lean)
  derives the real public miss, typed failure and absence of owner packets after
  the literal family's selected closed-gate silence. These physical laws do not
  supply the rational free continuation or its conditional incentive comparisons.

[SourceServiceBindingAcceptancePosterior](../Vegas/Game/SourceServiceBindingAcceptancePosterior.lean)
conditions an actual timely first binding call on its real receipt flag. The
residual source draw remains independent of the same conditioned public/foreign
traffic kernel, with accepted typed value or actual missed failure. It covers
unprotected calls under the owner's recorded turn-policy continuation. Returned
free continuations may send further raw packets, so this does not yet identify
their conditional source law.

[SourceServiceUnusableProtectedCall](../Vegas/Game/SourceServiceUnusableProtectedCall.lean)
derives the actual acceptable protected call from a clear legal unusable-binding
input, including absent or mistyped material. At a completed raw continuation,
its sole identifier gives an accepting receipt and the actual used-handle
association. Sole remains explicit because a later raw retry can void protection.
[SourceServiceUnusableDuplicate](../Vegas/Game/SourceServiceUnusableDuplicate.lean)
proves the actual sole-or-duplicate partition from recalled responses and real
traffic records. At complete settlement this yields used association or the
existing conditional one-time collection bound; it gives no renewed fine or
whole-policy utility comparison.
[ReactiveBindingUsedCommitment](../Vegas/Pending/ReactiveBindingUsedCommitment.lean)
derives complete-frame rejection of any commitment reusing a publicly associated
handle, regardless of private candidate meaning. The actual traffic relation
retains completed events, permanent used associations or matching candidate meanings
through arbitrary responses and scheduler commands. Full commitment support
and the duplicate-packet strategic comparison remain open.

[SourceServiceMissingAssociatedCoupling](../Vegas/Game/SourceServiceMissingAssociatedCoupling.lean)
derives the changed handle's public association from an actual protected sole
missing-opening call at completion. A policy gate on that persistent public
association has exactly the original ungated continuation law. The same finite
repair coupling then permits every later bare owned fixed reuse, without a
changed-slot avoidance premise. Initial mistyped material and the signed-breach
exception remain separate.

[SourceServiceMissingSignedResponse](../Vegas/Game/SourceServiceMissingSignedResponse.lean)
handles an actual signed opening or evidence-bearing commitment at a repaired
input, using full effective original support. A clear legal repaired input
excludes the signed breach and the existing retained implementation selects its
legal fallback with unchanged shadow. An expanded input copies the effective
commitment and its actual signed envelope. One shared draw gives both the
original invocation and actual retained implementation marginals. No frame is
asserted after fallback, and whole-policy payoff comparison remains open.

[ReactiveBindingForeignCommitment](../Vegas/Pending/ReactiveBindingForeignCommitment.lean)
derives permanent public rejection for a bare commitment naming another
player's handle. Submission and private copying leave the application and
shadow unchanged, including for fresh foreign handles. The commitment ledger
and the same finite fixed/associated continuation consumers carry this class
using the real ownership test. Evidence-bearing commitments remain a separate
signed-breach case; terminal payoff domination is not inferred.

[SourceServiceMissingResponseClassification](../Vegas/Game/SourceServiceMissingResponseClassification.lean)
classifies every effective original response at the actual clear repaired
input, without original risk-menu support. Actual envelope and recalled-event
transport give the retained copy or excluded auditable, recorded or unusable
branches of the same implementation. Static value coverage, real counted-slot
freshness, capacity and protection derive typed-default admission for the
uncharged unusable branch. This does not preserve a frame after fallback or
control the resulting whole-policy payoff; mistyped certificates can still
change the future capability relation.

[SourceServiceSiteKind](../Vegas/Game/SourceServiceSiteKind.lean) derives the
actual local input and either a publicly completed cut or a ready event with
one of the seven source constructor kinds at every actual response-menu site.
This applies to arbitrary builders, including activations after graph
completion. The completed-cut branch needs its own payoff comparison; the
fixed-calendar ready-phase exhaustion alone does not cover it.

The risk-menu continuation consumers still require original risk-supported
future responses. An excluded initial response can reach information states
absent from the retained game, so profile extension does not imply that
condition there. Full effective-menu continuations need a separate repair and
comparison argument, including subsequent exclusions and risk-open inputs.

[ReactiveBindingCandidateAgreement](../Vegas/Pending/ReactiveBindingCandidateAgreement.lean)
derives outside-slot equality and old-certificate preservation from genuine
same-before missing/repair registrations and their actual preparations. The
same finite continuation induction preserves already equal slots. Its fixed
risk-menu consumer derives those resources from the real origins, admitting
reuses outside the changed slot or with actual public associations. Full
commitment support, initial mistyped certificates and terminal utility remain
separate.

[ReactiveBindingCopiedSubmission](../Vegas/Pending/ReactiveBindingCopiedSubmission.lean)
preserves the full frame and actual raw candidate capability when a later fresh
bare commitment is copied with its original material, including mistyped or
absent material. The retained implementation copies originals already admitted
at the actual input, otherwise trying default repair and a legal fallback. One
sampling engine records the original response in either case. Calendar callers
derive full copy/repair agreement from their actual compiled menu. The stopped
coupling composes fresh copies with arbitrary private material. Initially
changed candidate reuse and whole-policy utility domination remain open.

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
