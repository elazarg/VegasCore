# Artifact and validation guide

For sequential-equilibrium results and remaining work, start with the
[research map](docs/se-preservation-roadmap.md). It distinguishes the checked
full-language SE compiler, the general-roster revelation compiler, the
action-restriction theorem, and the remaining research boundaries.
The [implementation stack](docs/se-compilation-stack.md) records the checked
proof edges and explicit assumptions of the source-to-raw theorem.

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python scripts/report-open-obligations.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

Do not run `lake update` when reproducing a revision. The cache only accelerates
the subsequent kernel-checked build.

## What is checked

| Boundary | Owning code |
| --- | --- |
| Source execution and safety | `Vegas/Source/` |
| Source legal-history interfaces, pure policies, and continuation laws | `Vegas/Source/CommitmentInterface.lean`, `Vegas/Source/ProtocolEvaluation.lean`, `Vegas/Source/SetupProtocolEvaluation.lean` |
| Source pure SPE characterization, including private setup | `Vegas/Game/SourceSubgame.lean`, `Vegas/Game/SetupSubgame.lean` |
| Source behavioral policies, continuation laws, and SPE characterization | `Vegas/Source/ProtocolBehavioralPolicy.lean`, `Vegas/Source/SetupProtocolBehavioral.lean`, `Vegas/Game/BehavioralSubgame.lean` |
| Conditional behavioral SPE preservation and reflection at proper roots | `GameTheoryExtensions/Protocol/BehavioralContinuation.lean` |
| Conditional pure SPE preservation and reflection at proper roots | `GameTheory/GameTheory/Protocol/Continuation.lean` |
| Proper reactive subgames after two deterministic initial responses | `Interaction/ReactiveSubgamePrefix.lean` |
| Honest source SPE whose compiled graph policy fails SPE under uniform, at-most-once inclusion | `Vegas/Examples/ReactiveEarlyOpeningSPE.lean` |
| Immutable authorization at original submission, with conditional exclusion at every legal continuation | `Interaction/ReactiveAuthorization.lean`, `Vegas/Pending/ReactiveAuthorization.lean` |
| Authorized unfinished packets belong to the sender's current ready owned event under source information discipline | `Interaction/ReactiveRecallInvariant.lean`, `Vegas/Pending/ReactiveAuthorizationProgress.lean` |
| Premature packets in the early-opening witness remain unauthorized; fresh later openings are authorized | `Vegas/Examples/ReactiveAuthorization.lean` |
| Source to typed graph and canonical single-policy correspondence | `Vegas/Compile/EventGraphCanonical.lean`, `Vegas/Compile/EventGraphDeviation.lean` |
| Sequential completion by dependency barriers | `Vegas/EventGraph/Sequential.lean` |
| Message transport and player policies | `Interaction/MessageApplication.lean`, `Interaction/MessageApplicationPolicies.lean` |
| Event-addressed runtime and service | `Vegas/Pending/EventApplication.lean`, `Vegas/Pending/EventService.lean` |
| Binding from authenticated submission through arbitrary native continuations | `Vegas/Pending/EventCommitmentBinding.lean` |
| Multiplayer native action protocol, policy equivalence, and bounded native execution | `Vegas/Pending/NativeProtocol.lean`, `Vegas/Pending/NativeProtocolPolicy.lean`, `Vegas/Pending/NativeProtocolEvaluation.lean`, `Vegas/Pending/NativeProtocolSafety.lean` |
| Fresh candidates at every native prefix and direct construction of typed binding material | `Vegas/Pending/EventFreshCandidates.lean`, `Vegas/Pending/EventBindingAction.lean` |
| Full-source honest law under adaptive public graph scheduling | `Vegas/Compile/EventGraphScheduling.lean` |
| Full-source asynchronous deviations and Nash correspondence | `Vegas/Compile/EventGraphDeviation.lean`, `Vegas/Game/EventCompilation.lean` |
| Asynchronous pending-message service and arbitrary-player completion | `Vegas/Pending/EventService.lean`, `Vegas/Pending/EventServiceCompletion.lean` |
| Asynchronous pending-message deviation reduction | `Vegas/Pending/EventDeviationLaw.lean`, `Vegas/Pending/EventStrategicLaw.lean` |
| Full-source pending-message deviations and Nash correspondence | `Vegas/Game/EventMessageStrategic.lean` |
| Full-source initialized compiler law, including fresh bindings, sampling and guarded disclosure | `Vegas/Game/SourceServiceLaw.lean` |
| Authentic partial traffic audit and public binding omissions preserve the full-source joint typed-outcome/realized-settlement law on every admitted compiled profile | `Vegas/Pending/ReactiveServiceAudit.lean`, `Vegas/Game/SourceServiceAudit.lean` |
| Every source SE of the full language, for finite commitment payload types, has a permitted native SE with the same typed source terminal law; each native decision site is compared with original source deviations by its kind | `Vegas/Game/SourceServiceEquilibrium.lean`, `Vegas/Game/SourceServiceSiteKind.lean`, `Vegas/Game/SourceServiceUnsentBinding.lean`, `Vegas/Game/SourceServiceAvailableOpening.lean` |
| Every source SE of the full language, for finite commitment payload types, has an audited bounded raw-runtime SE with the source joint typed-terminal-state/payoff law, the payoff realized as settlement and no charge on its paths; a complete audit meets the audit hypotheses (`Vegas.Paper.source_audited_raw_sequential_equilibrium`, `SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved`) | `Vegas/Game/SourceServiceCompilation.lean`, `Paper.lean` |
| Actual continuation-repair couplings imply settlement comparisons; a deposit fixed from all effective-history payoff extrema removes the separate gain-bound premise | `Vegas/Game/SourceServiceRepairSettlement.lean`, `Vegas/Game/ServicePayoffBounds.lean` |
| Actual timed binding, guarded disclosure and public sampling with exact physical policy mixtures and full execution laws | `Vegas/Game/SourceServiceTimedPolicy.lean`, `Vegas/Game/SourceServiceTimedBinding.lean`, `Vegas/Game/SourceServiceTimedDisclosure.lean`, `Vegas/Game/SourceServiceTimedSample.lean` |
| Every physical response at an actual permitted source-service decision is a replay alias or supported by the actual source compiler, given derived effective source support | `Vegas/Game/SourceServiceLocalSupport.lean` |
| One original Bayes sequence supports all effective source choices after unreachable-view completion; actual continuations and the original assessment limit are unchanged | `Vegas/Source/ProtocolChoiceFiniteness.lean`, `Vegas/Source/DisclosureSupport.lean`, `Vegas/Game/SourceChoiceCompletion.lean`, `Vegas/Game/SourceServiceChoiceSupport.lean` |
| Stopped repair through a whole remaining binding roster, with permitted repaired traces and forbidden-record/omission/observation alternatives | `Vegas/Game/SourceServiceBindingWaiting.lean`, `Vegas/Game/SourceServiceStoppedBindingWindow.lean` |
| Exact stopped repair of arbitrary off-turn roster responses, with persistent signed evidence or unchanged observations and legal repaired endpoint traces | `Vegas/Pending/ReactiveOffTurnRepair.lean`, `Vegas/Pending/ReactiveOffTurnWindow.lean`, `Vegas/Game/SourceServiceOffTurnWindow.lean` |
| Every certificate in a permitted network execution originates in a recorded successful resolution; actual guarded opening aliases agree at an unsent source opportunity | `Vegas/Pending/ReactiveResolutionEvidence.lean`, `Vegas/Game/SourceServiceEvidence.lean` |
| Initial-parameter/public-result joint laws and Bayesian Nash correspondence | `Vegas/Source/InitialState.lean`, `Vegas/Game/ParameterOutcomes.lean` |
| Two-player zero-sum source Nash value equals every native coarse-correlated value under the paper service | `Vegas/Game/ZeroSum.lean`, `GameTheory/GameTheory/Core/ZeroSum.lean` |
| Finite decision tables preserve every legal continuation law | `GameTheory/GameTheory/Protocol/DecisionPlan.lean` |
| Correlated mixtures of independently trembled finite plans retain an action-probability floor after recall conditioning | `GameTheory/GameTheory/Protocol/TremblingPlans.lean`, `GameTheory/GameTheory/Math/Probability/UniformTremble.lean` |
| Finite zero-sum saddle existence with L1 feature penalties and a security-based penalty bound | `GameTheoryExtensions/Analysis/ZeroSumRegularization.lean` |
| Identical normal-form CE correspondence does not imply SE outcome preservation | `GameTheoryExtensionsTests/CorrelatedSequentialGap.lean` |
| Zero-sum Nash equilibria can have equal expected payouts and different payout laws | `GameTheoryExtensionsTests/ZeroSumOutcomeLaws.lean` |
| Exact payoff-subspace incentive criteria and component-based bounds on deviation gains | `GameTheory/GameTheory/Analysis/IncentiveCone.lean`, `GameTheory/GameTheory/Analysis/Protocol/Incentives.lean`, `GameTheoryExtensions/Analysis/Protocol/Sequential.lean` |
| Additive payoffs are exactly those preserved by every change of correlation with fixed marginals | `GameTheoryExtensions/Analysis/CorrelationPayoff.lean` |
| Communication can make source nonstrategic payoffs strategic; coupled zero-sum constraints give strictly stronger incentive implications | `GameTheoryExtensionsTests/ComponentCommunication.lean`, `GameTheoryExtensionsTests/CoupledIncentives.lean` |
| Conditional sanction bounds, sufficient local sequential rationality, and the exact detection limit for alarms with zero false positives | `GameTheoryExtensions/Analysis/Enforcement.lean` |
| Exact finite-family criterion for all sufficiently large sanctions, incremental liability, and first-departure gain/detection bounds | `GameTheoryExtensions/Analysis/EnforcementLimits.lean` |
| Executable least scalar deposit for rational comparison tables; soundness, minimality over real deposits, and infeasible-row witnesses | `GameTheoryExtensions/Analysis/EnforcementSynthesis.lean`, `GameTheoryExtensionsTests/EnforcementSynthesis.lean` |
| Local structural action restrictions imply continuation laws, retained beliefs, consistent rational completion, and general SE extension with exact net-payoff laws | `GameTheory/GameTheory/Protocol/ActionRestriction.lean`, `GameTheory/GameTheory/Analysis/Protocol/RestrictionExtension.lean`, `GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean` |
| Nested reactive response menus construct structural restrictions with unchanged observations and arbitrary continuation laws; every menu has decision-site recall | `Interaction/ReactiveMenuRestriction.lean`, `Interaction/ReactiveOwnPlay.lean`, `InteractionTests/ReactiveMenuRestriction.lean` |
| Checkpoint prefix-law and Bayes-belief projection with different source/native step counts | `GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean` |
| Passive sampling followed by ordinary replay and public at-most-once report inclusion gives persistent receipt and ledger evidence | `Interaction/ReactiveMonitoring.lean` |
| Packets outside a ready public event reject in barrier-ordered graphs; timely reporting retains evidence of premature traffic | `Vegas/Pending/ReactiveMonitoring.lean` |
| Current-address submissions are canonical after normalization, rejected, or publicly nonconforming, under explicit binding/node premises | `Vegas/Pending/ReactiveOpeningConformance.lean` |
| Reveal-only source programs retain all withholding choices, count decisions by open obligations, and accept guards from an empty registry | `Vegas/Source/RevealSequence.lean`, `Vegas/Examples/RevealSequence.lean` |
| Canonical opening and silence/expiry blocks use the existing reactive service and preserve full execution effects under explicit acceptance/deadline premises | `Vegas/Pending/ReactiveRevealBlock.lean` |
| A fixed reveal service and restricted response menu are constructed inside the actual native backend; source choices admit finite action splitting with exact Boolean projection and full support | `Vegas/Game/RevealService.lean`, `Vegas/Game/RevealServiceActions.lean` |
| The reveal-service policy adapter reuses the source event compiler and stays within C at every input; monitored settlement composes watcher/report, ticks and expiry for either source branch | `Vegas/Game/RevealServicePolicy.lean`, `Vegas/Pending/ReactiveRevealSettlement.lean` |
| The supported initial values extend a finite raw message alphabet without removing responses, and cover authentic openings at checkpoints retaining the initial binding tables | `Vegas/Pending/ReactiveInitialValues.lean`, `Vegas/Game/RevealServiceBounds.lean` |
| Actual source/native revelation preserves typed store and completion-history agreement; a native decision view recovers the exact source view, including correlated initial types | `Vegas/Game/RevealServiceState.lean`, `Vegas/Game/ServiceInformation.lean` |
| Equal source views reconstruct the native graph observation and initial candidate catalogue; full before-view equality reduces to explicit public service/transcript invariants | `Vegas/Game/ServiceObservation.lean` |
| Reveal-service decision clocks follow from existing observations at every raw history and every response menu, with a watcher distinct from source owners | `Vegas/Game/RevealServiceClock.lean` |
| The actual compiled owner-choice law equals the residual source reveal kernel under the compiler's suffix, store and own-history invariants | `Vegas/Game/RevealServiceCorrespondence.lean` |
| Every ordinary response executes a complete monitored reveal block with exact typed source-state and action-history agreement; published replays retain their actual network and recall effects | `Vegas/Pending/ReactiveRevealResponse.lean`, `Vegas/Game/RevealServiceBlock.lean` |
| Every finite-menu behavioral profile settles the general reveal service within its horizon, including arbitrary malformed traffic | `Vegas/Game/RevealServiceCompletion.lean` |
| Extra effective responses produce attributable rejection or format violations; reserved inclusion and reporting collect persistent evidence with the actual fresh-packet sampling probability | `Vegas/Game/RevealServiceEnforcement.lean` |
| Earlier source observations are recoverable from later reveal-only observations along actual protocol histories; public result prefixes determine candidate ledger encodings | `Vegas/Source/ObservationRecall.lean`, `Vegas/Pending/RevealTranscript.lean` |
| Every watched SE of the general reveal service extends to the full bounded raw game with the same joint observation/net-payoff law, assuming zero watcher utility at every history | `Vegas/Game/RevealServiceWatcher.lean` |
| Induction over actual service blocks gives the initialized typed source-state law for arbitrary reveal sequences, all source policies, correlated valid bindings and every alias-splitting weight | `Vegas/Game/RevealServiceCheckpoint.lean`, `Vegas/Game/RevealServiceExecution.lean`, `Vegas/Game/RevealServiceLaw.lean` |
| Exact public calendar and transcript encodings are preserved by actual normalized openings and published replay aliases | `Vegas/Game/RevealServiceCalendarState.lean`, `Vegas/Game/RevealServiceTranscript.lean`, `Vegas/Pending/ReactiveRevealTranscript.lean` |
| Monitoring bounds apply to standard behavioral continuations; deposits compare every extra response with any clean legal continuation at operational checkpoints | `Vegas/Game/RevealServiceCollection.lean`, `Vegas/Game/RevealServiceOrdinaryComparison.lean`, `Vegas/Game/RevealServicePayoffs.lean` |
| Finite rational payoff extrema bound all continuation gains; the existing scalar checker computes the sufficient range/rate deposit | `GameTheoryExtensions/Analysis/FinitePayoffBounds.lean` |
| Source decision depths, finite reveal-only histories and observation-prefix recovery use the actual setup protocol, including correlated initialization | `Vegas/Game/SourceInformation.lean`, `Vegas/Game/SourceObservationRecall.lean` |
| A focal selector preserves Boolean action laws; actual recorded-response prefixes and normalized emitted entries support its history-fiber proof | `Vegas/Game/RevealServiceSelector.lean`, `Interaction/ReactiveRecordedResponse.lean`, `Vegas/Pending/ReactiveResponseRecall.lean` |
| Source-state prefix laws hold at actual native behavioral decision depths; source observations reconstruct the focal player's replay recall, including repeated owners | `Vegas/Game/RevealServicePrefixBehavioral.lean`, `Vegas/Game/RevealServiceOwnerPrefix.lean`, `Vegas/Game/RevealServiceFocalRecall.lean` |
| General SE extension under a sound terminal audit preserves the actual joint randomized net-payoff law, with correlated partial verdicts and explicit conditional collection assumptions | `GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean` |
| An audit readout records actual transmissions and public phases under arbitrary schedulers; evidence persists, replays retain broadcaster attribution, and authentic partial records give no false accusations of compliant traffic | `Interaction/ReactiveTrafficAudit.lean` |
| Per-record partial-audit coverage implies conditional collection after a detected first step, against arbitrary subsequent behavioral play | `Interaction/ReactiveAuditCollection.lean` |
| Arbitrary finite activation/wait windows preserve application state and current observations when pending identifiers and retained replay responses are already public | `Interaction/ReactivePublishedResponses.lean` |
| One native information-site law replacement is one actual response followed by the original profile's continuation, with sufficient remaining fuel | `Interaction/ReactiveLocalContinuation.lean` |
| Source one-site continuation values factor through the original posterior state, current action law and unchanged baseline continuation | `Vegas/Game/SourceLocalContinuation.lean` |
| Fully mixed source perturbations compile to fully mixed native profiles; one common native consistent assessment preserves source-state posteriors at every owner site | `Vegas/Game/RevealServiceMixing.lean`, `Vegas/Game/RevealServiceBayes.lean`, `Vegas/Game/RevealServiceConsistency.lean` |
| Every original revelation-sequence source SE compiles to a restricted native SE, with whole-policy conditional optimality and exact joint typed state/payoff law | `Vegas/Game/RevealServiceOwnerValue.lean`, `Vegas/Game/RevealServiceOwnerIncentives.lean`, `Vegas/Game/RevealServiceEquilibrium.lean` |
| Every retained terminal history is clean; concrete conditional sampling supplies collection against every extra ordinary response at every retained site | `Vegas/Game/RevealServiceClean.lean`, `Vegas/Game/RevealServicePrefixEnforcement.lean`, `Vegas/Game/RevealServiceOwnerCollection.lean` |
| Every retained revelation-service SE extends to the full bounded raw game under sufficient range deposits and positive passive-observation coverage | `Vegas/Game/RevealServiceOrdinaryExtension.lean` |
| Actual finite watched-history payoff extrema supply sufficient fixed deposits before choosing an equilibrium | `Vegas/Game/RevealServiceDeposits.lean` |
| End-to-end SE preservation for arbitrary finite revelation sequences, repeated owners and correlated valid initial bindings, with exact joint typed terminal-state/net-payoff law | `Vegas/Game/RevealServiceCompilation.lean` |
| The full history traffic audit is exactly reconstructible from existing service recall at every legal prefix and invariant under private normalization | `Interaction/ReactiveTrafficState.lean` |
| Every retained prefix has conforming traffic; every extra effective action produces actual attributable forbidden traffic | `Vegas/Game/RevealServiceWatcherSupport.lean`, `Vegas/Game/RevealServiceTraffic.lean`, `Vegas/Game/RevealServiceTrafficSound.lean`, `Vegas/Game/RevealServiceTrafficDeparture.lean` |
| Native terminal-audit enforcement for arbitrary retained menus and services with a common decision clock; source-to-raw instance with fixed deposits for every player and exact joint typed outcome/realized settlement law | `Vegas/Pending/ReactiveAuditEquilibrium.lean`, `Vegas/Game/RevealServiceAuditDeposits.lean`, `Vegas/Game/RevealServiceAuditCompilation.lean` |
| Deferred binary hazards realize the exact choice law and admit full-support perturbations converging to a final-opportunity compiler | `GameTheoryExtensions/Math/Probability/DeferredChoice.lean` |
| A finite mixture of scheduled response policies is realized behaviorally by the actual interaction-plan evaluator under arbitrary sampling and intervening responses | `Interaction/ReactivePolicyMixture.lean`, `Vegas/Pending/ReactivePolicyMixture.lean` |
| Unpublished own packets add no passive information; including one identifier makes every remaining copy of that identifier public | `Interaction/DeferredObservation.lean` |
| Opaque binding submission and inclusion preserve foreign recall and pending-observation laws across different privately fixed binding meanings | `Vegas/Pending/ReactiveBindingObservation.lean` |
| Two ready canonical opening times give different remembered pending observations despite equal final public states and equal phase/ledger traffic-audit records; this is an information distinction, not an SE impossibility | `Vegas/Examples/OpeningTimingChannel.lean` |
| An actual unusable binding and a valid binding followed by withholding have equal public audit transcripts, so a sound public audit cannot distinguish them | `Vegas/Examples/UnusableBindingAudit.lean` |
| From an arbitrary residual source belief, behavioral deviations using unusable bindings admit value-only continuation mixtures with the same joint parameter/result law and a conditional best-response comparator | `Vegas/Source/ValueBindingContinuation.lean` |
| Completing a sequential event starts its successor's deadline at the actual completion time; local early and expiry branches both admit increasing deadlines | `Vegas/Pending/EventSequentialTiming.lean` |
| Canonical evidence requests coincide exactly when certificates resolve equally; raw finite compiler coverage remains separate from normalization | `Vegas/Pending/EvidenceNormalization.lean`, `Vegas/Pending/ReactiveFiniteCompiler.lean`, `Vegas/Examples/SuccessfulEvidenceAliases.lean` |
| Pending published identifiers yield no new observations; spent replay preserves this local property without erasing scheduler or action recall | `Interaction/MessageReplayObservation.lean`, `Interaction/ReactiveQuiescent.lean` |
| Reserved inclusion ignores inserted or removed published pending copies and actual spent replays | `Vegas/Pending/ReactiveReplaySelection.lean` |
| The actual C/W/N menus inherit decision clocks from all raw histories; every watched-game SE extends to the effective native game when watcher utility is identically zero | `Vegas/Examples/MonitoredGuessing/Restricted.lean`, `Vegas/Examples/MonitoredGuessing/RestrictedClock.lean`, `Vegas/Examples/MonitoredGuessing/WatcherExtension.lean` |
| Both source choices at both reveals have checked service laws, including silent withholding followed by expiry | `Vegas/Examples/MonitoredGuessing/RestrictedExecution.lean` |
| Restoring watcher choices and every bounded raw private alias preserves the joint observation/payoff law, for normalization-invariant readouts and identically zero watcher utility | `Vegas/Examples/MonitoredGuessing/WatcherRaw.lean`, `GameTheoryExtensions/Protocol/ContinuationHorizon.lean` |
| Every final raw Alice response has a local legal comparator at the source checkpoints, for arbitrary declared payoff tables and nonnegative rejection charges | `Vegas/Examples/MonitoredGuessing/RestrictedFinalComparison.lean` |
| Unselected Bob packets leave Alice's entire next input equal to the silent source branch under the fixture's empty Alice passive sample | `Vegas/Examples/MonitoredGuessing/BobContinuation.lean` |
| Global recall can fail at inactive states while decision recall and the generic SE existence theorem still apply | `GameTheory/GameTheory/Protocol/DecisionRecall.lean`, `GameTheoryExtensionsTests/DecisionRecall.lean` |
| Nonvacuous general-theorem instance: Alice's departure creates a new Bob decision; deposit one preserves every source SE and the exact zero-payoff law | `GameTheoryExtensionsTests/RestrictionEnforcement.lean` |
| Declared integer return tables share operational graph execution; inferred charges deter every raw early submission; prescribed native play retains the exact type/result/net-payoff law | `Vegas/EventGraph/PayoffTransport.lean`, `Vegas/Examples/MonitoredGuessing/Payoffs.lean`, `Vegas/Examples/MonitoredGuessing/PayoffInference.lean`, `Vegas/Examples/MonitoredGuessing/PayoffLaw.lean` |
| Exact caught/missed continuation criterion; forcing the sender's future actions to fail cannot repair disclosure when it has no remaining source actions | `GameTheoryExtensions/Analysis/FailureEnforcement.lean`, `GameTheoryExtensionsTests/ForcedFailureEnforcement.lean` |
| Simultaneous finite-agent best responses with pinned behavior and mandatory trembles; exact realization by original protocol execution | `GameTheory/GameTheory/Analysis/PerturbedEquilibrium.lean`, `GameTheory/GameTheory/Analysis/Protocol/AgentForm.lean` |
| Construct fully mixed Bayes approximants and one consistent limit with jointly optimal local responses at all free information sites | `GameTheory/GameTheory/Analysis/Protocol/AgentCompletion.lean` |
| Ex ante local gains equal information-set reach times Bayes continuation gains; a whole continuation deviation has an information-local implementation | `GameTheoryExtensions/Analysis/Protocol/LocalDeviation.lean`, `GameTheoryExtensions/Analysis/Protocol/ContinuationDeviation.lean` |
| With finitely many histories and decision-site recall, consistent local optimality implies whole-policy sequential rationality on terminal play, including off-path sites; no common decision clock is assumed | `GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean`, `GameTheoryExtensions/Analysis/Protocol/BehavioralOneShot.lean` |
| Sequential equilibrium on terminal play exists with finitely many histories and decision-site recall, for arbitrary real payoffs | `GameTheory/GameTheory/Analysis/Protocol/SequentialExistence.lean` |
| Rare contamination preserves even off-path limiting beliefs; finite-prefix departure probability is bounded by the per-step risk times horizon | `GameTheory/GameTheory/Math/Probability/Domination.lean`, `GameTheoryExtensions/Math/Probability/FirstDeparture.lean` |
| A profitable deviation admits a finite sound sanction exactly when its observation law has positive mass outside all admitted observations | `GameTheoryExtensions/Analysis/ObservableEnforcement.lean` |
| Ordinary-view packet reports, soundness on compliant snapshots, and conditional sampling/report-delivery bounds | `Interaction/MessageMonitoring.lean`, `Interaction/MessageMonitoringProbability.lean` |
| Ledger-only conformance evidence persists through arbitrary raw continuations; accepted extra evidence in the native fixture escapes the pilot's charge but is publicly detectable | `Interaction/ReactiveLedgerConformance.lean`, `Vegas/Examples/MonitoredGuessing/Conformance.lean` |
| Every compiled graph decision satisfies the packet evidence checker; ordinary passive sampling detects the native counterexample with exactly its sampling probability | `Vegas/Pending/ReactiveConformance.lean`, `Vegas/Examples/PassiveDisclosureMonitoring.lean` |
| Automatic penalties preserve every SE outcome law of the ordinary guessing game, with a converse under strict collateral and unchanged net payoff laws | `GameTheoryExtensionsTests/AmbientEnforcementEquilibrium.lean` |
| Every source SE of the finite private-state sender/receiver class extends to an SE with identical state and net payoff laws under typewise disclosure charges; payoff-range bounds give a fixed target for all source SEs | `GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean` |
| Statewise constant-sum, including zero-sum, games in that decision class preserve every source SE under optional disclosure without sanctions | `GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean` |
| Every SE of the actual initialized guessing program has a bounded native SE with identical joint private-bit/public-result/net-payoff law, for fixed collectible charge `D ≥ 2` | `Vegas/Examples/MonitoredGuessing/Equilibrium.lean`, `Vegas/Examples/MonitoredGuessing/NativePayoff.lean` |
| One fixed playerwise policy translation preserves every source SE of that initialized guessing program and its joint secret/result/net-payoff law | `Vegas/Examples/MonitoredGuessing/Compilation.lean` |
| Every SE of the literal two-reveal program with any integer return table and zero watcher payoff has a full bounded raw native SE preserving joint initial type, results and net payoffs | `Vegas/Examples/MonitoredGuessing/DeclaredCompilation.lean` |
| Fixed source-to-restricted policies preserve all-profile joint laws and source SE; every restricted SE extends through ordinary, watcher and raw response restoration | `Vegas/Examples/MonitoredGuessing/RestrictedEquilibrium.lean`, `Vegas/Examples/MonitoredGuessing/RestrictedLaw.lean`, `Vegas/Examples/MonitoredGuessing/RestrictedExtension.lean` |
| Sharp collateral thresholds against arbitrary target SE implementations: one half for fair guessing, one for all source guessing laws | `GameTheoryExtensionsTests/AmbientEnforcementThreshold.lean` |
| Explicit pending certificates escape a ledger-only alarm; a network-input alarm requires stronger observations | `Vegas/Examples/DisclosureMonitoring.lean` |
| Shared randomness enables signaling through permitted traffic; even observing the receiver's public guess does not permit detection with zero false positives | `GameTheoryExtensionsTests/MonitoredSignaling.lean` |
| Auction failure of dominance, including every faithful translation | `Vegas/Examples/CommitRevealAuction.lean` |
| SE separation for accepted named evidence, with literal declared and compiled settlement payoffs | `Vegas/Examples/SelectiveAssociation/SourceEquilibrium.lean`, `Vegas/Examples/SelectiveAssociation/Settlement.lean`, `Vegas/Examples/SelectiveAssociation/PayoffSeparation.lean` |
| Native SE with empty passive observation, all legal information sites and whole-policy deviations | `Vegas/Examples/SelectiveAssociation/RestrictedEquilibrium.lean`, `Vegas/Examples/SelectiveAssociation/RestrictedPrefixPosterior.lean`, `Vegas/Examples/SelectiveAssociation/RestrictedBeliefs.lean` |
| Isolated passive-observation change defeats preservation of that SE's payout law | `Vegas/Examples/SelectiveAssociation/RestrictedSeparation.lean` |
| Generic simulation and equilibrium transport | `GameTheoryExtensions/` |
| Paper-visible theorem selection and axiom pins | `Paper.lean` |

The proved capstones are universally quantified proofs, not conclusions
inferred from tests.

The [enforcement experiments](docs/disclosure-enforcement-design.md) separate
the incentive effect of an automatic penalty from monitoring and collection.
The generic finite sender/receiver class admits arbitrary priors, finite
receiver actions and arbitrary payoffs. It preserves every source SE under
typewise deterrence, with one common consistent assessment construction and
exact state and net payoff laws. A fixed bound on sender payoff ranges supplies
the same target charges and playerwise compiler for every source SE.
Statewise constant-sum games in this class need no sanctions: the receiver's
informed best response already supplies the sender's incentive to stay silent.
The Boolean guessing game retains every ordinary source choice and adds an
optional disclosure charged only to its sender. A utility penalty of one
implements every source SE by a playerwise translation, preserving the joint
secret/guess law and the actual net payoff-vector law. The threshold is sharp:
fair guessing is implementable exactly from one half, and all source guessing
laws exactly from one, among nonnegative penalties. Above one, every target SE
also has the state and net payoff laws of a source SE. The native monitoring
experiment checks the visibility of explicit certificates, and the signaling
experiment checks what a monitor lacking shared private information can detect.
The abstract experiments do not themselves implement a native monitor or escrow.

The [general restriction theorem](GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean)
preserves every given source SE in a fixed target game under structural local
execution correspondence and conditional enforcement bounds. It constructs
consistent target beliefs and rational new decisions, and preserves the exact
completed-history/net-payoff law. The protocols must have finite histories,
decision-site recall, common-depth decision sites and aligned steps. Its collection
premise covers arbitrary continuations; a strategic watcher who can decline
reporting needs a separate argument. This theorem is not yet an all-program
source-to-native compiler theorem.

The [monitored native theorem](Vegas/Examples/MonitoredGuessing/Equilibrium.lean)
connects the actual initialized two-reveal source program to its compiled graph
and the existing bounded raw-message runtime. Every source SE has a native SE
with the same joint initial-bit, public-result and actual net-payoff-vector law.
The [fixed playerwise translation](Vegas/Examples/MonitoredGuessing/Compilation.lean)
additionally makes Bob's completion depend only on his own source policy;
Alice's and Watcher's policies are fixed. This semantic translation uses
classical choice and does not supply executable strategy synthesis.
The fixed service permits one early Alice response, ordinary half-probability
passive observation by a strategic Watcher, and inclusion gated by its public
replay. All bounded malformed calls, evidence requests and replays remain legal
alternatives. A fixed `D ≥ 2` rejection charge deters the early transmission;
the proof supplies rational continuations at every information site and one
consistent trembling sequence. Watcher is indifferent at zero utility, and
collectibility is an explicit assumption; paid reporting and escrow are not
implemented. See the [scope audit](docs/research/se-native-pilot.md).
The [declared-payoff family](Vegas/Examples/MonitoredGuessing/DeclaredCompilation.lean)
has a separate end-to-end theorem for every integer return table with zero
watcher payoff. It starts with the literal source program's assessment and
evaluated returns, retains source opening and withholding, and preserves the
joint initial-bit/result/net-payoff law in the full bounded raw game. Deposits
are fixed at twice Alice's whole payoff range and Bob's whole payoff range.
All extra ordinary responses have checked continuation comparisons; watcher
restoration and private-alias lifting finish the native extension. Completion
at new information sites may depend on the source assessment, so this broader
result does not supply the pilot's fixed playerwise completion guarantee.

The family uses the specified fair-bit setup, fixed service calendar, partial
watcher sampling, and empty Alice pending sample after Bob's response. Initially
valid commitments, ideal evidence and collectible deductions remain explicit
assumptions. The result covers neither fresh source commitments nor arbitrary
reveal sequences, and it retains source withholding. See the
[response and scope audit](docs/research/monitored-response-coverage.md).

The [general revelation theorem](Vegas/Game/RevealServiceCompilation.lean)
covers arbitrary finite reveal sequences, including repeated owners, correlated
valid initialization, and arbitrary typed terminal utilities with zero watcher
utility. A single game and deposit vector, computed mathematically from finite
watched-history payoff extrema and positive coverage, preserve every original
source SE and its joint typed terminal-state/net-payoff law. This is the full
bounded raw response menu at the service's specified activations. Arbitrary
intervening activations and fresh source commitments remain open. It is forward
existence, with a noncomputable consistent completion; it does not assert
reflection, unique target equilibria or a fixed playerwise completion algorithm.

The [terminal-audit capstone](Vegas/Game/RevealServiceAuditCompilation.lean)
uses the same source class and calendar, but imposes no zero-utility reporter
condition. It derives fixed all-player deposits from the effective game's finite
payoff range. The native SE uses expected audited utilities and preserves the
joint law of the actual randomized settlement vector, including any correlation
between players' audit verdicts. Authentic phase-and-broadcaster records,
positive conditional record coverage and collection are explicit service
assumptions. No audit information is added before the last strategic choice.
Envelope signatures alone do not satisfy the broadcaster-attribution contract.

The [selective-association comparison](docs/selective-association-proof-contract.md)
keeps the compiled application, service calendar, deadlines, selector and full
bounded raw menus fixed. Empty passive observation admits a sequential
equilibrium giving Alice expected payout zero. Under the specified passive leak,
every sequentially rational assessment gives her at least one half. Therefore
even arbitrary, payoff-dependent strategy and belief translations cannot match
that equilibrium's Alice payout law. The positive proof uses one common fully
mixed Bayes sequence and checks every legal information site, including off-path
sites. Payouts are the program's signed integer settlement expressions. This
finite comparison does not establish general source-to-native SE preservation
or a result for unrestricted packets and unbounded interaction.

The source protocol and generic continuation-transfer results do not establish
native SPE preservation. Recovery has checked initialized execution laws and
local incentive guarantees, but
[`ReactiveEarlyOpeningSPE.lean`](Vegas/Examples/ReactiveEarlyOpeningSPE.lean) proves
that the current compiler fails SPE under the specified uniform service.
The [counterexample guide](docs/early-opening-and-spe.md) explains the exact
scope, completion facts, and profitable deviation. Whole-service continuation
laws and a contract sufficient for positive native SPE preservation remain open.
The [combined service design](docs/reactive-spe-service.md) records the checked
authorization consequences and the remaining enforcement and continuation
obligations. No authorization-enforcing backend or native SPE preservation
theorem is claimed by these conditional results.
`Vegas/Examples/SourceProtocol.lean` and
`Vegas/Examples/SetupProtocol.lean` check information-set closure on hidden source
prefixes; `GameTheory/GameTheory/Tests/ContinuationTransfer.lean` proves that the
atomic irreversible-failure example has no uniform continuation-law certificate.
`Vegas/Examples/BehavioralProtocol.lean` checks mixed binding admission with an
infinite player universe and retention of bindings after a prefix.
`Vegas/Examples/EventService.lean` and the source/event-graph tests are concrete
execution regressions.
`Vegas/Examples/ParameterOutcomes.lean` checks a private-bit example with identical
public marginals and different type-dependent utilities.
`Vegas/Examples/InFlightCommitment.lean` checks binding before inclusion: reading
another pending message permits a new candidate but cannot change a transmitted
handle. `Vegas.Paper.native_commitment_binding` audits the general invariant.
The same regression checks private memory without preparation commands,
exactly one recall entry per action, and the immutable meaning of direct
submissions. Both competing packets remain includable. The native action
protocol's application cache is proved empty at every legal initialized history.
The initial-play command-service capstones do not yet cover this native game;
its source-policy compiler and continuation correspondence remain open.

## Interpretation

The native theorem concerns decoded terminal source states. Missing native
outcomes remain an explicit `Option` case. Utilities or observations of network
traffic, latency, fees, receipts, or other runtime-only data require an
additional correspondence contract.

The commitment service is ideal. Authentication, opaque commitment behavior,
relative deadlines, reserved inclusion, and a fixed finite epoch protocol are
part of the proved target model. Every epoch uses a publicly and adaptively
chosen permutation of all events, followed by one clock tick and expiry sweep;
`ServiceFeasible` requires every deadline to be at least two ticks. Wire and
order policies may adapt to public histories. This is not a generalized fair
network theorem, and the artifact establishes neither computational
cryptography nor an EVM/ledger implementation.

`Vegas.Language` is a surface-syntax prototype with an internal `SurfaceCore`
elaboration target. Its optional `Legal` predicate demands satisfiable guards;
`SourceProgram` instead admits unsatisfiable guards with failure-aware
resolution. Connecting the two requires an explicit semantic elaboration,
including deferred guard checks and publication results. The prototype has no
execution semantics and is outside the verified strategic tower.

`Paper.lean` is a self-contained capstone audit. Its statements delegate to
repository results and pin their proof dependencies; supporting lemmas remain
in their owning modules. The pins contain only `propext`, `Classical.choice`,
and `Quot.sound`. No library module or paper capstone contains a proof
admission.
The asynchronous graph compiler preserves and reflects same-error Nash at
compiled source profiles for utilities of the public source result, which is
what an outcome is. Its unilateral deviation witness is one source-policy
mixture chosen before private setup, and that deviation law is the stronger
statement, over decoded terminal source states. The graph-local scheduling theorem is separately audited.
The value-only source game also has a joint-law certificate for any fixed
reading of initial data paired with public results. Its audited Nash theorem
supports Bayesian utilities without retaining later private commitment choices.
Persistent private inputs carry ordinary values and no publication obligations.
The compiler preserves owner observations without generating commitment handles
or extra events. `Vegas.Examples.PrivateValueAuction` checks reporting under an
arbitrary finite joint valuation prior; `VegasTests.PrivateInputs` checks source
access restrictions and native resource absence. The design is documented in
[private inputs](docs/private-inputs.md).
Approximation is ex ante; no same-error interim or unrestricted native dominance
claim is implicit in it.
The asynchronous pending-message game has checked completion, full-source
honest outcome, exact unilateral-deviation mixture, and same-error Nash laws
under the concrete public epoch service. The finite source-policy mixture is
chosen before private setup, leaves every opponent unchanged, and covers any
native unilateral player policy. The public wire and adaptive order response
functions are jointly predrawn in the proof; they are not restricted to fixed
command traces.
Read the [active theorem map](docs/active-tower.md) for the
formal boundary and [event-pending deviation proof](docs/event-pending-deviation.md)
for the central adversarial argument.
