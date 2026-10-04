# Completing sequential-equilibrium preservation

The [checklist](se-proof-checklist.md) is the validation ledger. The
[stack](se-compilation-stack.md) states the games, utilities and backend
assumptions. The [asynchronous plan](se-schedule-generalization.md) records the
remaining general proof obligations. This plan orders the work needed to
integrate the explicit decision-packet semantics and finish preservation.

## Target and scope

Fix the program, initial law, service, observation rule, bounded response
interface, utilities and deposits before choosing a source equilibrium. Every
source sequential equilibrium must have a bounded raw-runtime sequential
equilibrium preserving the joint initial-parameter, public-result and realized
settlement law. Utilities depend on initial parameters and public results.

The fixed-calendar composition is
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean).
Its source-to-permitted edge is
[SourceServiceEquilibrium](../Vegas/Game/SourceServiceEquilibrium.lean); its
permitted-to-raw edge is
[SourceServiceRawExtension](../Vegas/Game/SourceServiceRawExtension.lean).
The explicit decision-packet composition passes the warning-strict project
build, including the complete calendar capstone and its standard-axiom pins.
Dependency evidence and repository validation are tracked by the checklist.
The arbitrary-builder theorem remains open.

## Calendar comparison chain

Every selected resolution sends a packet: evidence-free FALSE withholding or
an authentic effective TRUE opening. Silence is waiting. The calendar requires
an actual decision at the final owner visit for bindings and resolutions alike.
Every actor therefore needs an opportunity in its roster.

[SourceServiceSiteKind](../Vegas/Game/SourceServiceSiteKind.lean) classifies a
native information site from its event, owner, recall and recorded bit:

| Site | Comparison |
| --- | --- |
| Public sample | `sample_comparison_eq` |
| Foreign binding | `foreign_binding_comparison_eq` |
| Foreign disclosure | `foreign_disclosure_comparison_eq` |
| Recorded own binding | `recorded_comparison_eq` |
| Unsent own binding | `unsent_binding_comparisons` |
| Recorded own disclosure | `recorded_disclosure_comparison_eq` |
| Unsent own disclosure | `unsent_resolution_comparisons` |

The first four equality cases and recorded disclosure preserve the complete
continuation law under every legal local alternative. Unsent bindings and
resolutions simulate the alternative exactly through one common mixture of
original source assessment comparisons. Missing opening material restricts
which TRUE decisions are effective; FALSE remains an explicit decision.

[SourceServiceOwnerComparison](../Vegas/Game/SourceServiceOwnerComparison.lean)
transports those continuation identities to the original source assessment.
The source sequence is fully supported and Bayesian. Its disclosure
normalization is an execution device; no equilibrium of the normalized source
game is assumed. [SourceServicePrefixFactorization](../Vegas/Game/SourceServicePrefixFactorization.lean)
and [SourceServiceBayes](../Vegas/Game/SourceServiceBayes.lean) retain the actual
native input, including observations and own recall.

The source-to-permitted assembly uses the local simulation limit theorem with
exact comparisons and zero simulation error. Original source regret is handled
by that theorem's source-sequence argument. Initialized law preservation comes
from [SourceServiceTimedLaw](../Vegas/Game/SourceServiceTimedLaw.lean).
The complete calendar source-to-permitted statement and its comparison callers
pass strict checking for this model. S2–S5 and the raw-runtime repair edge are
checked; the complete calendar capstone passes the project build.

## Calendar continuation repair

Repair must supply one implementable continuation policy shared across all
hidden histories of the deviator's information site. The actual evaluator
coupling must preserve initial parameters and public outcomes or supply enough
additional collection to dominate the base-payoff gain.

The final required visit needs an actual silence branch: silence followed by
deadline expiry leaves a public decision-miss marker. Derive that marker from
the real expiry transition. An arbitrary state's lack of an accepted packet
does not imply a public miss. Optional-window coupling applies only where
silence remains in the retained menu.

The reactive service's application-side intention cache is empty along actual
initialized traces. Internal repair helpers needing this fact receive it from
their evaluator history. The nonreactive client runtime also uses explicit
private remember commands; its intentions must be reconstructed from actual
owner recall before that table can be removed. Do not add an oracle or a cache
hypothesis to the public capstone.
The send-time proof devices can be removed after the decision semantics and
callers are verified.

The concrete block kernels, program and active continuations, evaluator
coupling, settlement dominance, restriction extension and raw-alias lift all
pass strict checking for this model. R1–R4 and E1 are checked through their
complete statements, rather than conditional helpers.

## Arbitrary-builder proof

The generic service is [AsyncServiceSpec](../Vegas/Game/AsyncServiceSpec.lean).
The contract gives a timely owner opportunity, protected inclusion and complete
play; readiness starts the timer. The general retained menu keeps deferrals.
Late unrecorded opportunities and persistent owner risk open the bounded raw
continuation menu.

The [decision-commitment analysis](se-schedule-generalization.md#a-commitment-based-decision-protocol)
examines a compiler that freezes effective resolutions before mandatory
opening. [SourceSession](../Vegas/Pending/SourceSession.lean) implements opaque
admission, separate authenticated opening certificates, fresh opening timers,
and public-timeout cancellation. Its operational lemmas and
[native regression tests](../VegasTests/SourceSession.lean) establish the handler
boundary. Its packet-evidence instance supplies all-history capability
soundness through the existing generic framework. Its association-invariant
instance and `Vegas.SourceSession.history_opening_stored` identify authentic
pending original certificates with selected source binding values at every
initialized native history. `Vegas.SourceSession.history_source_invariant`
preserves the existing source-runtime invariant under arbitrary player responses,
passive leaks, rejected calls and scheduler commands. Binding and resolution
acceptance follow legal source transitions; cancellation retains a partial prefix
with valid readiness timestamps. The compiler's private-recall simulation,
phase service contract and conditional source/traffic law remain unproved.
[SourceSessionPolicy](../Vegas/Pending/SourceSessionPolicy.lean) supplies the native
source policy selector. It restores the whole own-action list before invoking the
rank-normalized graph policy, uses the existing binding fresh-slot selector, and
checks public deadlines with submission suppression scoped to each phase.
Owner-local prevalidation freezes the effective resolution result; the mandatory
opening reads that helper without another source draw. Private-intention recovery
uses the existing submission-origin lookup and checks the admission against its
actual owner view and fresh helper, rather than trusting arbitrary metadata.
Its local acceptance theorem
uses explicit phase authorization, timing, admitted-handle and fixed-value
premises. The native regression covers an original TRUE with a failed binding:
helper FALSE opens successfully while actual private recall restores TRUE.
The whole-service source-information relation remains open.
The [serial history projection](se-schedule-generalization.md#serial-history-projection-with-original-intention-recall)
gives its mathematical induction: replay original admitted actions, retain the
same typed store and cut, and identify restored own recall at every completion.
Its native formal statement must still connect actual receipts and lawful raw
representations to that replay.
The [serial finite-game argument](se-schedule-generalization.md#a-finite-game-argument-for-serial-phases)
derives a common completion-maximizing timing policy, source-posterior
factorization and rational free completion for an explicit opaque phase
interface with absorbing cancellation. It uses a public cancellation deduction
and a separate first-misconduct fine from one upfront escrow. Applying it to
the native runtime requires checking its raw-response classification, canonical
traffic and private recall, fresh protected phases, and actual conditional
watcher collection. It is a mathematical route, not a checked native capstone.
Its timing policy can depend on the builder at unprotected later opportunities;
the current policy's prompt behavior is preserved at protected first
opportunities, but its entire off-path policy is not proved optimal.
The serial route uses the public cancellation record for its timeout deduction
and immutable packet content or distinct-identifier pairs for misconduct;
the existing acceptance-based deadline audit cannot be reused wholesale.
The [raw-response audit](se-schedule-generalization.md#raw-response-audit-for-the-serial-argument)
classifies source actions, unexecutable decisions, private representation data
and signed departures against the actual interface. Lawful private
representations must have prescribed continuations, including representations
absent from the deterministic compiler's image. Watcher coverage is needed for
first witnesses created while gameplay runs, uniformly over later player
continuations; after sealing, a witness-free owner's fixed-payoff silence
comparison suffices. Pair offenses require joint witness coverage.
Public-timeout cancellation fixes the failure payoff before later gameplay or
watcher reports. The native
runtime proves that later source calls and samples cannot advance sealed
gameplay; source-suffix induction and the information-local timing channel
remain open. Replenishment is not established as necessary. The distinct native
watcher can report authentic observed envelopes through the same pending
runner, including source-player misuse of the report format. Its partial
collection bound, two-charge audit and actual report/settlement joint law remain
open; terminal resampling cannot replace an already emitted batch.

The [concurrent alternative](se-schedule-generalization.md#concurrent-alternative-one-fixed-cancellation-payoff-per-player)
uses a fixed cancellation deduction from every player, rather than only the
fault owner. This makes timing a common-interest binding-stage game: all
source types maximize stage completion probability. The mathematical selection
pins protected prompt play and maximizes completion over free timing agents;
barrier commutation supplies the successful source law. Its cost is charging
innocent players when another player causes cancellation. This alternative and
its native instantiation remain outside the checked theorem.

Use the [existing API map](module-architecture.md) for this proof. General
history induction, belief normalization, consistent subsequence extraction,
local-comparison limits and depth-free restriction extension already have
production implementations. The remaining work is to provide their premises
for the native application:

1. Align player types. `SourceSession.Principal` adds a neutral watcher;
   the source assessment needs an inactive-role lift. Player reindexing along
   an equivalence cannot discharge this addition, and Nash transport cannot
   replace sequential-equilibrium transport.
2. Adapt the event service contract to phases, including the full opening
   budget after actual admission and the reporting window after sealing.
   The event-wide sole-packet clause does not protect the honest two-packet
   resolution. `ReactiveAuthorizedService` filters builder inclusions and is
   not a proof for every builder satisfying the intended contract.
3. Derive source observation/private recall using the source-to-graph decoder
   and disclosure normalization. The existing bidirectional graph binding invariant is
   preserved by `SourceSession.bindingInvariant`; combined with packet
   evidence, `SourceSession.history_opening_stored` supplies the stored-value
   premise of `SourceSession.success_source_step`. The execution adapter
   `SourceSession.sourceServiceInvariant` combines authentic network evidence
   with the existing graph-runtime invariant, and
   `SourceSession.history_source_invariant` establishes semantic reachability
   and valid activation metadata at all initialized histories. Reuse these
   adapters instead of repeating their raw-history induction. Source-step
   correctness alone does not establish the compiler's information or strategy
   relation. `SourceSession.prescribedPolicy` selects the source decision
   or fixed opening from the genuine activation view, restores the chronological
   own-action list, and checks each phase separately. Its branch theorems identify
   the sampled admission law and deterministic opening. Prove exact restoration
   against the sampled source history, phase uniqueness at all prescribed
   histories, and protected-service discharge of the acceptance premises.
4. Connect actual watcher observation and delivery to the static misconduct
   audit. Reuse `EvidenceReportService.sample_coverage` for a genuine
   conditional observation/delivery law and the terminal-audit settlement
   interface for charges. A public cancellation deduction can be included in
   that interface's base payoff, provided its ownership and payoff law are
   proved; no separate general two-fine theorem is needed just to add such a
   deduction. Evaluate an already realized native report directly. Pair
   witnesses still require a joint observation bound. `EnforcementLimits`
   already characterizes finite-sanction feasibility through additional
   collection; prove the actual comparison coefficients before using that
   result or the finite rational deposit solver.
5. Prove the compiler-specific source/traffic fiber relation and one
   information-local timing selection. Reuse own-play reach cancellation and
   `GameTheory.Math.Probability.conditional_domination_converges_of_subset`
   once their actual reach and relative-error hypotheses hold. Initialized
   total-variation control alone does not supply those hypotheses at rare
   information values.
6. Supply the local gain comparisons to
   `GameTheory.Protocol.InformationModel.exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError`.
   Reuse `LocalizedEnforcement`, the unclocked restriction-extension results
   and private-alias transport for the raw extension. Their shared comparator
   and actual collection premises still need proofs; retained WAIT is not an
   excluded action that a sound misconduct audit can charge.

[SourceServiceRepeatedRepair](../Vegas/Game/SourceServiceRepeatedRepair.lean)
provides the full remaining execution coupling through repeated completed and
pending repair phases. It derives a genuine unusable-response seed, preserves
one retained implementation and fixed reference, and retains actual checkpoint
and subsequent tail laws at classified or signed-content exits. The next
comparison must use the same target assessment and actual settlement, including
earlier collection; per-offense coverage supplies no renewed deposit.
[SourceServiceRepeatedSettlement](../Vegas/Game/SourceServiceRepeatedSettlement.lean)
identifies the immutable parameter, public result and entire sampled payoff
vector on the final surviving-frame fiber. Its exact complementary laws retain
actual exit checkpoints and independent tails. Derive any complementary payoff
order using actual conditional collection and the same target continuation;
total per-offense coverage alone does not supply that order.
[SourceServiceRepeatedExitBound](../Vegas/Game/SourceServiceRepeatedExitBound.lean)
consumes the same initial-unusable coupling and bounds the original averaged
audited value on its final complementary fiber by the base-payoff minimum.
Actual persisted evidence supplies total collection; the sampled verdict need
not be certain. The retained-side value and net-charge comparison remain open.

The concrete private-resolution audit uses
[PrivateResolutionForkService](../Vegas/Examples/PrivateResolutionForkService.lean),
[PrivateResolutionForkNativeInputs](../Vegas/Examples/PrivateResolutionForkNativeInputs.lean)
and [PrivateResolutionForkClockPhase](../Vegas/Examples/PrivateResolutionForkClockPhase.lean).
The source equilibrium, initial type hiding and all-raw timing resources are
proved. [PrivateResolutionForkCompletionBounds](../Vegas/Examples/PrivateResolutionForkCompletionBounds.lean)
proves raw readiness, activation bounds and complete play;
[PrivateResolutionForkOpportunity](../Vegas/Examples/PrivateResolutionForkOpportunity.lean)
proves the owner-delay clause using actual public activation witnesses.
[PrivateResolutionForkProtectedInclusion](../Vegas/Examples/PrivateResolutionForkProtectedInclusion.lean)
proves protected sole-envelope receipts on every raw history and assembles the
full contract. [PrivateResolutionForkSpec](../Vegas/Examples/PrivateResolutionForkSpec.lean)
constructs the actual bounded service with finite nature and real initial
candidate coverage. [PrivateResolutionForkReceiptOrigin](../Vegas/Examples/PrivateResolutionForkReceiptOrigin.lean)
derives the exact ledger envelope and recorded submission behind Alice's
serial-zero accepting receipt. At Bob's turn it is Alice's first response or
her second response after literal WAIT. Exclude the first origin at the
delayed input and derive complete native Bayes likelihoods, then compare
whole native continuations. These obligations precede any timing counterexample
or conclusion about the general contract's sufficiency.

[AsyncServiceTrueGuessBayes](../Vegas/Game/AsyncServiceTrueGuessBayes.lean)
and [AsyncServiceWithholdingBayesBound](../Vegas/Game/AsyncServiceWithholdingBayesBound.lean)
give actual HIGH and LOW whole-continuation comparisons at native information
sites. TRUE support is derived from normalized source support and physical
guard success; its comparator has protected completion and zero authentic
charge. [PrivateResolutionForkTrueResource](../Vegas/Examples/PrivateResolutionForkTrueResource.lean)
derives that success for Bob from every initialized raw history. The values
retain actual counterfactual likelihoods.
[AsyncServiceGuessOptimality](../Vegas/Game/AsyncServiceGuessOptimality.lean)
relates the actual incumbent value to its LOW atom and derives the necessary
ordinary rationality inequality. The same convergent fully mixed Bayes sequence
with a rational pure LOW limit has a vanishing HIGH-versus-LOW mass gap, from
actual choice convergence and uniform whole-policy regret.
[PrivateResolutionForkGuessPayoff](../Vegas/Examples/PrivateResolutionForkGuessPayoff.lean)
identifies its fixed terminal payoff and rationality with Bob's real public
utility. Derive incoming native fiber likelihoods before drawing a rate or
preservation conclusion; no source posterior is a
premise. [PrivateResolutionForkNormalizedBob](../Vegas/Examples/PrivateResolutionForkNormalizedBob.lean)
derives the original normalized Bob lottery and its LOW source limit.
[PrivateResolutionForkBobObservation](../Vegas/Examples/PrivateResolutionForkBobObservation.lean)
derives its actual decoder and empty own source history from initialized raw
reachability, Bob readiness and Alice's real successful output.
[PrivateResolutionForkBobPinLimit](../Vegas/Examples/PrivateResolutionForkBobPinLimit.lean)
uses the same source sequence and native pin fields to force the prescribed
native LOW limit. [PrivateResolutionForkConcreteBobLimit](../Vegas/Examples/PrivateResolutionForkConcreteBobLimit.lean)
applies it to the actual admitted service, deriving all local decoder, recall,
turn and LOW-choice availability resources internally from the real trace.
Incoming likelihoods and ordinary target rationality remain separate.

[SourceServiceFirstActivation](../Vegas/Game/SourceServiceFirstActivation.lean)
derives the first ready owner input from an actual untouched completion
boundary. The contract horizon bounds its stopping time, the source
configuration is unchanged, and the input has protected inclusion. Its recall
readout integrates the actual response lottery after the same passive sample.
[SourceServiceFirstActivationFactorization](../Vegas/Game/SourceServiceFirstActivationFactorization.lean)
preserves a prior source-view/full-traffic factorization through the entire
binding or resolution wait to that input, with total mass on real inputs at
every supported prior view. The initialized pure-first-turn assembly below
supplies its actual prior; perturbed timing remains separate.

[SourceServiceFirstTurnCompletes](../Vegas/Game/SourceServiceFirstTurnCompletes.lean)
identifies the whole next-prefix law of the local first-turn completion phase
with the source behavioral step, before applying the source continuation.
[SourceServiceFirstTurnPrefix](../Vegas/Game/SourceServiceFirstTurnPrefix.lean)
derives this law for the actual global first-turn policy.
[SourceServiceFirstTurnRanks](../Vegas/Game/SourceServiceFirstTurnRanks.lean)
composes actual rank stops and derives the initialized effective source
prefix law at every rank, including correlated initial parameters. Its
evaluator composition uses ordered stopping predicates within the same
actual horizon.
[SourceServiceFirstTurnInformation](../Vegas/Game/SourceServiceFirstTurnInformation.lean)
derives whole effective source-view equality from equal current physical
observations at two actual first-turn rank endpoints. Initial draws may
differ; successful decoders and source checkpoints are derived from their
actual initialized support. Original erased intentions remain separate.
[SourceServiceOriginalPrefix](../Vegas/Game/SourceServiceOriginalPrefix.lean)
restores all owners' original private histories through one common memory
lottery after that actual decoder. It derives the complete original source
prefix law, jointly retaining the initial parameter, without another
effectiveness premise. This auxiliary carrier does not supply physical
native recall or a conditional information posterior.
[SourceServiceOriginalPrefixRetraction](../Vegas/Game/SourceServiceOriginalPrefixRetraction.lean)
derives actual source support and proves every restoration draw compresses
back to the same native decoder. The joint law retains the unchanged full
traffic and physical own input; no factorization is assumed.
[SourceServiceFirstBindingTraffic](../Vegas/Game/SourceServiceFirstBindingTraffic.lean)
joins the actual first-turn binding draw and whole source successor with the
same stopped full traffic. Its fixed-draw coupling carries an
original/effective successor pair from the prior source-view/traffic law.
The pure-first-turn whole-prefix induction is assembled below.
[SourceServiceFirstResolutionTraffic](../Vegas/Game/SourceServiceFirstResolutionTraffic.lean)
joins the global first-turn resolution draw, whole next-prefix decoder and
same full stopped traffic. Effective disclosures derive supported TRUE
realizability, and actual accepted completion supplies endpoint decoding.
[SourceServiceFirstResolutionCoupling](../Vegas/Game/SourceServiceFirstResolutionCoupling.lean)
couples traffic through the untouched wait, actual first protected response
and completion stop. Its prior pair-view/traffic induction hypothesis yields
original/effective successors with the same actual stopped traffic. Trace,
protection, fresh-slot and conforming-call resources are derived internally.
The whole-view consumer and rank induction below join the actual effective
source selection. Restoring original histories uses the common lottery.
[SourceServiceFirstActivationResources](../Vegas/Game/SourceServiceFirstActivationResources.lean)
derives first-input trace, protection, fresh-slot and conformance facts for
both owned decision kinds. The binding proof consumes them, and the actual
resolution dispatch coupling is separated from its scheduler lottery in
[SourceServiceResolutionPhaseTraffic](../Vegas/Game/SourceServiceResolutionPhaseTraffic.lean).
These provide the resources for the preceding resolution coupling.
[SourceServiceSampleCompletion](../Vegas/Game/SourceServiceSampleCompletion.lean)
derives the actual stopped sample/configuration law for any timing from its
initialized boundary and complete play. The real one-round sample traffic
coupling is checked separately.
[SourceServiceStoppedSampleTraffic](../Vegas/Game/SourceServiceStoppedSampleTraffic.lean)
carries it through the whole stopped run, retaining the same public value
and full traffic.
[SourceServiceStoppedSampleFactorization](../Vegas/Game/SourceServiceStoppedSampleFactorization.lean)
joins both carried source successors and an unchanged parameter with the same
actual draw and traffic,
deriving the sample marginal from the boundary and complete play. These
These local phase laws support the pure-first-turn induction below; native
belief transport remains separate.
[SourceServiceInitialTraffic](../Vegas/Game/SourceServiceInitialTraffic.lean)
supplies the actual initialized parameter/source/full-traffic factor through
the whole source view, without an independence assumption on private types.
Actual source residuals also retain the forward view map needed to restrict
whole-source traffic kernels to their typed tails.
[SourceServiceFirstTurnSampleFactorization](../Vegas/Game/SourceServiceFirstTurnSampleFactorization.lean)
propagates the prior whole-source-view factor through a fixed aligned sample
slice and the real stopped sample run. It derives the whole next-prefix
decoder and behavioral-step law, retaining the same parameter and traffic.
[SourceServiceFirstTurnBindingFactorization](../Vegas/Game/SourceServiceFirstTurnBindingFactorization.lean)
does the same for commitments, deriving the real compiler choice, protected
first-turn mixture and endpoint decoder before reusing the fixed-draw traffic
factor. [SourceServiceFirstTurnSharedCheckpoint](../Vegas/Game/SourceServiceFirstTurnSharedCheckpoint.lean)
derives typed checkpoints in one fixed aligned slice at every initialized
rank endpoint. Its state and action history come from the actual store and
completion history; no endpoint or likelihood promise is supplied.
[SourceServiceFirstTurnResolutionFactorization](../Vegas/Game/SourceServiceFirstTurnResolutionFactorization.lean)
supplies the whole-view resolution step. Static tail effectiveness derives
the supported normalization identity and realizable opening; actual canonical
choices, protected completion and checkpoint decoding supply the whole source
successor. The same parameter and traffic are retained through the existing
resolution factor.
[SourceServiceFirstTurnRankFactorization](../Vegas/Game/SourceServiceFirstTurnRankFactorization.lean)
composes these actual phases at every initialized pure-first-turn rank. Its
joint law is the true whole source behavioral iteration with the same initial
parameter and full stopped traffic. The channel reads only the whole effective
source observation. Neither a source marginal nor an endpoint or likelihood
equation is a premise.
[SourceServiceOriginalRankTraffic](../Vegas/Game/SourceServiceOriginalRankTraffic.lean)
then derives the true original source-prefix/full-traffic law through the same
all-owner restoration draw, retaining the initial parameter. Its channel reads
only the compressed original focal observation.
[SourceServiceOriginalFirstInput](../Vegas/Game/SourceServiceOriginalFirstInput.lean)
propagates this law to the actual first ready binding or resolution owner
input, before the response. The channel is total on real inputs at every
supported original source prefix. Physical private recall is retained; the
restored histories remain auxiliary source data.
[SourceServiceOriginalFirstInputPosterior](../Vegas/Game/SourceServiceOriginalFirstInputPosterior.lean)
derives recovery of the compressed source observation from actual typed cells
and completion history. Conditioning a supported input yields the true original
source-prefix/initial-parameter posterior on that compressed observation.
Uncompressed original intentions are not physically recovered. Identification
with native assessment history beliefs and nonpure timing remain separate.
[ReactivePassageBayes](../Interaction/ReactivePassageBayes.lean) expresses the
actual native state belief as terminal-history passage conditioned on reaching
the information site, using the unique earlier control rather than the final
control. [PassageBayes](../GameTheoryExtensions/Analysis/Protocol/PassageBayes.lean)
derives ancestor weights from real continuation cones and their true reach
probabilities. Its stochastic readout theorem carries the same original-memory
lottery through that genuine ancestor belief. No common decision depth or
stopped-history likelihood is a premise.
[SourceServiceFirstInputPassage](../Vegas/Game/SourceServiceFirstInputPassage.lean)
reads the chronological first event input from actual own recall and proves
that it records precisely passage through a first-event information site.
Later activations preserve this input. Its terminal passage mass is the actual
native information mass, with no common-depth assumption.
[AsyncServiceFirstInputPassage](../Vegas/Game/AsyncServiceFirstInputPassage.lean)
identifies the represented normalized first-turn profile's complete input law
with genuine initialization, rank stopping and first-activation stopping.
This identifies the input marginal; the joint ancestor restoration is supplied
by the terminal and native posterior laws below.
[SourceServiceInitialReadout](../Vegas/Game/SourceServiceInitialReadout.lean)
recovers the exact initial source environment from the existing persistent
graph inputs at every initialized descendant and legal native history.
Encoding injectivity makes this state unique, and terminal source readout
agrees with it. Correlated parameters can therefore use the same initial draw
in an ancestor carrier; the decoder adds no player observation.
[SourceServiceFirstInputSourceLaw](../Vegas/Game/SourceServiceFirstInputSourceLaw.lean)
identifies the actual stopped prefix restoration and input jointly, using that
same decoded initial draw and one common all-owner lottery.
[SourceServiceFirstInputReadoutPosterior](../Vegas/Game/SourceServiceFirstInputReadoutPosterior.lean)
derives the true original source posterior from each supported physical stopped
input.
[SourceServicePastPrefix](../Vegas/Game/SourceServicePastPrefix.lean) recovers the
before-rank source state from persistent fields and filtered completion history.
It agrees with the rank-seed decoder and is invariant under every legal native
continuation. Perturbed waiting needs its own posterior transport.
[SourceServiceFirstInputAncestor](../Vegas/Game/SourceServiceFirstInputAncestor.lean)
derives the real owned ancestor's prefix from its ready input alone and retains
the same source readout at every descendant. This supplies the operational
ancestor bridge without a cleanliness or fixed-depth assumption.
[SourceServiceFirstInputTerminalLaw](../Vegas/Game/SourceServiceFirstInputTerminalLaw.lean)
identifies the full represented terminal prefix-restoration/input joint with
the genuine initialized stopped law. The common restoration kernel survives
actual native continuations.
[SourceServiceFirstInputNativePosterior](../Vegas/Game/SourceServiceFirstInputNativePosterior.lean)
conditions the actual encountered ancestor of every positive-mass first owned
site. One recovery function and one common original-memory lottery give the
true original source-prefix/initial-parameter posterior on the compressed view.
The information antichain comes from native decision recall; no clean-history
or stopping-likelihood premise is supplied.
[AsyncServiceFirstTurnBeliefResources](../Vegas/Game/AsyncServiceFirstTurnBeliefResources.lean)
derives actual physical support and clear owner risk for each history in that
first-turn Bayes belief. These statements cover pure first-turn play; perturbed
waiting and sequential rationality remain open.

The actual binding-response law now composes with protected completion,
retaining the transmitting draw and full stopped traffic. The native Bayes
law cancels the complete focal owner's recalled-action likelihood, including
earlier waiting. Foreign deferral probabilities remain in counterfactual
reach. A conditional escape estimate must compare against that actual
denominator; a small unconditional escape probability alone is insufficient.
Public misses are excluded from every history at source-compatible native
information by the shared public record. Hidden private risk remains distinct.
[AsyncServiceForeignEscape](../Vegas/Game/AsyncServiceForeignEscape.lean)
proves that hidden escape is exactly foreign recalled submission or opportunity
risk. Full mixing reaches the classifier's actual clean witness, so its clean
counterfactual mass is positive. The conditional escape bound divides the sum
of foreign private-risk masses by that actual clean mass. Making this ratio
vanish under one coherent perturbation family remains open; positivity is not
an asymptotic lower bound.
[SourceServiceWaitRiskConfounding](../Vegas/Game/SourceServiceWaitRiskConfounding.lean)
checks a local runtime branch pair: with deadline three and inclusion bound
two, a second turn at clock zero is protected and a second turn at clock one
is timely but unprotected. The same typed successful commitment is accepted
at clock one on both paths; the next player's full input agrees, while the
sender's private opportunity-risk recall differs. A separate geometric path
law gives both late paths the same weight and conditional risk one half.
This calculation does not identify an initialized native Bayes law or certify
an all-history service contract. It shows why acceptance and private risk
must be distinguished when choosing the probability event to control.
[OpaqueBindingForkService](../Vegas/Examples/OpaqueBindingForkService.lean)
certifies a compiled two-player builder against the service contract at every
RAW history. After Alice waits, it fairly orders a tick and her second turn;
the protected clock-zero call and unprotected clock-one call are both accepted
at clock one.
[OpaqueBindingForkSites](../Vegas/Examples/OpaqueBindingForkSites.lean) derives
an initialized clear source witness and the same full Bob input on the privately
risky branch.
[OpaqueBindingForkImmediate](../Vegas/Examples/OpaqueBindingForkImmediate.lean)
proves that immediate acceptance instead exposes activation time zero, so its
Bob input differs from the delayed branches' activation time one.
[OpaqueBindingForkVanishingWait](../Vegas/Examples/OpaqueBindingForkVanishingWait.lean)
uses one globally admitted local policy with initial WAIT weight alpha. Its
actual initialized four-branch law gives the delayed Bob input mass alpha and
conditional private risk one half for every positive alpha. This certifies the
rare-fiber limitation of an unconditional convergence estimate. It does not
prove the behavior of rational free completion, source-payoff distortion or
failure of SE preservation.
[OpaqueBindingForkSourcePosterior](../Vegas/Examples/OpaqueBindingForkSourcePosterior.lean)
proves that the actual conditional typed configuration is the clean witness's
configuration. Both physical decoders succeed, and the common original-memory
lottery retains exactly the same initial parameter and source-prefix law.
Surviving private risk therefore does not distort this fixture's projected
source-prefix belief. Future free-policy choices and payoffs remain separate.

For waiting comparisons, a late canonical packet can still be accepted before
expiry without a charge, so the accepted branch needs source-continuation
control as well as the miss branch's real collection bound.
Protected binding completion also identifies the actual whole-program source
prefix and behavioral step through its derived residual. The pure-first-turn
original-memory/input law above does not supply conditional assessment
transport for perturbed waiting or late decisions.
Supported original resolution intentions now have exact protected packet
completion and typed-state agreement, with effective history kept distinct.
Their joint response law also composes with the actual stopping kernel,
retaining full traffic and the current owner's restored intention. Residual
source-view recovery is derived from the actual source constructors, and one
static decoder slice supplies a compiler-aligned typed tail, embedding,
reference-order certificate, lift and recovery shared across the prior.
The same recursion inherits effective disclosures from the whole profile.
The binding and resolution phase factors retain an unchanged parameter beside
both source successors and the same actual stopped traffic.
[DisclosureProfilePrefix](../Vegas/Game/DisclosureProfilePrefix.lean) composes
all owners' real memory kernels to recover the complete original source law
at every normalized source prefix. The initialized native rank carrier has
that original law with the actual traffic channel and first owner input;
conditional-prefix transport to native beliefs remains open.
The actual restoration also retracts to the same effective state on support,
and its view compression transports an effective source-view channel through
the common original-memory lottery. Waiting in the binding prefix law uses
the real decoder's unfinished result, derived from the unwritten ready field.
[DisclosureProfileJointChannel](../Vegas/Game/DisclosureProfileJointChannel.lean)
retains correlated initial parameters in that same original-state and channel
law. The pure-first-turn original rank theorem identifies that channel with
the actual native traffic; perturbed timing still needs its own law.
A single timely canonical transmission followed by owner silence also has an
actual accepted-action/public-miss dichotomy outside the protected window.
[SourceServiceLateDecisionCompletion](../Vegas/Game/SourceServiceLateDecisionCompletion.lean)
proves it on initialized raw histories, without a response-menu premise.
Its acceptance law can depend on the builder and the public packet content;
the dichotomy alone does not bound the value of waiting.
[SourceServiceLateTurnCompletion](../Vegas/Game/SourceServiceLateTurnCompletion.lean)
carries that dichotomy through the actual turn-counted continuation policy.
The real recorded call makes this event's completion-stopped law silent;
the owner's policy at later events remains available. This bridge requires
neither protected delivery nor a chosen acceptance probability, and supplies
no strategic upper comparison.
[LateResolutionService](../Vegas/Examples/LateResolutionService.lean)
proves all three service clauses over every raw history of a concrete compiled
resolution. Its public scheduler includes only FALSE at the second timely
opportunity and expires the event when the late inclusion bound ends. Its
actual audited payoff comparison is proved in
[LateResolutionContinuation](../Vegas/Examples/LateResolutionContinuation.lean).
At a reachable initialized late turn, TRUE and silence incur the public miss
and payoff `−D`, while accepted FALSE yields `0` under every authentic partial
audit. The current turn policy is silent there for every timing lottery
because its protected gate is closed. This requires rational free completion.
[LateResolutionSourceEquilibrium](../Vegas/Examples/LateResolutionSourceEquilibrium.lean)
constructs a genuine consistent source SE with strategy TRUE for the declared
payoff, classifying actual source histories and deriving source finiteness and
full mixing.
[LateResolutionNativeSite](../Vegas/Examples/LateResolutionNativeSite.lean)
reaches the actual bounded risk menu's late decision information site, proves
FALSE is a legal choice at that same input, and gives its strict physical
continuation improvement over the current policy. The actual initialized
geometric policy reaches such a site for every positive deferral weight below
one and every source profile, when later timing slots exist. This reach is for
the physical policy; its finite-menu representation needs whole-law coverage.
[LateResolutionNativeInformation](../Vegas/Examples/LateResolutionNativeInformation.lean)
derives the same late clock, readiness, activation time, remaining commands
and entire empty network at every actual history sharing the witness input.
Actual recall, response provenance and serial invariants supply these facts,
without a belief equation.
[LateResolutionNativeContinuation](../Vegas/Examples/LateResolutionNativeContinuation.lean)
identifies the actual native terminal-state law with its current response
draw followed by the four physical passive commands. Every future player
policy has the same suffix law.
[LateResolutionNativeRationality](../Vegas/Examples/LateResolutionNativeRationality.lean)
proves WAIT has value `−D` and legal FALSE has value `0` under every native
assessment belief at this site. For `D > 0`, the finite-menu representation
of the entire current turn policy fails sequential rationality for any timing
lottery, including pure first-turn timing. Actual consistent native beliefs
exist but cannot remove this regret. Preservation remains possible through
rational free continuation at late inputs.
[LateResolutionNativePerturbation](../Vegas/Examples/LateResolutionNativePerturbation.lean)
uses the actual fully mixed native Bayes assessment. Its late conditional
regret is at least `(1 − ε)D − ε`, and eventually at least `D/2` at one fixed
site as trembles vanish, even with varying source and timing approximants.
Every history in that site's actual fiber has positive native probability.
This certifies the need for free late completion, not a failure of preservation.
[LateResolutionFreeLate](../Vegas/Examples/LateResolutionFreeLate.lean)
proves every raw response at that entire late fiber has typed failure and
audited value at most zero for a nonnegative deposit. Legal FALSE attains
zero and is locally optimal under any beliefs. A whole native equilibrium
still needs rationality at the other sites.
[LateResolutionFirstActivation](../Vegas/Examples/LateResolutionFirstActivation.lean)
derives the actual deterministic first native input under every profile and
identifies its entire information fiber. Its clear menu contains only WAIT
or canonical FALSE/TRUE; TRUE availability requires actual message bounds
coverage.
[LateResolutionFirstDecision](../Vegas/Examples/LateResolutionFirstDecision.lean)
proves actual first FALSE/TRUE acceptance and the forced silent completed
second menu. [LateResolutionNativeSites](../Vegas/Examples/LateResolutionNativeSites.lean)
exhaustively classifies all initialized native decision sites as first, late
unrecorded, or late completed.
[LateResolutionFirstPayoff](../Vegas/Examples/LateResolutionFirstPayoff.lean)
derives the accepted first decision's full typed source readout and zero
authentic partial-audit charge.
[LateResolutionFirstOptimality](../Vegas/Examples/LateResolutionFirstOptimality.lean)
proves TRUE optimal at the entire protected first fiber and forced silence
optimal at both completed second fibers, under any beliefs.
[LateResolutionFreeEquilibrium](../Vegas/Examples/LateResolutionFreeEquilibrium.lean)
constructs a native risk-menu SE: TRUE first, FALSE late after WAIT, forced
silence after completion. Its initialized joint full typed readout and actual
realized settlement vector equal those of the source opening equilibrium,
under any authentic partial sampler and nonnegative deposit. The concrete
larger-menu extension below supplies rational completion; arbitrary-service
source preservation remains open.
[LateResolutionPreservation](../Vegas/Examples/LateResolutionPreservation.lean)
preserves EVERY source SE of this concrete fixture in the native risk menu,
including the same full typed terminal state and realized settlement vector.
Actual source rationality derives its TRUE law.
[LateResolutionEffectiveExtension](../Vegas/Examples/LateResolutionEffectiveExtension.lean)
bounds every effective continuation at each retained history by an actual clean
retained continuation: TRUE first, FALSE after an unrecorded deferral, silence
after completion. This extends every audited risk-menu SE to the full effective
menu with the same complete terminal control law.
[LateResolutionRawPreservation](../Vegas/Examples/LateResolutionRawPreservation.lean)
then preserves EVERY original source SE of this fixture in the full bounded raw
runtime, with the same joint typed terminal state and realized sampled-settlement
vector. It uses authentic partial observation and a nonnegative deposit, without
a detection bound. This is a concrete service; arbitrary-service preservation
remains open.
[ReactiveCompletedConfig](../Vegas/Pending/ReactiveCompletedConfig.lean)
proves arbitrary raw submissions and environment commands preserve the entire
graph configuration once all events complete. Further traffic and charges
remain possible.

The [late-decision signaling probe](../scripts/experiments/late_decision_signaling_probe.py)
checks this distinction with exact Bayes limits and every whole-policy
comparison. Equal waiting trembles make waiting profitable for one type;
view-dependent waiting trembles yield a rational preserving limit in that
finite tree. The general construction must choose one consistent family
across all native information sets and account for its timing likelihoods.

Continue in this order:

1. Use the actual protected/miss joint laws in the waiting comparisons; the
   literal timing policy alone does not identify rational free continuation.
2. Choose one common information-dependent waiting family with independent
   prescribed and free tremble rates. Derive conditional likelihood estimates
   or payoff comparisons for surviving foreign-risk histories at every site;
   initialized loss and clean-prefix equality do not settle these obligations.
3. Compare protected decisions, waiting, late first attempts and departures
   under the actual audited utility.
4. Use the original-sequence free-site completion in those comparisons,
   including after collection of the one-time deposit has become certain.
5. Complete the source-to-risk-menu equilibrium embedding, general continuation
   repair, effective-menu extension and raw-alias lift.
6. Compose the arbitrary-builder capstone and derive the calendar corollary.

[AsyncServicePrescribedCompletion](../Vegas/Game/AsyncServicePrescribedCompletion.lean)
constructs a consistent native assessment for each fixed admitted effective
source profile. It agrees with immediate decisions at source-compatible sites
and is rational at every free site under the actual audited utility. Its whole
initialized history law equals first-turn play, including the joint full typed
readout and sampled settlement vector. This is not yet an equilibrium: rationality
at prescribed sites remains open. Off-path normalization need not commute with
taking limits; the varying-source construction below retains its actual pin limits.

[AsyncServiceInitializedDomination](../Vegas/Game/AsyncServiceInitializedDomination.lean)
compares the actual uniformly perturbed geometric pins, with arbitrary free
continuation, to first-turn play of the same effective profile. Every initialized
history keeps at least `((1 - δ)(1 - ε))^(card Player * fuel)` of its first-turn
mass. The corresponding total variation loss vanishes uniformly in the source
profile and free continuation. This permits varying original source approximants
without assuming convergence of off-path normalization. It does not control
beliefs conditioned on rare inputs or select incentive-compatible waiting rates.

[AsyncServiceCompatibleWait](../Vegas/Game/AsyncServiceCompatibleWait.lean)
derives exact geometric WAIT probability at every actual source-compatible input:
`ε` for geometric play, and `δ * uniformWait + (1 - δ) * w(who, info)`
for the actual information-dependent native pin.
The input's real bounded execution excludes a final truncated turn. These
likelihoods remain relevant for foreign players' conditional beliefs.
[AsyncServiceInformationWait](../Vegas/Game/AsyncServiceInformationWait.lean)
allows WAIT rates to depend on the owner's complete actual information, with
uniform trembles and arbitrary completion outside compatible sites.
[AsyncServiceInformationWaitDomination](../Vegas/Game/AsyncServiceInformationWaitDomination.lean)
uses the shared initialized induction to retain at least
`((1 - δ)(1 - b))^(card Player * fuel)` of first-turn mass when `b` bounds local
WAIT rates at compatible sites. This controls initialized loss, without choosing
rates that give source-relative beliefs or rational prescribed decisions.

[SourceServiceClearAudit](../Vegas/Game/SourceServiceClearAudit.lean)
derives absence of owner misses and zero current audited charge at a legal
risk-menu prefix with the owner's persistent risk clear, using authentic partial
sampling only. At source-compatible information, actual own recall, public state
and receipts transfer this current verdict to every initialized RAW history
with that input. Its information-fiber consumer applies to any actual response
menu, including the full effective game, without requiring original risk-menu
support or restricting foreign deviations. This gives no future zero-charge
claim; unfinished current verdicts can change.

[SourceServiceCompatibleImmediateAudit](../Vegas/Game/SourceServiceCompatibleImmediateAudit.lean)
derives the actual owner's packet and slot resources from compatible information
at every initialized raw prefix. After its immediate response, arbitrary foreign
raw policies preserve owner clarity and zero terminal collection under authentic
partial sampling. The physical policy uses one whole continuation across hidden
histories. [SourceServiceEffectiveImmediateComparator](../Vegas/Game/SourceServiceEffectiveImmediateComparator.lean)
represents that same whole policy in the complete effective game. Actual local
owner slots and bounded records derive admission along its supported suffix;
one shared generic restriction induction gives the exact physical terminal law
from any actual control with these owner resources, including an idle control
after a committed response.
Every hidden history at a compatible effective input has zero owner collection
against arbitrary effective opponents. Source payoff comparisons remain open.
[SourceServiceAuditableCollection](../Vegas/Game/SourceServiceAuditableCollection.lean)
and [SourceServiceRecordedCollection](../Vegas/Game/SourceServiceRecordedCollection.lean)
derive the backend's total collection bound for a classified forbidden packet or
repeated submission at any native information in any response menu.
[ReactiveRecalledEmission](../Vegas/Pending/ReactiveRecalledEmission.lean)
derives authentic own calls from raw recall, including late or rejected calls;
actual serial provenance distinguishes the two emitted identifiers. No
historical deadline-fit or original risk-menu trace is required.
Later behavioral policies are arbitrary. This bounds the existing one-time
charge, without assuming certain evidence observation or renewed punishment.
[SourceServiceCompatibleChargedComparison](../Vegas/Game/SourceServiceCompatibleChargedComparison.lean)
compares a committed classified forbidden packet or replay with that same clean
whole-policy comparator. Actual collection and the fixed effective-history
range deposit give the audited-utility inequality under every belief at a
compatible effective site and arbitrary future policies. Its total-charge and
base-range lower bound applies at any native input; the comparator and
same-assessment comparisons keep their actual compatibility premise. No risk-profile
extension or future risk support is assumed. Dominance by the prescribed source
response, uncharged unusable choices and SE preservation remain open.

[AsyncServiceCompatibleRecall](../Vegas/Game/AsyncServiceCompatibleRecall.lean)
derives source compatibility of every earlier own recalled decision at a
compatible input. Agreement on compatible inputs therefore fixes the owner's
entire recalled likelihood, independently of completion elsewhere. Existing
counterfactual Bayes cancellation applies even to arbitrarily rare own WAITs;
foreign WAIT likelihoods and conditional escape remain separate obligations.

[AsyncServiceOriginalCompletion](../Vegas/Game/AsyncServiceOriginalCompletion.lean)
derives a complete supported source Bayes sequence from the original
assessment's consistency proof. Full abstract-choice support and normalized
effective-choice support are retained. That source sequence precedes the
choice of waiting and tremble rates; every admissible rate and selection-bonus
family supplies a fully mixed native Bayes sequence and one common convergent
strategy/belief subsequence.
Its consistent limit is rational at all free sites, initialized play visits only
source-compatible sites, and the joint full typed outcome and realized sampled
settlement law equal the original source strategy's law. Its WAIT rates depend
on actual information and have a common vanishing upper bound at compatible
sites. The pins retain actual normalized approximants, including their off-path
limits. This does not identify native conditional beliefs with source beliefs
or prove prescribed-site rationality. Choosing waiting rates that support those comparisons remains open.
Prescribed uniform trembles and free-agent reference trembles have independent
vanishing rates; initialized loss depends only on the prescribed rate.

[ReactiveBindingPublicTraffic](../Vegas/Pending/ReactiveBindingPublicTraffic.lean)
proves joint equality of the network, receipts, public scheduler input and
recall, and every foreign player's input and recall while private binding
values differ. Canonical binding transmission, arbitrary foreign raw
responses and every pending inclusion at a sole-ready binding preserve this
joint readout. Its public coordinate is explicit even in a one-player game.
[ReactiveBindingPublicRounds](../Vegas/Pending/ReactiveBindingPublicRounds.lean)
extends this readout equality through actual scheduler rounds, including a
common partial observation draw, every command and arbitrary foreign raw
policies. Only the binding owner is replaced by physical silence.
[SourceServiceBindingSelection](../Vegas/Game/SourceServiceBindingSelection.lean)
derives that replacement from actual recorded turn policy for any timing and
proves the full completion-stopped joint law. Changing the canonical binding's
private value preserves public selection, misses and all foreign inputs with
the same correlated prefix parameter. Horizon exhaustion is retained. A
manual first-call acceptance/public-miss decomposition uses the actual
unique-call prefix resources below; the strategic waiting comparison remains open.
[SourceServiceBindingChoiceSelection](../Vegas/Game/SourceServiceBindingChoiceSelection.lean)
joins the actual sampled source commitment value to this selection law,
conditionally on the same physical prefix and correlated initial parameter.
The reference failure packet is a physical proof experiment, not an assumed
admitted source action. No acceptance probability is supplied.
[SourceServiceBindingFirstPacket](../Vegas/Game/SourceServiceBindingFirstPacket.lean)
derives absence of prior owner packets naming an unrecorded event from actual
initialized recall and provenance. After a manual canonical first call, every
such owner packet throughout the stopped recorded-policy run is its exact
envelope, including identifier and readiness token. Foreign raw policies are
arbitrary. [ReactiveBindingAcceptanceReceipts](../Vegas/Pending/ReactiveBindingAcceptanceReceipts.lean)
derives the reverse receipt resource on every initialized raw history: each
accepted event handle has an actual owner-authored ledger commitment with
its accepting receipt.
[SourceServiceBindingAttemptCompletion](../Vegas/Game/SourceServiceBindingAttemptCompletion.lean)
composes these resources at an initialized raw binding prefix with a fresh
counted candidate. Every endpoint of a manual timely canonical attempt completes
with either this identifier's accepting receipt, no miss and the exact chosen
typed successor,
or its actual public miss, no accepting receipt for this identifier and typed
failure. Complete play and uniqueness are derived. Selected-input resources
derive freshness from the actual trace, without global risk clarity. The
subsequent owner follows any recorded timing policy; foreign raw policies are
arbitrary.
The call need not be protected or supported by that timing policy.
[SourceServiceBindingAttemptLaw](../Vegas/Game/SourceServiceBindingAttemptLaw.lean)
joins the actual residual source commitment draw, typed binding output and
same public/foreign traffic, retaining the prefix parameter. The real
failure-reference selection kernel's accepting receipt for this identifier
selects the drawn value; absent acceptance selects typed failure with a real
miss.
[SourceServiceBindingNoAttempt](../Vegas/Game/SourceServiceBindingNoAttempt.lean)
derives the other branch at an actual initialized unrecorded binding with
closed protection. Activation remains fixed while the clock increases, so
protection cannot reopen. Every timing lottery is silent until actual
completion; complete play gives a public miss, typed failure and no owner
packet naming the event anywhere in the network. Foreign raw policies are
arbitrary. The waiting incentive comparison remains open.
[SourceServiceTimingMixture](../Vegas/Game/SourceServiceTimingMixture.lean)
identifies the whole completion-stopped strategic execution from an untouched
boundary with the original finite timing prior over real owner-only turn
family runs. Private recall and all traffic stay joint; binding and resolution
consumers retain the same prefix parameter. The prior is derived from actual untouched
recall; no posterior or acceptance law is supplied. Selected turns can be
absent or lose protection, and finite-budget exhaustion remains represented.

[SourceServiceBindingSelectedInput](../Vegas/Game/SourceServiceBindingSelectedInput.lean)
derives the actual chronological selected input and supported canonical
response, or completion before it with no owner event packet, a public miss
and typed failure. No selected-slot visit or source admission is assumed.
[SourceServiceBindingStoppedResponse](../Vegas/Game/SourceServiceBindingStoppedResponse.lean)
decomposes an actual protected geometric response and its full completion
continuation into real waiting and receipt-driven source commitment selection.
Earlier deferrals remain in the original input; waiting can later attempt or
miss. The selected-family laws below supply actual source-choice factorization;
the strategic waiting comparison remains open.

[SourceServiceBindingSelectedAssembly](../Vegas/Game/SourceServiceBindingSelectedAssembly.lean)
composes the original timing prior, actual selected-input stop and real
completion into one joint law. Its physical marginal is the actual completed
binding law, retaining the same parameter and all public/foreign traffic. The
auxiliary input is the original chronological before-response recall; no
selected-slot visit or acceptance mass is assumed.
[ReactiveBindingCommitmentProvenance](../Vegas/Pending/ReactiveBindingCommitmentProvenance.lean)
preserves actual owner commitments that address completed events, use a
publicly associated handle or have matching fixed candidate meanings, across
foreign/noncommitment responses, shared fresh registration and all environment
commands. This
supplies the traffic resource needed to allow further owner commitments in
continuation repair. The stopped coupling composes later fresh usable bindings.
[SourceServiceBindingSelectedResources](../Vegas/Game/SourceServiceBindingSelectedResources.lean)
derives fresh counted candidates, actual owner turn/slot invariants and no
earlier owner packet at the real selected raw input. Its aligned source
configuration is unchanged; protection gives the actual source commitment
kernel, and a closed gate gives silence. Other owners may use raw actions.
[SourceServiceSelectedReference](../Vegas/Game/SourceServiceSelectedReference.lean)
derives the actual selected before-response input, raw trace, unchanged source
configuration and recalled turn resources for either strategic event kind.
Absence of a selected input gives actual completion, a public miss and no owner
packet. [ReactiveResolutionMiss](../Vegas/Pending/ReactiveResolutionMiss.lean)
derives immutable typed publication failure from that real miss marker on every
initialized raw history.
[SourceServiceResolutionSelectedCompletionLaw](../Vegas/Game/SourceServiceResolutionSelectedCompletionLaw.lean)
joins the original timing prior to the actual resolution input and completion.
Protected FALSE/TRUE draws use their own full traffic kernels; closed hits and
absent selection give actual misses and typed failure.
[SourceServiceResolutionProtectedCompletion](../Vegas/Game/SourceServiceResolutionProtectedCompletion.lean)
derives acceptance from compiler-aligned effective disclosures through the
shared [physical completion](../Vegas/Game/SourceServiceProtectedDecisionCompletion.lean).
These operational laws do not establish waiting incentives.
[SourceServiceBindingSelectedReference](../Vegas/Game/SourceServiceBindingSelectedReference.lean)
derives the silent reference's actual selected before-response input, initialized
raw trace, unchanged source configuration, fresh slot and original commitment
lottery. It needs an actual completion boundary and horizon bound, without an
assumed selected visit or global risk clarity.
[SourceServiceSelectedResponse](../Vegas/Game/SourceServiceSelectedResponse.lean)
proves the exact stopped execution law by replacing the actual silent reference
response with the original selected input's canonical lottery. Its last recall
entry recovers that same before-response execution; no response is redrawn from
support or assigned an assumed selection probability.
[SourceServiceSelectedContinuation](../Vegas/Game/SourceServiceSelectedContinuation.lean)
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
joins the original timing prior to that same actual reference prefix. Protected
hits use the original source lottery and actual accepted typed outcome; closed
hits and completion before selection use real misses and typed failure. The
joint law retains the selected input, prefix parameter and all public/foreign
traffic. This is the literal policy's operational decomposition; its closed
silence does not establish rational free continuation.
[SourceServiceBindingSelectedClosedCompletion](../Vegas/Game/SourceServiceBindingSelectedClosedCompletion.lean)
derives the real public miss, typed failure and absence of owner packets after
the literal family's selected closed-gate silence. These physical laws do not
supply the rational free continuation or its conditional incentive comparisons.

The watcher samples authentic evidence partially; observation and report
delivery may be correlated. Positive conditional coverage and a finite
challenge window are backend obligations. A concrete pending-message reporting
implementation must establish them. Public misses and packet collection are
separate mechanisms.

[SourceServiceAuthorizationBreach](../Vegas/Game/SourceServiceAuthorizationBreach.lean)
derives rejection of actual emitted invalid-token and foreign-actor packets
at every complete legal record. The information-local auditable classifier
uses it with the existing partial-evidence collection bound. This supplies
another checked deviation class without changing backend coverage; wrong
node kinds are covered separately by
[SourceServiceNodeKindBreach](../Vegas/Game/SourceServiceNodeKindBreach.lean)
through accepting-receipt constructor compatibility. Valid-token off-turn
calls are not automatically forbidden.
[SourceServiceCompletedPacket](../Vegas/Game/SourceServiceCompletedPacket.lean)
covers newly allocated packets addressed to already completed events and is
integrated into the same auditable collection comparison. Earlier accepted
envelopes remain permitted. Two submissions before completion require a
separate pair argument, since the builder may accept the newer packet.
[SourceServicePublicRejection](../Vegas/Game/SourceServicePublicRejection.lean)
shares the actual public rejection argument and derives forbiddenness for
wrong opening ownership or public binding association at a ready resolution.
Those classes are integrated into the same information-local collection bound.
Private binding capabilities retain their own repair obligations.

[SourceServiceDuplicatePackets](../Vegas/Game/SourceServiceDuplicatePackets.lean)
proves at least one of two distinct actual same-event envelopes is forbidden
at complete settlement. Existing partial coverage bounds total charge in
every arbitrary behavioral continuation, selecting a forbidden packet
pointwise at the final history. An actual raw prefix with authentic own calls
and a second same-event response reconstruct the real pair. Connecting that committed
local choice to the actual terminal evaluator is proved in
[SourceServiceRecordedCollection](../Vegas/Game/SourceServiceRecordedCollection.lean).
The risk extension classifies it directly from own recall and combines its
collection bound with the fixed clean comparator. The class therefore needs
no separate other-exclusion comparison hypothesis. The bound does not give
an incremental fine after an earlier charge.

[SourceServiceResolutionComplement](../Vegas/Game/SourceServiceResolutionComplement.lean)
derives the actual ready owned opportunity, unrecorded status and protection
from a minted token, clear risk and both classifier complements. At an owned
resolution, public checks and actual trace invariants then prove the bounded
effective response is retained. A fresh-envelope or acceptance promise is
not a premise.
[SourceServiceUnusableBinding](../Vegas/Game/SourceServiceUnusableBinding.lean)
completes the actual partition: outside both charged classes, an effective
response is retained or is a canonical binding with absent or mistyped private
opening material. The risk extension derives this residual from a genuine
information-site history and confines its remaining upper comparison to that
class. Its whole-policy continuation comparison remains an explicit obligation.
[ReactiveBindingPendingExpiry](../Vegas/Pending/ReactiveBindingPendingExpiry.lean)
preserves the pending-failure frame through actual due expiry, including the
public miss marker and service recall. The shared completion congruence lives
in [EventCompletionObservation](../Vegas/Pending/EventCompletionObservation.lean).
[ReactiveBindingCertificateRepair](../Vegas/Pending/ReactiveBindingCertificateRepair.lean)
proves that a mistyped bare commitment installs a real owned certificate
capability absent from its typed-default replacement despite equal networks.
This is a continuation-coupling gap, not a profitable-deviation theorem. A
stopped comparison must act at a real owner input, handle uncharged late
acceptance, and supply rational continuation after a public miss with the
one-time deposit already sunk.
[ReactiveBindingRiskResolve](../Vegas/Pending/ReactiveBindingRiskResolve.lean)
derives actual risk-menu admission of a first timely FALSE decision after
private repair, even without protected delivery. Any supported waiting/FALSE
mixture has a joint response law with the full frame and actual implementation
memory; its retained-policy fallback is unused. Certificate-dependent responses,
subsequent inclusion and whole-policy rationality remain separate.
[ReactiveMissingBindingTransport](../Vegas/Pending/ReactiveMissingBindingTransport.lean)
separates absent opening material from mistyped certifiable material. The
actual absent-opening response blocks the fresh candidate; replacing it adds
owned capabilities without removing any original one. Every subsequent
effective response has the same emitted packet, and bounded raw responses can
be copied after original-input normalization. This is one response step:
later handling of uncertified opening claims can differ, and full frame closure
and settlement dominance remain unproved.
[ReactiveMissingOpeningEvidence](../Vegas/Pending/ReactiveMissingOpeningEvidence.lean)
derives that the actual missing commitment's blocked candidate remains blocked
through arbitrary native continuations. Neither owned nor forwarded evidence
can certify a later opening claim for that handle. Such a claim belongs to the
existing signed-content breach class, so the same final-record verdict and
partial collection bounds apply. This classification supplies no renewed
fine or whole-policy dominance.
[ReactiveBindingAcceptedOpening](../Vegas/Pending/ReactiveBindingAcceptedOpening.lean)
preserves the full frame through actual original opening acceptance, including
publication failure. A matching authentic certificate transfers repaired
acceptance back to the original state; acceptance created by repair is an
actual signed-content breach. The continuation must still be coupled up to
that breach and compared under the one-time settlement law.
[ReactiveBindingInertWindow](../Vegas/Pending/ReactiveBindingInertWindow.lean)
couples finite waiting and activation windows under the actual retained
implementation. Original-input normalization preserves owner responses that
emit no new commitment, while foreign raw responses and public scheduler
choices retain their joint law. The coupling carries the full repair frame,
input recall and old opening capabilities. Inclusion and terminal dominance
are separate obligations; this restricted window is not a whole-policy repair.
Its implementation uses the complete bounded effective menu, so this coupling
does not establish admission to the narrower service risk menu.
[ReactiveBindingOpeningStep](../Vegas/Pending/ReactiveBindingOpeningStep.lean)
classifies the actual pending opening transition: the full frame is preserved,
including invalid-token and rejected inclusions, or the same envelope is an
owner-authored signed breach. Foreign catalogue equality derives ownership
of a repaired-only acceptance.
[SourceServicePastCommitmentTraffic](../Vegas/Game/SourceServicePastCommitmentTraffic.lean)
derives prior owner-commitment provenance from actual issued readiness tokens
at a ready sequential event. Under a policy sending no further commitments,
arbitrary foreign responses and scheduler commands preserve the rank bound;
once this event completes, every old token-valid owner commitment names a
completed event. These are stopping-proof resources, not terminal dominance.
[ReactiveBindingCommitmentStep](../Vegas/Pending/ReactiveBindingCommitmentStep.lean)
uses this completed-event resource to preserve the full frame through actual
owner commitment inclusions. Foreign commitments retain their actual immutable
candidate meaning; invalid tokens and public rejections are consumed with
matching false receipts.
[ReactiveBindingPacketStep](../Vegas/Pending/ReactiveBindingPacketStep.lean)
combines every actual packet constructor and scheduler command, preserving
the full frame or identifying the same pending owner-authored signed breach.
The environment coupling has exact marginals and a common partial observation
draw. [ReactiveBindingInertClosure](../Vegas/Pending/ReactiveBindingInertClosure.lean)
keeps the actual implementation shadow fixed on the noncommitment owner slice
and derives preservation of opening capabilities under every environment
transition. [ReactiveImplementationInvariant](../Interaction/ReactiveImplementationInvariant.lean)
carries ordinary unrestricted service invariants through the same private
implementation's real joint evaluator.
[SourceServiceMissingStoppedCoupling](../Vegas/Game/SourceServiceMissingStoppedCoupling.lean)
couples the full actual run and the same retained implementation's joint
execution and memory law for noncommitment responses or later fresh bare
bindings with arbitrary private material. The completed preparation still
excludes additional owner commitments.
Every endpoint preserves the evolving frame, memory, actual candidate provenance
and opening capabilities, or carries the same actual owner-authored signed breach
in both inputs. Clean branches carry equal actual risk records and service risk
for every inclusion bound. Ordinary runtime invariants come from initialized raw traces and
the real evaluator. One common finite induction serves the complete bounded
effective menu and the risk menu. Its risk consumer derives repaired admission
from actual original risk support, current binding invariants and recalled
records. Missing-registration origins additionally allow the fixed-reuse slice
described below. Full commitment support and terminal utility domination remain
open.
[ReactiveBindingRiskRecall](../Vegas/Pending/ReactiveBindingRiskRecall.lean)
derives the actual initial risk-record equality from both raw traces, their
common scheduler history and submitted event names. Public response before-views
are the corresponding real activation views, with a pending activation handled
explicitly. Paired owner responses preserve these records when they name the
same event. Clear-site admission requires actual canonical response membership.
[ReactiveBindingRiskAdmission](../Vegas/Pending/ReactiveBindingRiskAdmission.lean)
transports actual original risk-supported responses to the same repaired risk
menu at whole inputs. Clear binding and resolution cases derive fresh typed slots,
protected windows and TRUE certificate/guard success; expanded inputs transport
effective responses. Invocation and resume coupling use the same retained
implementation for noncommitments, fresh copies and fixed reuses with matching
meanings or actual public associations. The finite stopped coupling composes
fresh copies. For an actual missing-registration origin it also composes fixed
reuses outside the initially changed slot or with a public association. Reuse of
that slot without association, initial mistyped certificates and terminal utility
domination remain open.
Fresh copied bindings use candidate-only repair memory and preserve their
actual handler outcome or expiry. The fixed-calendar repair induction carries
`BindingShadow.CompletedAt` from empty initial memory through actual completed
blocks. It rules out stale completion overrides at a ready event without an
extra capstone assumption. Reused handles use their fixed candidate meaning,
rather than newly supplied private material.
Later copied mistyped material retains its real raw capability, even when it
fails the current payload type and is usable at another binding. The capability
changed by the initial repair still requires a separate continuation argument.
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
removes sole as a blanket continuation promise: every actual recall extension
has either the sole identifier or two real same-event owner traffic records.
At complete settlement, the first branch records the handle and the second
gets the existing conditional one-time collection bound. This supplies no
renewed fine or whole-policy utility comparison.
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
completion. [SourceServiceCompletedContinuation](../Vegas/Game/SourceServiceCompletedContinuation.lean)
proves that the full typed readout is fixed under arbitrary raw continuation.
At every compatible completed input, silent whole continuation has zero charge
and is optimal in the full effective game under every belief and arbitrary
foreign policies. [SourceServiceCompletedRationality](../Vegas/Game/SourceServiceCompletedRationality.lean)
uses actual decision recall and consistent single-site optimality to prove
rationality without requiring future free policies to be silent. The same
assessments returned by `exists_consistent_original_sequence_completion` and
`exists_consistent_source_completion` are rational at completed compatible
risk-menu sites under nonnegative focal deposits. Its literal pin sequence supplies silence, even for varying original
source approximants and without a waiting-rate bound at these sites.
Unfinished compatible-site comparisons and the general SE theorem remain open.

The risk-menu continuation consumers still require original risk-supported
future responses. An excluded initial response can reach information states
absent from the retained game, so profile extension does not imply that
condition there. Full effective-menu continuations need a separate repair and
comparison argument, including subsequent exclusions and risk-open inputs.

[ReactiveBindingCandidateAgreement](../Vegas/Pending/ReactiveBindingCandidateAgreement.lean)
derives candidate equality outside the one changed slot from two actual
same-before registrations and their real preparation runs. Replacing absent
material preserves every old owned certificate. The same finite continuation
induction carries already equal slots through shared responses and actual
scheduler steps, allowing the fixed-reuse consumer to derive its resources
from those origins. It supplies no terminal utility comparison.

[ReactiveBindingCopiedSubmission](../Vegas/Pending/ReactiveBindingCopiedSubmission.lean)
proves that copying a later fresh bare commitment with its original material
preserves the full frame and its actual raw candidate capability, including
mistyped or absent material. The retained implementation copies originals
already admitted at the actual input, otherwise trying default repair and a
legal fallback. Both transformations share one sampling and response-recording
engine. Calendar callers derive agreement from the actual compiled menu.
The stopped coupling composes fresh copies with arbitrary private material.
Unassociated reuse of the changed slot, initial mistyped certificates and
terminal utility comparisons remain open.

[ReactiveBindingUsableStep](../Vegas/Pending/ReactiveBindingUsableStep.lean)
proves full-frame inclusion closure for matching fixed owner candidates,
including rejected and late calls. Actual fresh usable submission establishes
these matching meanings and completed-boundary memory without assuming
protected inclusion. Local matching-fixed response closure is also checked;
the actual missing-origin fixed-reuse slice is composed by the stopped coupling.
Changed unassociated candidates and initial mistyped certificates remain separate.
[ReactiveUsedBindingOpening](../Vegas/Pending/ReactiveUsedBindingOpening.lean)
proves every opening of a used mistyped candidate is rejected. Its authentic
certificate may fail the public association or typed guard check.
[SourceServiceUsedBindingOpening](../Vegas/Game/SourceServiceUsedBindingOpening.lean)
derives the used association from an actual recalled protected sole commitment
before a later owned resolution, then places its mistyped opening in the
existing auditable public-breach class. Partial collection applies without
treating authentic certification as a signed-content breach. Whole-policy
repair and payoff domination remain open.

[ReactiveBindingCopiedWindow](../Vegas/Pending/ReactiveBindingCopiedWindow.lean)
couples one actual effective owner response law to the same retained private
implementation. Noncommitments, fresh bare registrations with arbitrary
private material and fixed reuses with matching meanings or public associations
preserve current memory, the full frame, commitment provenance and original
opening capabilities.
[ReactiveBindingCopiedResume](../Vegas/Pending/ReactiveBindingCopiedResume.lean)
extends that law to arbitrary foreign raw actions and inactive resumptions.
[ReactiveBindingPacketStep](../Vegas/Pending/ReactiveBindingPacketStep.lean)
also admits actual fixed matching owner candidates at inclusion. The full
fresh-copy suffix is composed by both effective and risk-menu stopped couplings;
utility comparison and finite reused-candidate closure remain open.

## Validation

Run one artifact-writing Lake build at a time. Targeted builds isolate proof
failures; the coherent checkpoint must pass `lake --wfail build`, the evidence
checker, module and documentation checks, central Lean-option checks and
repository tooling tests. The paper must pin the final capstone's standard
axioms. Commit and push each verified checkpoint, preserving unfinished work
outside its staged snapshot. No proof admission or compiler-fact hypothesis
may replace a missing implementation argument.
