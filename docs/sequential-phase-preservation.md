# Sequential equilibrium on the phase runtime

The intended-game preservation theorem applies on
`phaseApplication`, instantiated with the sequential compiled graph, singleton
phases and supplied per-event relative deadline durations. See the
[deadline scope](se-deadline-scope.md) for the timing contract and concrete
positive-latency instance.
The phase executor exposes packet observations, a retirement archive
and permanent exclusion. The concurrent reserved-tape theorem uses a maximal
phase plan.

The conclusion is a sequential equilibrium against whole-policy
deviations, preserving the joint typed readout and realized settled payoff law
with zero audit charges and no excluded owners on its paths.
[Canonical preservation](../Vegas/Game/SequentialPhasePreservation.lean) and
[audited raw preservation](../Vegas/Game/SequentialPhaseRawPreservation.lean)
are stated under the assumptions below. The paper-facing theorem is
`Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium`.

## Assumptions

The source setup is well formed, with private inputs independent conditional on
an observable public initial signal. The source premise is an equilibrium of the
intended game. The exit payoff is at most every intended terminal payoff, and
utility has the existing lower and upper bounds, including the treatment of
unfinished executions as zero.

Players and intended-protocol histories are finite. The fixed bounded physical
phase runtime has finite nature; native and recovery finiteness are derived by
the adapters. The theorem allows adaptive scheduling and arbitrary leak rules
satisfying the stated physical service assumptions.

The builder must satisfy opportunity, protected inclusion and completion on the
actual phase runtime. Their primitive definitions already live in
[PhaseServiceContract](../Vegas/Pending/PhaseServiceContract.lean). The
[native service adapter](../Vegas/Game/SequentialPhaseNativeService.lean)
derives the clear counted-prefix guards used by the one-packet comparisons.
Completion covers all legal horizon-terminal states. The reaction and inclusion
bounds must sum to strictly less than each owned event's supplied duration
`runtime.deadline event`, measured from that event's readiness clock.

Applying the theorem requires proofs of the entire physical service contract,
in addition to the timing inequality and finite-nature instance. Opportunity,
protected inclusion and completion quantify over every legal raw phase history,
including horizon-terminal histories. A scheduler that satisfies only the
timing inequality does not supply these hypotheses.

The response catalogue covers output and input values, with candidate capacity
strictly greater than each player's binding-event count over the whole program.
Singleton phases do not reduce that requirement to a per-phase bound. Raw-menu
extension retains the multiplicative funding condition: the payoff spread is at
most observation rate times delivery rate times deposit. Neither rate is divided
out or silently assumed positive.

## Concrete instance

[The service fixture](../Vegas/Examples/SequentialPhaseService.lean) publishes
an initially private Boolean commitment and computes a payment of two for true
and zero for false. Its four-command scheduler activates the owner, includes
the optional packet, advances the clock and expires an unfinished publication.
The deadline is one and both service bounds are zero.

The fixture proves finite nature, opportunity, protected inclusion and
completion for every legal raw application history, including malformed
responses, silence and horizon-terminal states. Both private inputs have
positive initial probability and reach a genuine player decision. Input/output
coverage, capacity, well-formedness and the observable conditional-independent
prior are also proved.

[The equilibrium application](../Vegas/Examples/SequentialPhaseServiceEquilibrium.lean)
proves source equilibrium existence and applies the preservation theorem to
obtain an actual whole-policy raw phase SE. It assumes neither equilibrium nor
service witnesses. Utility is proved equal to the program's executable
transfer; the exclusion payoff is minus one, the deposit is three, and complete
authentic reporting supplies observation and delivery rates of one.

[The delayed service](../Vegas/Examples/SequentialPhaseDelayedService.lean)
uses the same source game with deadline duration six and reaction/inclusion
bounds three and two. Its first event is player-owned; activation occurs at
clock one and receipt at clock two. It proves the full all-raw-history service
contract and finite nature, rather than only the inequality `3 + 2 < 6`.
[Its equilibrium application](../Vegas/Examples/SequentialPhaseDelayedEquilibrium.lean)
constructs a funded raw sequential equilibrium with no exits or charges and
the exact intended joint readout and realized settled-payoff law.

## Checked interfaces

- [SequentialRuntimePhases](../Vegas/Game/SequentialRuntimePhases.lean) constructs
  the actual singleton plan from the sequential compiled program and proves
  event membership, ownership, readiness confinement and settlement quiescence.
  This instantiates the existing phase executor rather than defining a new one.
- [PhaseSingleton](../Vegas/Pending/PhaseSingleton.lean) proves that a fresh miss
  in a singleton commitment phase leaves no surviving owner to retry. Settlement
  keeps the generation unchanged for lists with singleton commitment phases.
- [PhaseSingletonRebuild](../Vegas/Pending/PhaseSingletonRebuild.lean) proves exact
  physical-state equality after rebuilding one automatically completed singleton,
  under native invariance, unique readiness and alignment of the saved config and
  accepted handles. The result retains candidates, clock and activation metadata.
- [PhaseSingletonTransition](../Vegas/Pending/PhaseSingletonTransition.lean)
  applies the rebuild comparison to the actual due-expiry kernel, retaining the
  failed endpoint in the archive and advancing to the remaining phase suffix.
- [PhaseDrainCorrespondence](../Vegas/Pending/PhaseDrainCorrespondence.lean)
  identifies phase settlement with the global recovery drain when checkpoint
  exclusion is unchanged, readiness is unique and the endpoint is globally
  quiescent. The proof concatenates actual automatic-completion traces.
- [PhaseClearMetadata](../Vegas/Pending/PhaseClearMetadata.lean) proves on every
  legal raw history that empty exclusion implies generation zero and an empty
  archive. Consequently a nonempty actual archive certifies public exclusion.
- [PhaseRecoveryInformation](../Vegas/Game/PhaseRecoveryInformation.lean) projects
  actual local views, recall, packet identities and receipts to recovery
  information without consulting the builder's hidden history.
- [PhaseRecoveryMenuProjection](../Vegas/Game/PhaseRecoveryMenuProjection.lean)
  proves raw bounded-menu agreement and commutation of existing operational
  normalization with this projection. The normalized phase raw menu agrees with
  the recovery canonical menu. The
  [canonical choice equivalence](../Vegas/Game/SequentialPhaseChoiceEquivalence.lean)
  supplies the one-packet correspondence at clear played inputs.
- [PhaseCheckpointAlignment](../Vegas/Pending/PhaseCheckpointAlignment.lean)
  derives exact saved/live config and accepted-handle equality at every actual
  unfinished singleton raw history. Its
  [accepted-table frame](../Vegas/Pending/PhaseAcceptedFrame.lean) accounts for
  arbitrary private preparation and unusable accepted bindings. The accompanying
  [exclusion comparison](../Vegas/Pending/PhaseCheckpointExclusion.lean) proves
  that saved and current exclusions agree there as well.
- [SequentialPhaseObservation](../Vegas/Game/SequentialPhaseObservation.lean)
  reconstructs the entire current public phase view from the native public view
  before exclusion, using the actual completion-order length and plan suffix.
- [PhaseClearPacketInformation](../Vegas/Game/PhaseClearPacketInformation.lean)
  reconstructs exact static tags on every retained packet of a clear one-packet
  history, including pending, ledger and leaked packets, for arbitrary observation
  rules. It assumes neither author-only leakage nor honest policies.
- [PhaseStaticCountVerdict](../Vegas/Pending/PhaseStaticCountVerdict.lean) proves
  that clean traffic with a fixed namespace per event has the same phase and
  native count verdict, including opening references to signed bindings.
- [SequentialPhasePlayerInformation](../Vegas/Game/SequentialPhasePlayerInformation.lean)
  reconstructs each player's full current input and own recall from its recovery
  projection on every actual clear counted history. The decoder uses only that
  player's information, with arbitrary leak rules and policies.
- [PhaseClearService](../Vegas/Pending/PhaseClearService.lean) proves that a signed
  input for an unfinished event retains the current attempt on clear singleton
  counted histories. It derives native fixed-execution protected inclusion from
  the existing phase service contract, preserving identifiers, clocks and receipts.
- [SequentialPhaseEnvironment](../Vegas/Game/SequentialPhaseEnvironment.lean)
  proves equality of the actual phase environment kernel's current-state marginal
  and the recovery environment kernel for every command on every initialized raw
  sequential singleton history.
- [SequentialPhaseHandle](../Vegas/Game/SequentialPhaseHandle.lean) proves the
  analogous actual handler equality for every signed input of a clear counted
  history. It covers unusable accepted commitments and failed openings; the
  [settlement adapter](../Vegas/Game/SequentialPhaseSettlement.lean) retains the
  automatic cascades.
- [SequentialPhaseCountedMenu](../Vegas/Game/SequentialPhaseCountedMenu.lean)
  proves that every canonical admitted phase response at an actual clear counted
  prefix projects to a legal recovery one-packet response. The
  [local envelope comparison](../Vegas/Game/PhaseRecoveryLocalEnvelope.lean)
  supplies the actual count-verdict producer; raw aliases are not silently
  identified with canonical recovery choices.
- [RecoveryOnePacketPreservation](../Vegas/Game/RecoveryOnePacketPreservation.lean)
  exposes intended-to-one-packet SE preservation, no exclusions on supported
  paths and its joint base-payoff/readout law without an audit backend or funding
  premises. The full recovery raw theorem carries no exclusions through the
  raw-extension theorem's normalized state law, alongside zero audit charges.
- [RecoveryInitializedClearance](../Vegas/Game/RecoveryInitializedClearance.lean)
  proves no exclusion in the actual common completion limit. It bounds the runtime
  exclusion flag by native failure mass, makes that bound vanish with the common
  tremble scale, and passes it through strategy-to-terminal-law convergence. It
  uses neither payoff equality nor audit cleanliness.

- [PhaseResponseAliases](../Vegas/Pending/PhaseResponseAliases.lean) proves exact
  local-envelope preservation, recall stability and closure for the actual
  counted menu under its existing operational normalizer.
  [PhaseResponseAliasEquilibrium](../Vegas/Game/PhaseResponseAliasEquilibrium.lean)
  derives SE extension from that normalized counted game to its private response
  aliases, with projected beliefs at every information site and the complete
  normalized protocol-state law. Its payoff premise is invariance under private
  response normalization.
- [OnePacketClearCountedResponse](../Vegas/Game/OnePacketClearCountedResponse.lean)
  shows that every completed owned event in a clear native counted history has
  an authentic own signed packet. Consequently no count-permitted new callback
  can repeat a completed event, and its named event is genuinely ready.

- [SequentialPhaseCountedMenuReverse](../Vegas/Game/SequentialPhaseCountedMenuReverse.lean)
  proves reverse admission and phase canonical normalization at paired actual
  clear phase/native counted prefixes. The source prefix and deciding-player
  information match are induction premises, rather than an assumed final law.
- [SequentialPhaseSchedulerInformation](../Vegas/Game/SequentialPhaseSchedulerInformation.lean)
  reconstructs the builder's own environment view and full recall on actual clear
  counted prefixes, and proves the derived scheduler's exact command law there.
  [Recorded environment origins](../Interaction/ReactiveRecordedEnvironment.lean)
  supply genuine earlier prefixes for every remembered command.

## Execution, beliefs and continuation values

The actual transition comparison covers both player responses and environment
steps, with length-preserving legal traces in both directions before exclusion.
[SequentialPhaseTransition](../Vegas/Game/SequentialPhaseTransition.lean) retains
the first exclusion endpoint; it does not identify the richer continuations after
that endpoint. The
[reverse clear lift](../Vegas/Game/SequentialPhaseClearLift.lean) constructs a
genuine canonical phase prefix from a counted recovery prefix. The
[choice equivalence](../Vegas/Game/SequentialPhaseChoiceEquivalence.lean) identifies
actual typed callbacks there. Source/native finite nature is
[derived from phase finite nature](../Vegas/Game/SequentialPhaseFiniteNature.lean).

The phase archive contains retired public snapshots and clocks. Clear inputs
have a checked inverse using the player's own information. After exclusion,
remaining decision agents belong to free completion pools. Their continuations
must be optimized in the actual phase game, retaining its richer information.

[SequentialPhaseCompletion](../Vegas/Game/SequentialPhaseCompletion.lean) constructs
one common fully mixed sequence of actual phase assessments, its Bayes beliefs,
and a consistent subsequential limit. It proves pooled optimality at every
approximation and arbitrary local-law optimality at free sites in the limit.
[The recovery comparison](../Vegas/Game/SequentialPhaseRecoveryComparison.lean)
constructs a global fully mixed recovery sequence that agrees with the phase
component mixtures at clear played inputs. Its choices after exclusion are
arbitrary; recovery optimality of those choices is neither assumed nor proved.

[SequentialPhaseStoppedLaw](../Vegas/Game/SequentialPhaseStoppedLaw.lean) proves
exact stopped-state law transport before exclusion or a supplied physical-state
guard, for actual phase menus included in the counted menu. The generic
[StoppedBayes](../GameTheoryExtensions/Analysis/Protocol/StoppedBayes.lean) theorem
recovers a site's Bayes state posterior from its first-passage law, including the
corresponding information-mass identity. The
[phase application](../Vegas/Game/SequentialPhaseBayesState.lean) constructs a
real recovery information site, derives its positivity from phase-site positivity,
and proves equality of the full physical-state Bayes laws. This comparison uses
the decoded raw recovery policy.
[SequentialPhaseComparisonPolicy](../Vegas/Game/SequentialPhaseComparisonPolicy.lean)
proves its exact agreement with the embedded canonical comparison at every
actual clear recovery history, including inactive players. [SequentialPhaseComparisonStopped](../Vegas/Game/SequentialPhaseComparisonStopped.lean)
carries the stopped physical-state laws through that agreement, directly between
the actual phase component assembly and bounded recovery comparison, from any
matched history pair.
[SequentialPhaseComparisonBayes](../Vegas/Game/SequentialPhaseComparisonBayes.lean)
proves the resulting physical-state posterior equality for the actual phase and
bounded recovery comparison policies at the positive factory scales. It
constructs the recovery decision site and derives its positivity.

The original terminal utility is preserved.
[PhaseTerminalFailure](../Vegas/Game/PhaseTerminalFailure.lean) proves that a failed
program reveal in a decoded terminal readout implies actual exclusion of its
owner, and equates the existing phase and recovery base payoffs under the actual
failure-coverage invariant. The compiler supplies the reveal's owned-output
provenance. Inherited publication cells are not confused with program reveals.
[SequentialPhaseDecodedDebt](../Vegas/Game/SequentialPhaseDecodedDebt.lean) proves
that latent own source debt remains absorbing and yields the exclusion payoff
under every whole-policy continuation satisfying the actual completion contract.
This handles debt before it becomes public exclusion, without changing utility.

## Native service and value estimates

[OnePacketCountedService](../Vegas/Game/OnePacketCountedService.lean) isolates
opportunity and protected inclusion at genuine clear counted prefixes. The
[waiting theorem](../Vegas/Game/OnePacketBoundaryWaiting.lean) uses those factual
conditions and clear counted terminal completion to reach the first owner
callback while preserving configuration and own recall. Its
[phase instance](../Vegas/Game/SequentialPhaseBoundaryWaiting.lean) obtains each
condition from the original physical phase contract. The existing recovery
results remain full-contract specializations of the shared proofs.

[SequentialPhaseNativeComparison](../Vegas/Game/SequentialPhaseNativeComparison.lean)
constructs the actual native fully mixed Bayes sequence from the phase weights.
The initialized recovery prior uses the same expression as the existing native
factory; its equality with the phase projection is proved at the trace and nature
producers. No independent source/native finiteness assumption is added.

The [foreign-exit bound](../Vegas/Game/SequentialPhaseForeignFailureBound.lean)
retains the original quadratic-plus-linear tremble error times remaining runtime
rank, for arbitrary focal policies starting at genuine clear regular native
source turns. It stops at public failure or focal source debt and allows an
additional stopping predicate. It does not assert a uniform estimate over all
raw histories.
[SequentialPhaseNativeValues](../Vegas/Game/SequentialPhaseNativeValues.lean)
instantiates the binding source kernel with the actual phase comparison weights,
retaining its cubic completion-law error and bad-stop bound. Its terminal
completion callback comes from the original phase completion contract.

[SequentialPhaseStoppedPayoff](../Vegas/Game/SequentialPhaseStoppedPayoff.lean)
compares actual phase terminal utility with the debt-stopped readout. Own
exclusion and own source debt have their original constant payoff; the remaining
error is bounded by twice the utility bound times foreign-exit probability.
The [belief version](../Vegas/Game/SequentialPhaseStoppedPayoffBelief.lean) averages
this estimate. [Actual-history projection](../Vegas/Game/SequentialPhaseStoppedPayoffHistory.lean)
derives failure coverage from legal histories rather than assuming it.
[SequentialPhaseLocalStopped](../Vegas/Game/SequentialPhaseLocalStopped.lean)
extends the matched physical laws to arbitrary focal choice distributions at
clear played inputs. The
[native debt readout identity](../Vegas/Game/RecoveryDebtStoppedReadout.lean)
separates exact stopped-law transport from completion and payoff bounds.

The [uniform native value error](../Vegas/Game/SequentialPhaseNativeValueError.lean)
fixes one actual native comparison site for every phase baseline/deviation
law. It combines exact Bayes and choice transport with the regular-prefix
foreign-exit bound and posterior irregular-history drift. The original
conditional private-input independence, observable signal, calibrated tremble
scale and catalogue coverage assumptions remain explicit.
[Baseline law transport](../Vegas/Game/SequentialPhaseNativeStrategyLaw.lean)
identifies the mapped phase strategy with the actual native comparison strategy
at that site. The [gain bound](../Vegas/Game/SequentialPhaseNativeGainError.lean)
therefore compares a deviation and its prescribed baseline using the same
uniform error; no baseline identity is assumed.
[Native ordinary-response comparisons](../Vegas/Game/SequentialPhaseNonLateNativeComparisons.lean)
bound pure pending responses by the original source deviations under physical
phase service. At an unpending, nonowing ordinary phase site,
[all local choice laws coincide](../Vegas/Game/SequentialPhaseUnpendingChoices.lean),
so their gain is exactly zero for arbitrary payoffs.
[Pending affine values](../Vegas/Game/SequentialPhasePendingValueAffine.lean)
and [arbitrary local completion values](../Vegas/Game/SequentialPhaseLocalCompletionValue.lean)
instantiate the shared source-potential proofs from actual phase completion and
honest continuation estimates. Both binding and resolution events are covered.
[Keyed component values](../Vegas/Game/SequentialPhaseKeyedComponentValues.lean)
use common native option scores for the original phase utility, with only the
original intended-terminal punishment floor.
[Pooled component gains](../Vegas/Game/SequentialPhaseKeyedGains.lean) follow from
the actual phase pooled optimality and owing-site indifference, with one uniform
vanishing error. [Pure option bounds](../Vegas/Game/SequentialPhaseKeyedPureChoices.lean)
control the physical tremble loss and identify each keyed option as a part of
the same pool. [Keyed pure-choice comparisons](../Vegas/Game/SequentialPhaseKeyedComparisons.lean)
cover every legal phase choice using these actual pooled gains and the original
source-deviation alternatives.

The [honest source laws](../Vegas/Game/SequentialPhaseHonestLaw.lean) and
[same-weight retention](../Vegas/Game/SequentialPhaseComparisonRetention.lean)
supply the initialized comparison estimates from actual counted service.
[SequentialPhaseInitializedLaw](../Vegas/Game/SequentialPhaseInitializedLaw.lean)
proves the original physical phase joint readout/base-payoff approximation.
[SequentialPhaseInitializedClearance](../Vegas/Game/SequentialPhaseInitializedClearance.lean)
proves no exclusions on initialized limit support by bounding the physical
exclusion flag. Arbitrary suffixes after exclusion remain in the actual game;
their rare probability is bounded rather than their states being identified.

[The shared protocol limit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
requires only pure local-choice comparisons. Decision recall extends those to
local lotteries and whole-policy SE at the common consistent limit. The recovery
consumer and pooled-component consumer reuse this argument.
The preservation capstone applies it to the same actual phase completion
sequence and its consistent limit, deriving the initialized law approximation
from physical phase service.
[SequentialPhaseRawLaw](../Vegas/Game/SequentialPhaseRawLaw.lean) checks the final
sequential audit consumer: a canonical phase SE with the desired law extends to
raw audited SE with zero charges, no exclusions and the realized settled joint
law.

The preservation proof composes these interfaces:

1. [Ordinary comparisons](../Vegas/Game/SequentialPhaseNonLateComparisons.lean)
   and keyed comparisons bound every pure deviation of the actual phase common
   completion by an original source gain or a vanishing error. Owing sites have
   exactly zero gain. Keyed sites use actual phase pooled optimality.
2. [Combined comparisons](../Vegas/Game/SequentialPhaseLocalComparisons.lean)
   use one uniform vanishing error before quantifying over sites and choices.
   The shared limit then supplies whole-policy SE and the initialized joint law
   for the same consistent completion witness.
3. Canonical preservation combines that limit with the physical no-exclusion
   support theorem. Raw preservation applies the alias and count-audit
   extensions, retaining the realized settled joint law and zero charges.

This proves the singleton sequential-phase scope above. The broader
[arbitrary-builder checklist](se-async-checklist.md) retains its own fixed target
and obligations.

## Service and emission boundaries

The two service contracts quantify over their own unrestricted raw histories.
The phase inclusion predicate tests uniqueness per attempt and event; the
recovery predicate tests uniqueness per static event. Tag erasure supplies a
one-way fixed-execution comparison when the protected packet retains the current
attempt. A converse or all-history scheduler lift does not follow from that
comparison.

Native readiness tokens can still be issued for already completed events,
whereas the phase mask removes tokens outside the installed phase. Consequently
arbitrary raw local envelopes need not agree. The one-packet comparison must
reject repeated completed-event calls on both sides by their earlier own signed
packet, while treating current and future events separately. The raw count-audit
extension follows only after the one-packet equilibrium is established.
