# Sequential equilibrium on the phase runtime

The target is the existing intended-game preservation guarantee on
`phaseApplication`, instantiated with the sequential compiled graph and singleton
phases. The phase executor, packet observations, retirement archive and permanent
exclusion semantics stay as implemented. The concurrent reserved-tape theorem
keeps its existing maximal-phase plan.

The desired conclusion is a sequential equilibrium against whole-policy
deviations, preserving the joint typed readout and realized settled payoff law
and charging nobody on its paths. A physical state comparison alone does not
establish this conclusion.

## Assumptions to retain

The source setup is well formed, with private inputs independent conditional on
an observable public initial signal. The source premise is an equilibrium of the
intended game. The exit payoff is at most every intended terminal payoff, and
utility has the existing lower and upper bounds, including the treatment of
unfinished executions as zero.

The builder must satisfy opportunity, protected inclusion and completion on the
actual phase runtime. Their primitive definitions already live in
[PhaseServiceContract](../Vegas/Pending/PhaseServiceContract.lean). Their relation
to the recovery service premises needs proofs; it cannot be inferred from a
singleton plan. The old opportunity and inclusion assumptions quantify over
all legal recovery traces, including traces after exclusion. Completion covers
all legal horizon-terminal states. The reaction and inclusion bounds must sum to
strictly less than each owned event's deadline.

The response catalogue covers output and input values, with candidate capacity
strictly greater than each player's binding-event count over the whole program.
Singleton phases do not reduce that requirement to a per-phase bound. Raw-menu
extension retains the multiplicative funding condition: the payoff spread is at
most observation rate times delivery rate times deposit. Neither rate is divided
out or silently assumed positive.

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
  the recovery canonical menu; the one-packet count filters remain to compare.
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

These are supporting theorems. They do not prove the target preservation theorem
or close an arbitrary-builder checklist obligation.

## Execution, beliefs and continuation values

The actual transition comparison now includes both player responses and environment
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
constructs the old decision site and derives its positivity, rather than adding
a separate old-site assumption.

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

The remaining obligations are:

1. Combine the checked local-deviation stopped laws, Bayes posteriors and payoff
   error with the native source-value estimates. Prove the forced and keyed
   continuation-gain comparisons for the actual phase common completion, retaining
   the original intended-terminal exit floor and source-information assumptions.
2. Derive the initialized comparison's joint-law approximation and vanishing
   exclusion probability using the honest source law and same-weight retention.
   The shared counted service interfaces must supply its actual history guards.
3. Apply the existing common-limit comparison machinery to prove phase SE, then
   recover the intended joint readout/payoff law and apply the phase counted-to-raw
   extension with audited settlement and the multiplicative funding condition.

These supporting theorems do not yet prove the target preservation theorem or
close an arbitrary-builder checklist obligation.

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
