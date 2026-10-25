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

## Information and continuation obligations

The phase observation contains retired public snapshots, including their past
clocks. The forced-exit observation exposes the current recovery state and own
recall. Forgetting phase metadata gives a candidate local projection; reconstructing
all phase information from the old input requires a separate proof. Final-state
equality does not supply it.

The existing recovery construction offers a more flexible seam: after any public
exclusion every remaining player's decision agent belongs to a free completion
pool. A phase proof can therefore try to reproduce the source comparisons on
clear inputs and complete the richer post-exclusion game rationally. It must use
one common fully mixed approximation and its Bayes-consistent limit, rather than
selecting unrelated best responses at separate information sets.

The remaining obligations are:

1. Combine the checked callback-menu comparisons and private-alias extension
   inside the actual history construction. Reverse admission uses a paired genuine
   native prefix; that prefix must be constructed by the induction. The canonical
   recovery menu and phase raw count-filtered menu are related through the
   operational normalizer rather than treated as identical.
2. Construct the matched builder and actual reactive history or stopped-law
   comparison, including packet observations, own recall and source initialization.
   The checked physical kernels do not by themselves supply a scheduler or a
   legal cross-contract trace. Derive the needed service guards with their
   actual history quantifiers.
3. Instantiate one common fully mixed completion on the phase game and prove its
   clear-input Bayes and continuation-gain comparisons. Complete post-exclusion
   decisions rationally using their actual richer information. The absence of
   exclusion in the limiting recovery equilibrium does not justify deleting
   off-path archive information or choosing unrelated belief limits. In particular,
   latent own source debt must retain its exclusion payoff through every
   continuation. An already-excluded player's constant-payoff theorem does not
   establish this: the recovery proof also uses failed-source-readout valuation.
   Prove the phase payoff compatibility or actual exclusion consequence explicitly;
   changing phase terminal utility would change the target.
4. Apply the existing phase one-packet-to-raw SE extension to recover audited
   settlement and the joint law. No isomorphism of all raw actions is required.

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
