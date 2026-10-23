/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReservedEpochUnflaggedExpiry
import Interaction.ReactiveEnvironmentMass
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Old request origins of stopped unflagged commitment failures -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem stopped_prefix_roundsSupported
    {app : ReactiveApplication Player} (menu : app.ResponseMenu)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (remaining : Nat) (anchor : app.Execution)
    (trace : (menu.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, anchor⟩))
    (stopped : (menu.protocol initial horizon scheduler).History → Prop) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralUntil
        (menu.bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∀ middle : (menu.protocol initial horizon scheduler).History,
        TracePrefix trace middle.trace → TracePrefix middle.trace final.trace →
          app.RunRoundsSupported scheduler (menu.decodeProfile initial horizon scheduler profile)
            anchor middle.state := by
  classical
  let model := menu.information initial horizon scheduler
  let players := menu.decodeProfile initial horizon scheduler profile
  let property := fun history : (menu.protocol initial horizon scheduler).History =>
    TracePrefix trace history.trace ∧
      ∀ middle : (menu.protocol initial horizon scheduler).History,
        TracePrefix trace middle.trace → TracePrefix middle.trace history.trace →
          app.RunRoundsSupported scheduler players anchor middle.state
  have preserved : ∀ history, ¬ stopped history →
      ¬ (menu.protocol initial horizon scheduler).terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        property next := by
    intro history _going running holds next supported
    have extended := model.runBehavioralFrom_reachesWithin profile 1 history next supported
    have length := model.length_of_mem_support_runBehavioralFrom_one profile running supported
    refine ⟨holds.1.trans extended.tracePrefix, ?_⟩
    intro middle after before
    by_cases earlier : middle.trace.length ≤ history.trace.length
    · have keptEarlier := before.reachesWithin.ancestor_comparable extended earlier
      exact holds.2 middle after keptEarlier.tracePrefix
    · have equal : middle = next := by
        exact before.eq_of_length (by have upper := before.length_le; omega)
      subst middle
      have current := holds.2 history holds.1 .refl
      have step : next.state ∈
          (app.controlStep initial horizon scheduler players history.state).support := by
        have mapped : next.state ∈
            ((model.runBehavioralFrom profile 1 history).map History.state).support :=
          (PMF.mem_support_map_iff _ _ _).mpr ⟨next, supported, rfl⟩
        rw [menu.run_map_state_eq_iterate initial horizon scheduler profile 1 history] at mapped
        simpa only [Function.iterate_one, PMF.pure_bind] using mapped
      exact ReactiveApplication.runRoundsSupported_controlStep initial horizon scheduler
        players anchor history.state next.state current step
  have initially : property ⟨some ⟨remaining, none, anchor⟩, trace⟩ := by
    refine ⟨.refl, ?_⟩
    intro middle after before
    have same : middle = ⟨some ⟨remaining, none, anchor⟩, trace⟩ :=
      before.eq_of_length (Nat.le_antisymm before.length_le after.length_le)
    cases same
    exact ⟨0, (PMF.mem_support_pure_iff _ _).mpr rfl⟩
  intro final supported
  exact (model.runBehavioralUntil_support_history_closed
    (menu.bounded initial horizon scheduler).wellFoundedHistories profile stopped property
      preserved ⟨some ⟨remaining, none, anchor⟩, trace⟩ initially final supported).2

omit [Fintype Player] in
theorem phase_exclusion_transition_idle
    {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (joint : Player → Option (phaseApplication runtime leaks).Action)
    (moved : some after ∈ ((phaseApplication runtime leaks).transition
      initial horizon scheduler (some before) joint).support)
    (owner : Player) (active : owner ∉ before.execution.application.current.excluded)
    (excluded : owner ∈ after.execution.application.current.excluded)
    (command : EnvironmentCommand graph)
    (actual : after.execution ∈ (before.execution.environmentStep
      (phaseApplication runtime leaks) (.application command)).support) : after.actor = none := by
  rcases before with ⟨remaining, actor, execution⟩
  cases actor with
  | some acting =>
      cases (PMF.mem_support_pure_iff ..).mp moved
      generalize actionEq : (joint acting).getD
        ({ transmission := none } : (phaseApplication runtime leaks).Action) = action at excluded
      rcases action with ⟨transmission⟩
      cases transmission <;> exact (active excluded).elim
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff ..).mp moved
          exact (active excluded).elim
      | succ remaining =>
          obtain ⟨selected, _positive, supported⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
          obtain ⟨next, stepped, same⟩ := PMF.support_map .. ▸ supported
          cases Option.some.inj same
          have commands := (phaseApplication runtime leaks).environmentStep_command_unique
            execution next selected (.application command) stepped actual
          rw [commands]
          rfl

variable (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "graph" => serviceGraph setup mode
local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs

/-- At each actual first-attempt stopped endpoint, every newly excluded
commitment owner had a literal ready old episode at the anchor. Its original
binding has no accepting receipt at that endpoint, including after rollback.
All fresh successors and all initial unsafe packets are interpreted by the
actual unflagged runner; no coupled footprint is assumed. -/
theorem phaseProposalUnflagged_stopped_exclusion_request
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩))
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (owner : Player) (active : owner ∉ anchor.application.current.excluded) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∀ ending, final.state = some ending →
        owner ∈ ending.execution.application.current.excluded →
          ∃ event ∈ phase.events,
            anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ ∧
              PhaseCount.ResponseRecorded runtime leaks owner
                ⟨anchor.application.attempt, event⟩ (anchor.recall owner) ∧
              ¬ PhaseService.BindingAccepted runtime leaks
                ⟨anchor.application.attempt, event⟩ owner ending.execution := by
  classical
  intro initial horizon scheduler players profile stopped final supported ending stateEq excluded
  rcases final with ⟨finalState, finalTrace⟩
  change finalState = some ending at stateEq
  subst finalState
  let final : ((menu).protocol initial horizon scheduler).History := ⟨some ending, finalTrace⟩
  obtain ⟨before, after, prior, joint, legal, realized, _originEvent, fromStart, toFinal,
    atAttempt, phaseInstalled, wasActive, nowExcluded, _originInside, _originRequest⟩ :=
    phase_attempt_stopped_exclusion_origin runtime leaks (menu) plan inputs horizon scheduler
      profile ⟨remaining, none, anchor⟩ trace phase installed owner active final
        (by
          dsimp only [initial, stopped] at supported
          convert supported using 1
          congr 3
          funext history
          cases history.state <;> rfl) ending rfl excluded
  obtain ⟨command, applicationStep⟩ := PhaseService.new_exclusion_application_command
    runtime leaks plan inputs horizon scheduler before after joint realized owner wasActive
      nowExcluded (by
      intro message next handled
      have same := PhaseRuntimeState.handle_commitment_phase_excluded runtime
        before.execution.application next phase phaseInstalled commitment message handled
      exact fun chosen => wasActive (same ▸ chosen))
  have idle := phase_exclusion_transition_idle runtime leaks initial horizon scheduler before after
    joint realized owner wasActive nowExcluded command applicationStep
  obtain ⟨updated, selected, executionEq⟩ := PMF.support_map .. ▸ applicationStep
  obtain ⟨next, phaseStep, updateEq⟩ := PMF.support_map .. ▸ selected
  have afterApplication : after.execution.application = next := by
    exact (congrArg (fun execution : (app).Execution => execution.application)
      executionEq).symm.trans
        (congrArg (fun execution : (app).Execution => execution.application) updateEq).symm
  obtain ⟨event, native, commandEq, inside, request, nativeStep, completed, _normalized⟩ :=
    PhaseRuntimeState.environment_new_exclusion_request runtime before.execution.application next
      phase phaseInstalled command phaseStep owner wasActive
        (by simpa only [afterApplication] using nowExcluded)
  subst command
  have roundSupport := stopped_prefix_roundsSupported (menu) initial horizon scheduler profile
    remaining anchor trace stopped final supported ⟨some after, prior.extend joint legal realized⟩
      (TracePrefix.extend fromStart joint legal realized) toFinal
  have decoded : (menu).decodeProfile initial horizon scheduler profile = players := by
    funext who
    exact (menu).decode_restrictPolicy_of_covered initial horizon scheduler who (players who)
      ((menu).anchoredPolicy_covered initial horizon scheduler ⟨remaining, none, anchor⟩ trace
        (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values) who
          (phaseProposalUnflaggedPolicy_covered setup mode runtime leaks bounds plan values who))
  rw [decoded] at roundSupport
  rcases after with ⟨afterRemaining, afterActor, afterExecution⟩
  change afterActor = none at idle
  subst afterActor
  obtain ⟨count, reached⟩ := roundSupport
  rw [ReactiveApplication.runRounds_anchoredPolicy] at reached
  obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler ((menu).toRawTrace initial horizon scheduler prior)
  have activated := (invariant.active.activated_iff event).mpr
    ⟨request.2.2.1, by simp only [request.2.2.2.1, Option.isSome_some]⟩
  cases stamp : before.execution.application.current.native.activatedAt event with
  | none => simp only [stamp, Option.isSome_none, Bool.false_eq_true] at activated
  | some entered =>
      have due : runtime.deadline event ≤
          before.execution.application.current.native.clock - entered := by
        by_contra early
        rw [environmentStep_expire_of_not_due runtime _ event request.2.2.1 entered stamp early]
          at nativeStep
        cases (PMF.mem_support_pure_iff _ _).mp nativeStep
        exact request.2.2.1.1 completed
      obtain ⟨_who, payload, binding⟩ := commitment ▸ phase.fields event
        ((phase.mem_events event).mp inside).1 ((phase.mem_events event).mp inside).2
      have ownerEq : _who = owner := Option.some.inj
        (((graph).actor?_of_outputLayout_binding binding).symm.trans request.2.2.2.1)
      subst _who
      have expiryPrefix : TracePrefix prior (prior.extend joint legal realized) :=
        TracePrefix.extend (E := (menu).protocol initial horizon scheduler) .refl
          joint legal realized
      have old := phaseProposalUnflagged_expiry_recorded_at_anchor setup mode runtime leaks bounds
        plan complete coveredValues maximal ordered values fullValues tape activationGap
          processingGap gaps margin capacity ⟨remaining, none, anchor⟩ trace before prior fromStart
            owner event payload binding request entered stamp due afterExecution afterRemaining
              applicationStep (prior.extend joint legal realized)
                expiryPrefix count reached
      have anchorRequest := old.2 atAttempt
      have mapped :=
        ((menu).reaches_raw initial horizon scheduler toFinal.reachesWithin).tracePrefix
      obtain ⟨other, _otherInside, otherRequest, unaccepted⟩ :=
        PhaseService.not_bindingAccepted_after_commitment_exclusion runtime leaks plan inputs
          horizon scheduler before ⟨afterRemaining, none, afterExecution⟩ ending
            ((menu).toRawTrace initial horizon scheduler prior) joint
              ((menu).legal_raw initial horizon scheduler legal) realized
                ((menu).toRawTrace initial horizon scheduler finalTrace) mapped phase phaseInstalled
                  commitment owner wasActive nowExcluded
      have eventEq : other = event := ordered.ready_actor_unique _ request.2.2.1
        otherRequest.2.2.1 request.2.2.2.1 otherRequest.2.2.2.1
      subst other
      refine ⟨event, inside, ?_, ?_, ?_⟩
      · simpa only [atAttempt] using anchorRequest
      · simpa only [atAttempt] using old.1
      · simpa only [atAttempt] using unaccepted

/-- A genuinely fresh owned frontier survives the entire actual commitment
attempt under the prescribed unflagged future. This is a stopped-run result,
not a declaration that an old WAIT or pending episode has become fresh. -/
theorem phaseProposalUnflagged_stopped_survival_of_fresh
    (complete : leaks = MessageNetwork.completePendingObservation)
    (coveredValues : bounds.CoversOutputValues)
    (maximal : plan.phases.IsChain fun first last =>
      first.kind ≠ last.kind ∨ first.kind = .sample)
    (ordered : (graph).RevealRelaxedOrdered)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (fullValues : ∀ who key, FullSupport (values who key))
    {length : Nat} (tape : ReservedEpoch.Tape Player length)
    (activationGap processingGap : Nat)
    (gaps : tape.BoundedGaps (ReservedEpoch.completionCycles runtime)
      activationGap processingGap)
    (margin : runtime.AsyncTimely (fun _ => activationGap + 1) (fun _ => processingGap + 1))
    (capacity : ReservedEpoch.executionHorizon runtime ≤ bounds.candidateCount)
    (remaining : Nat) (anchor : (app).Execution)
    (trace : ((menu).protocol ((inputs).map (PhaseRuntimeState.initial plan))
      (ReservedEpoch.executionHorizon runtime)
        (ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape)).Trace
          (some ⟨remaining, none, anchor⟩))
    (phase : RuntimePhase graph) (installed : phase ∈ anchor.application.phases.head?)
    (commitment : phase.kind = .commitment)
    (owner : Player) (active : owner ∉ anchor.application.current.excluded)
    (fresh : ∀ event, anchor.application.SeedRequest owner ⟨anchor.application.attempt, event⟩ →
      ¬ PhaseCount.ResponseRecorded runtime leaks owner
        ⟨anchor.application.attempt, event⟩ (anchor.recall owner)) :
    let initial := (inputs).map (PhaseRuntimeState.initial plan)
    let horizon := ReservedEpoch.executionHorizon runtime
    let scheduler := ReservedEpoch.family runtime leaks (ReservedEpoch.packetCapacity runtime) tape
    let players := ReactiveApplication.anchoredPolicy anchor
      (phaseProposalUnflaggedPolicy setup mode runtime leaks bounds plan values)
    let profile := fun who => (menu).restrictPolicy initial horizon scheduler who (players who)
    let stopped := fun history : ((menu).protocol initial horizon scheduler).History =>
      match history.state with
      | none => False
      | some control => control.execution.application.attempt ≠ anchor.application.attempt
    ∀ final ∈ (((menu).information initial horizon scheduler).runBehavioralUntil
        ((menu).bounded initial horizon scheduler).wellFoundedHistories profile stopped
          ⟨some ⟨remaining, none, anchor⟩, trace⟩).support,
      ∀ ending, final.state = some ending →
        owner ∉ ending.execution.application.current.excluded := by
  intro initial horizon scheduler players profile stopped final supported ending stateEq failed
  obtain ⟨event, _inside, request, recorded, _unaccepted⟩ :=
    phaseProposalUnflagged_stopped_exclusion_request setup mode runtime leaks bounds plan complete
      coveredValues maximal ordered values fullValues tape activationGap processingGap gaps margin
        capacity remaining anchor trace phase installed commitment owner active final supported
          ending stateEq failed
  exact fresh event request recorded

end Vegas
