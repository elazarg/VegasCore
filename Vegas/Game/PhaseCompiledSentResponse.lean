/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePolicy
import Vegas.Pending.PhaseSentMenu
import Vegas.Pending.PhaseNativePlayerInput
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.PhaseBindingIdleMenu
import Vegas.Pending.PhaseReadyRequests
import Vegas.Pending.PhasePlanSuffix

/-! # Complete compiled and canonical responses after authentic transmission -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem prescribed_silent_of_submitted {graph : Vegas.EventGraph Player L}
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (event : graph.EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (submitted : runtime.reactiveAlreadySubmitted leaks past event = true) :
    runtime.prescribedReactivePolicy leaks who policy past view = PMF.pure ⟨none⟩ := by
  apply pmf_eq_pure_of_support_subset_singleton
  intro action positive
  rw [runtime.prescribedReactivePolicy_apply] at positive
  obtain ⟨intentions, _supported, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ positive)
  have blocked : runtime.prescribedReactiveResponse leaks who policy past intentions view =
      PMF.pure (⟨none⟩, none) := by
    simp only [prescribedReactiveResponse, turn, submitted, Bool.true_or, ↓reduceIte]
  rw [blocked, PMF.pure_map] at produced
  exact (PMF.mem_support_pure_iff _ _).mp produced

/-- A genuine previously transmitted current coordinate forces BOTH complete
response policies to silence. Native private-memory consistency is unnecessary
because its submitted-event flag already blocks resampling. -/
theorem phaseSourcePolicy_prescribed_of_sent
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (who : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
    (event : (serviceGraph setup mode).EventId)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (sent : ∃ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
      PhaseSeedScheduler.ownPacket ⟨execution.application.attempt, event⟩ who message = true)
    (policy : (serviceGraph setup mode).BehavioralPolicy who) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) who policy
        ((PhaseNativeProjection.execution runtime leaks plan execution).recall who)
        ((PhaseNativeProjection.execution runtime leaks plan execution).observe
          (runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)) who) := by
  let nativeLeaks := PhaseNativeProjection.nativeLeaks leaks plan
  let projected := PhaseNativeProjection.execution runtime leaks plan execution
  have singleton := PhaseCount.onePacketActions_eq_singleton_of_sent runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler remaining who execution
      trace ⟨execution.application.attempt, event⟩ request sent
  have canonical : phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
        PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro response positive
    have offered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
      who _ _ response positive
    rw [singleton] at offered
    exact Finset.mem_singleton.mp offered
  obtain ⟨message, member, addressed⟩ := sent
  have named : message.payload.packet.call.event? (serviceGraph setup mode) = some event :=
    (of_decide_eq_true addressed).2.2
  have nativeMember : message.mapPayload CommitAttemptPacket.packet ∈
      (runtime.reactiveApplication nativeLeaks).outputs (projected.recall who) := by
    change message.mapPayload CommitAttemptPacket.packet ∈
      (runtime.reactiveApplication nativeLeaks).outputs
        ((execution.recall who).map (PhaseNativeProjection.playerEntry runtime leaks plan))
    rw [PhaseNativeProjection.outputs runtime leaks plan]
    exact List.mem_map.mpr ⟨message, member, rfl⟩
  have submitted := (runtime.reactiveAlreadySubmitted_iff nativeLeaks (projected.recall who)
    event).mpr (runtime.reactiveSubmittedEvents_mem nativeLeaks (projected.recall who)
      (message.mapPayload CommitAttemptPacket.packet) event nativeMember named)
  have turn := execution.application.current.native.ownTurn_of_ready
    (serviceGraph_revealRelaxedOrdered setup mode) who event
    ((execution.application.current.native.publicView_eventReady event).mpr request.2.2.1)
    request.2.2.2.1
  have selected := execution.application.current.native.publicView.ownTurn?_of_ownTurn who
    event turn
  have native := prescribed_silent_of_submitted runtime nativeLeaks who policy
    (projected.recall who) (projected.observe (runtime.reactiveApplication nativeLeaks) who)
      event selected submitted
  rw [canonical, PMF.pure_map, native]
  rfl

/-- At an actual clear callback with no current request the canonical counted
menu and the native prescribed policy are both exactly silent. -/
theorem phaseSourcePolicy_prescribed_of_no_request
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (who : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
    (clear : execution.application.current.excluded = ∅)
    (absent : ∀ coordinate, ¬execution.application.SeedRequest who coordinate)
    (policy : (serviceGraph setup mode).BehavioralPolicy who) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      runtime.prescribedReactivePolicy (PhaseNativeProjection.nativeLeaks leaks plan) who policy
        ((PhaseNativeProjection.execution runtime leaks plan execution).recall who)
        ((PhaseNativeProjection.execution runtime leaks plan execution).observe
          (runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)) who) := by
  let nativeLeaks := PhaseNativeProjection.nativeLeaks leaks plan
  let projected := PhaseNativeProjection.execution runtime leaks plan execution
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler
    trace
  have living := (phaseApplication_live runtime leaks).history initial horizon scheduler
    (fun state supported => by
      obtain ⟨input, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨PhaseRuntimeState.initial_frontier plan input,
        PhaseRuntimeState.initial_live plan input⟩) raw
  have geometry := phasePlanGeometry_history runtime leaks plan maximal inputs horizon scheduler raw
  have quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event := by
    intro event eligible
    rcases eligible with ⟨_ready, excluded⟩
    cases acting : (serviceGraph setup mode).actor? event with
    | none => simp only [acting] at excluded
    | some owner =>
        rw [acting] at excluded
        change owner ∈ execution.application.current.excluded at excluded
        rw [clear] at excluded
        exact Finset.notMem_empty _ excluded
  have idle : execution.application.current.native.publicView.Idle who := by
    intro event ready acting
    apply absent ⟨execution.application.attempt, event⟩
    exact execution.application.request_of_ready (serviceGraph_revealRelaxedOrdered setup mode)
      living.1 living.2 geometry.2.2 quiescent event
        ((execution.application.current.native.publicView_eventReady event).mp ready) who acting
  have selected := execution.application.current.native.publicView.ownTurn?_eq_none who idle
  have selectedView :
      ((projected.observe (runtime.reactiveApplication nativeLeaks)
        who).application.publicView).ownTurn? who = none := selected
  have native : runtime.prescribedReactivePolicy nativeLeaks who policy (projected.recall who)
      (projected.observe (runtime.reactiveApplication nativeLeaks) who) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro action positive
    rw [runtime.prescribedReactivePolicy_apply] at positive
    obtain ⟨intentions, _supported, produced⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ positive)
    have blocked : runtime.prescribedReactiveResponse nativeLeaks who policy
        (projected.recall who) intentions
        (projected.observe (runtime.reactiveApplication nativeLeaks) who) =
          PMF.pure (⟨none⟩, none) := by
      simp only [prescribedReactiveResponse, selectedView]
    rw [blocked, PMF.pure_map] at produced
    exact (PMF.mem_support_pure_iff _ _).mp produced
  have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds
    plan inputs horizon scheduler remaining who execution trace clear absent
  have canonical : phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) =
        PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro response positive
    have offered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment
      who _ _ response positive
    rw [singleton] at offered
    exact Finset.mem_singleton.mp offered
  rw [canonical, PMF.pure_map, native]
  rfl

end Vegas
