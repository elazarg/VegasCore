/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCandidateSupply
import Vegas.Pending.ReactiveSignedCommitments
import Vegas.Pending.EventCommitmentBinding

/-! # Own emitted commitments remain fixed across every physical attempt

A globally fresh handle has never appeared in an earlier own commitment,
including a packet from an attempt whose semantic outputs were rolled back.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Every fixed physical catalogue entry remains fixed through submission,
acceptance, automatic completion, next-phase installation, and retry. -/
theorem phaseApplication_fixesCandidates :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      FixesCandidates before.current.native after.current.native) where
  refl _ _ fixed := fixed
  submit state who material candidate fixed := by
    change (submitStep (material.call.register state.current.native who) who
      material.call.packet).candidates.lookup candidate ≠ .fresh
    have registered := material.call.register_lookup_of_not_fresh state.current.native who
      candidate fixed
    rw [submitStep_lookup_of_not_fresh _ _ _ _ (by rwa [registered]), registered]
    exact fixed
  handle state message next accepted candidate fixed := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change (PhaseRuntimeState.settle _ _ _ _ _).current.native.candidates.lookup candidate ≠ _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      change native.candidates.lookup candidate ≠ .fresh
      rw [handle_lookup_of_not_fresh runtime state.current.native native
        ⟨message.id, message.payload.packet.call⟩ candidate fixed handled]
      exact fixed
    · cases accepted
  environment state command next reached candidate fixed := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := PMF.support_map .. ▸ reached
      change (PhaseRuntimeState.settle _ _ _ _ _).current.native.candidates.lookup candidate ≠ _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      change native.candidates.lookup candidate ≠ .fresh
      rw [(environmentStep_tables runtime _ _ command supported).2]
      exact fixed
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact fixed

/-- Actual own signed commitments have fixed their own candidate permanently. -/
def PhaseOwnCommitmentsFixed (execution : (phaseApplication runtime leaks).Execution) : Prop :=
  ∀ who, ∀ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
    ∀ event slot, message.payload.packet.call = .commitment event (who, slot) →
      execution.application.current.native.candidates.lookup (who, slot) ≠ .fresh

theorem PhaseOwnCommitmentsFixed.respond
    {execution : (phaseApplication runtime leaks).Execution}
    (valid : PhaseOwnCommitmentsFixed runtime leaks execution) (who : Player)
    (action : (phaseApplication runtime leaks).Action) :
    PhaseOwnCommitmentsFixed runtime leaks
      (execution.respond (phaseApplication runtime leaks) who action) := by
  let app := phaseApplication runtime leaks
  have fixes := (phaseApplication_fixesCandidates runtime leaks).respond execution who action
  intro observer message member event slot call
  obtain ⟨entry, entryMember, emitted⟩ := List.mem_filterMap.mp member
  have recallEq : (execution.respond app who action).recall observer =
      if observer = who then execution.recall who ++
        [⟨execution.observe app who, action, action.transmission.map fun material =>
          ⟨(who, execution.network.nextSerial who), app.packet
            (app.submit execution.application who material) who
              (execution.network.known who) material⟩⟩]
      else execution.recall observer := by
    rcases action with ⟨_ | material⟩ <;> rfl
  rw [recallEq] at entryMember
  split at entryMember
  · rename_i same
    subst same
    rcases List.mem_append.mp entryMember with old | new
    · exact fixes _ (valid observer message (List.mem_filterMap.mpr ⟨entry, old, emitted⟩)
        event slot call)
    · obtain rfl := List.mem_singleton.mp new
      rcases action with ⟨_ | material⟩
      · cases emitted
      · cases Option.some.inj emitted
        change (submitStep (material.call.register execution.application.current.native observer)
          observer material.call.packet).candidates.lookup (observer, slot) ≠ .fresh
        have emittedCall := phase_emit_call
          (execution.application.submit observer material) observer
          (execution.network.known observer) material
        change ((execution.application.submit observer material).emit observer
          (execution.network.known observer) material).packet.call = _ at call
        rw [emittedCall] at call
        rw [call]
        exact submitStep_commitment_fixed _ observer event slot
  · exact fixes _ (valid observer message (List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩)
      event slot call)

theorem PhaseOwnCommitmentsFixed.environmentStep
    {execution next : (phaseApplication runtime leaks).Execution}
    (valid : PhaseOwnCommitmentsFixed runtime leaks execution)
    (command : (phaseApplication runtime leaks).Command)
    (reached : next ∈
      (execution.environmentStep (phaseApplication runtime leaks) command).support) :
    PhaseOwnCommitmentsFixed runtime leaks next := by
  have same := (phaseApplication runtime leaks).environmentStep_recall
    execution next command reached
  have fixes := (phaseApplication_fixesCandidates runtime leaks).environmentStep
    execution next command reached
  intro who message member event slot call
  rw [same] at member
  exact fixes _ (valid who message member event slot call)

/-- Every actual raw history retains own fixed-handle provenance, regardless
of the initial semantic state, the scheduler, and earlier arbitrary responses. -/
theorem phaseOwnCommitmentsFixed_history
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) :
    ∀ {state} (_trace : ((phaseApplication runtime leaks).protocol
      initial horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant (PhaseOwnCommitmentsFixed runtime leaks) state := by
  have invariant : (phaseApplication runtime leaks).ServiceInvariant scheduler
      (PhaseOwnCommitmentsFixed runtime leaks) := {
    respond := fun _ _ _ valid => valid.respond runtime leaks _ _
    environment := fun _ _ _ valid _ reached => valid.environmentStep runtime leaks _ reached }
  intro state trace
  exact invariant.history initial horizon
    (fun _ _ _ _ member => (List.not_mem_nil member).elim) trace

end Vegas.EventGraphRuntime
