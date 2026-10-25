/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletionCases
import Vegas.Pending.ExclusionEvidence

/-! # Operational origins of owned event completions -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Every scheduler move completing an owned event either consumes an actual
pending envelope of its owner or is a due expiry of that same event. -/
theorem completion_pending_or_due
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {owner : Player} (owned : (graph setup).actor? event = some owner) :
    (∃ message ∈ execution.network.pending, message.sender = owner ∧
      message.payload.call.event? (graph setup) = some event) ∨
    (command = .application (.expire event) ∧
      ∃ entered, execution.application.activatedAt event = some entered ∧
        (runtime setup).deadline event ≤ execution.application.clock - entered) := by
  rcases owned_completion_cases execution next command reached ready action member owned with
    accepted | ⟨expired, entered, activated, due, _, _⟩
  · rcases accepted with ⟨accepted⟩
    exact Or.inl ⟨accepted.message, accepted.pending, accepted.sender, accepted.named⟩
  · exact Or.inr ⟨expired, entered, activated, due⟩

/-- A new public failure at an environment move from a clear state is at that
move's actual owned graph step, so its origin is pending traffic or due expiry. -/
theorem firstPublicFailure_pending_or_due
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (clear : ExclusionEvidence 0 ∅
      (⟨execution.application, ∅⟩ : RecoveryState (graph setup)))
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (failed : next.application.PublicFailure event) :
    execution.application.config.cut.Ready event ∧
      ((∃ message ∈ execution.network.pending, message.sender = owner ∧
        message.payload.call.event? (graph setup) = some event) ∨
      (command = .application (.expire event) ∧
        ∃ entered, execution.application.activatedAt event = some entered ∧
          (runtime setup).deadline event ≤ execution.application.clock - entered)) := by
  have notFailed : ¬ execution.application.PublicFailure event := by
    intro before
    have excluded := (clear.excluded_zero owner).mpr ⟨event, owned, before⟩
    exact Finset.notMem_empty owner excluded
  have footprint := completionStep_reactive_environmentStep (runtime setup) leaks execution next
    command reached
  rcases footprint with ⟨same, accepted, _⟩ |
    ⟨completed, ready, action, member, _, acceptedOnly⟩
  · exfalso
    apply notFailed
    apply (State.PublicFailure.congr event (by rw [same]) (by rw [same]) ?_).mp failed
    rw [accepted]
  · have which : event = completed := by
      by_contra different
      apply notFailed
      exact (State.PublicFailure.of_step_of_ne member
        (fun field changed => (acceptedOnly field changed).2) different).mp failed
    subst completed
    exact ⟨ready, completion_pending_or_due execution next command reached ready action member
      owned⟩

end Vegas
