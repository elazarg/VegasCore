/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketAcceptedTable

/-! # The two ways an event with an actor completes

A scheduler round completing an event with an actor either includes an
accepted packet of the actor naming the event, whose call content at the state
it is included at is the decoded action, or is a contract command, an expiry,
that keeps the table of accepted handles and decodes to a failing action
(`Vegas.completion_cases`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}

/-- **The two ways an actor completes.** A scheduler round completing an
event with an actor either includes an accepted packet of the actor naming the
event, whose call content at the state it is included at is the decoded
action, or is a contract command that keeps the accepted handles and whose
decoded action is failing. -/
theorem completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor) :
    (∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some event ∧
      decodeEventAction setup.program event action =
        callContent setup execution.application message.payload.call ∧
      (∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor) ∧
      ∀ owner payload, (graph setup).outputLayout event = .binding owner payload →
        next.application.accepted (.inr event) ≠ none) ∨
    (next.application.accepted = execution.application.accepted ∧
      Failing (decodeEventAction setup.program event action)) := by
  rcases owned_completion_cases execution next command reached ready action member acts with
    accepted | ⟨_, _, _, _, table, expired⟩
  · rcases accepted with ⟨accepted⟩
    exact Or.inl ⟨accepted.message, accepted.ledger, accepted.sender, accepted.named,
      accepted.content, accepted.candidateOwner, accepted.bindingAccepted⟩
  · exact Or.inr ⟨table, expiredAction_failing expired⟩

end Vegas
