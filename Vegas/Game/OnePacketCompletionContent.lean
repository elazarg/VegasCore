/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketActorRecord
import Vegas.Pending.ReactiveAcceptedOutput

/-! # The content of a completing packet

**Call content.** The *content* of a call at a contract state is the source
action it decodes to there: for a commitment, the commitment of the value its
handle binds, at any slot; for an opening, the disclosure; nothing for a
malformed call (`Vegas.callContent`). The source action a response transmits,
read when it is sent, is the content of its call at the state after the
submission (`Vegas.sentSourceAction_eq_callContent`). The content of a call
stays the same while the meaning of its handle is fixed
(`Vegas.callContent_keep`).

**Completion content.** A scheduler round completing an event with an actor by
a decoded action that is not failing includes an accepted packet of that actor
naming the event; the decoded action is the content of the packet's call at the
state it is included at, and a commitment's handle belongs to the actor
(`Vegas.completion_content`). Intended actions are never failing
(`Vegas.SourceProgram.ProtocolView.not_failing_of_intendedAvailable`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolView

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Intended actions are not failing.** An intended commitment commits a
value, and an intended reveal discloses. -/
theorem not_failing_of_intendedAvailable (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (view : ProtocolView who program) → (action : OwnAction Player L) →
    action ∈ intendedAvailable who program view → ¬ Failing (some action)
  | _, _, .ret _, _, _, impossible => impossible.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := member
          intro failing
          cases failing.1 _ _ _ _ rfl
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          rw [Set.mem_singleton_iff.mp member]
          intro failing
          cases failing.2
      | inr later => exact not_failing_of_intendedAvailable who next later action member

end Vegas.SourceProgram.ProtocolView

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

/-- **Completion content.** A scheduler round completing an event with an
actor by a decoded action that is not failing includes an accepted packet of
the actor naming the event. The decoded action is the content of the packet's
call at the state it is included at, and a commitment's handle belongs to the
actor. -/
theorem completion_content
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    {event : (graph setup).EventId} (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (member : next.application.config ∈
      (execution.application.config.step event ready action).support)
    {actor : Player} (acts : (graph setup).actor? event = some actor)
    (notFailing : ¬ Failing (decodeEventAction setup.program event action)) :
    ∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some event ∧
      decodeEventAction setup.program event action =
        callContent setup execution.application message.payload.call ∧
      ∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor := by
  rcases owned_completion_cases (runtime := runtime) execution next command reached ready action
    member acts with
    accepted | ⟨_, _, _, _, _, expired⟩
  · rcases accepted with ⟨accepted⟩
    exact ⟨accepted.message, accepted.ledger,
      accepted.sender, accepted.named,
      accepted.content, accepted.candidateOwner⟩
  · exact (notFailing (expiredAction_failing expired)).elim

end Vegas
