module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketCompletionCases

@[expose] public section

/-! # The content of a completing packet

**Call content.** The *content* of a call at a contract state is the source
action it decodes to there: for a commitment, the commitment of the value its
handle binds, at any slot; for an opening, the disclosure; nothing for a
malformed call (`Vegas.callContent`). The source action a response transmits,
read when it is sent, is the content of its call at the state after the
submission (`Vegas.sentSourceAction_eq_callContent`). The content of a call
stays the same while the meaning of its handle is fixed
(`Vegas.callContent_keep`).

**Completion content.** A newly appended owned record with non-failing decoded
actual decision comes from an accepted packet of its actor. Its source content
is the content of that packet at inclusion, and its commitment handle is owned
(`Vegas.completion_content`). Intended actions are never failing
(`Vegas.SourceProgram.ProtocolView.not_failing_of_intendedAvailable`).
-/

noncomputable section
namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- Every non-failing newly recorded owned decision has an accepted packet
with matching source content and candidate ownership, even when its physical
command also performs further automatic completions. -/
theorem completion_content
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (record : (graph setup).Completion) (fresh : record ∉ execution.application.config.history)
    (present : record ∈ next.application.config.history)
    {actor : Player} (acts : (graph setup).actor? record.event = some actor)
    (notFailing : ¬ Failing
      (record.decision.bind (decodeEventAction setup.program record.event))) :
    ∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some record.event ∧
      record.decision.bind (decodeEventAction setup.program record.event) =
        callContent setup execution.application message.payload.call ∧
      ∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor := by
  rcases completion_cases execution next command reached record fresh present acts with
    ⟨message, ledger, sender, named, content, owner, _binding⟩ |
    ⟨_table, failed⟩ | ⟨failed, _origin⟩
  · exact ⟨message, ledger, sender, named, content, owner⟩
  · exact (notFailing failed).elim
  · exact (notFailing failed).elim

end Vegas
