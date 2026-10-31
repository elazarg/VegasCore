/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletion

/-! # Accepted, expired and automatic owned completion records

A new owned record comes from an accepted packet, a due expiry, or automatic
service of a defaulted owner. Expiry preserves the complete accepted table;
automatic records retain their actual native origin and silent metadata even
when the command's primary acceptance changed another event's table entry.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}

/-- Accepted packets supply the decoded actual decision. Both expiry and
automatic service have failing decoded records; only expiry asserts global
accepted-table equality across the complete physical command. -/
theorem completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup runtime leaks).Execution)
    (command : (application setup runtime leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup runtime leaks) command).support)
    (record : (graph setup).Completion) (fresh : record ∉ execution.application.config.history)
    (present : record ∈ next.application.config.history)
    {actor : Player} (acts : (graph setup).actor? record.event = some actor) :
    (∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some record.event ∧
      record.decision.bind (decodeEventAction setup.program record.event) =
        callContent setup execution.application message.payload.call ∧
      (∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor) ∧
      ∀ owner payload, (graph setup).outputLayout record.event = .binding owner payload →
        next.application.accepted (.inr record.event) ≠ none) ∨
    (next.application.accepted = execution.application.accepted ∧
      Failing (record.decision.bind (decodeEventAction setup.program record.event))) ∨
    (Failing (record.decision.bind (decodeEventAction setup.program record.event)) ∧
      ∃ native, native.drain = next.application ∧ record ∉ native.config.history ∧
        ((∃ message ∈ execution.network.pending, command = .include message.id ∧
            handle runtime execution.application ⟨message.id, message.payload.call⟩ = some native) ∨
          ∃ operation, command = .application operation ∧
            native ∈ (environmentStep runtime execution.application operation).support) ∧
        record.decision = none ∧ record.defaultEvent = none ∧ actor ∈ native.config.defaulted) := by
  rcases owned_completion_cases execution next command reached record fresh present acts with
    accepted | expired | automatic
  · rcases accepted with ⟨accepted⟩
    exact Or.inl ⟨accepted.message, accepted.ledger,
      accepted.sender, accepted.named,
      accepted.content, accepted.candidateOwner,
        accepted.bindingAccepted⟩
  · obtain ⟨expiredCommand, entered, activated, due, action, value, expired, recorded⟩ := expired
    have table : next.application.accepted = execution.application.accepted := by
      rw [expiredCommand] at reached
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact (reactiveApplication_environment_tables runtime leaks execution.application state
        (.expire record.event) changed).1
    have decision := eq_of_heq (EventGraph.Completion.mk.inj recorded).2.1
    have failed : Failing
        (record.decision.bind (decodeEventAction setup.program record.event)) := by
      rw [decision]
      exact expired_record_failing execution.application.config expired
    exact Or.inr (Or.inl ⟨table, failed⟩)
  · have silent : record.decision = none := by
      obtain ⟨native, drained, freshNative, trigger, silent, unchanged, inactive⟩ := automatic
      exact silent
    have failed : Failing
        (record.decision.bind (decodeEventAction setup.program record.event)) := by
      rw [silent, Option.bind_none]
      simp [Failing, OwnAction.disclosure]
    exact Or.inr (Or.inr ⟨failed, automatic⟩)

end Vegas
