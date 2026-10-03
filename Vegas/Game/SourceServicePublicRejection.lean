/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceSettledEvidence

/-! # Public rejection persists until event completion

A completed event cannot accept another packet. While an event is ready,
sequential readiness prevents another event from changing its public handler
conditions. Wrong resolution handle ownership or public binding association
therefore prevents any future accepting receipt for a newly emitted packet.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph
  GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private def publiclyBlocked (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (state : EventGraphRuntime.State (graph setup)) : Prop :=
  event ∈ state.config.cut.completed ∨
    (state.config.cut.Ready event ∧ ¬ PublicConditions setup state message.payload.call)

private theorem publiclyBlocked_step
    {before after : EventGraphRuntime.State (graph setup)}
    (step : ContractStep before after) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (held : publiclyBlocked event message before) : publiclyBlocked event message after := by
  rcases held with completed | ⟨ready, blocked⟩
  · exact Or.inl (step.completed_mono completed)
  · rcases step with ⟨configEq, acceptedEq, activatedEq, clockLe⟩ |
        ⟨other, otherReady, action, supported⟩
    · exact Or.inr ⟨configEq ▸ ready, fun holds => blocked
        (publicConditions_of_later before after acceptedEq activatedEq clockLe _ holds)⟩
    · cases ready_unique before.config.cut otherReady ready
      left
      rw [before.config.step_cut event otherReady action after.config supported]
      exact (EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl rfl)

private theorem publiclyBlocked_respond
    (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (held : publiclyBlocked event message execution.application) :
    publiclyBlocked event message
      (execution.respond (application setup leaks) who response).application := by
  obtain ⟨configEq, publicEq⟩ :=
    (runtime setup).reactive_respond_application leaks execution who response
  apply publiclyBlocked_step (Or.inl ⟨configEq, congrArg PublicView.accepted publicEq,
    congrArg PublicView.activatedAt publicEq,
    le_of_eq (congrArg PublicView.clock publicEq).symm⟩) event message held

private def blockedPacketFacts (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (execution : (application setup leaks).Execution) : Prop :=
  SettledFacts setup leaks execution ∧ publiclyBlocked event message execution.application ∧
    (Emitted setup leaks execution message → (message.id, true) ∉ execution.receipts)

private theorem blockedPacketFacts_respond
    (execution : (application setup leaks).Execution) (who : Player)
    (response : (application setup leaks).Action) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (held : blockedPacketFacts event message execution) :
    blockedPacketFacts event message
      (execution.respond (application setup leaks) who response) := by
  let app := application setup leaks
  refine ⟨settledFacts_respond execution held.1 who response,
    publiclyBlocked_respond execution who response event message held.2.1, ?_⟩
  intro emitted
  rcases respond_emitted held.1 who response message emitted with prior | ⟨material, _, same⟩
  · rw [app.respond_receipts]
    exact held.2.2 prior
  · have unaccepted : (message.id, true) ∉ (execution.respond app who response).receipts := by
      rw [app.respond_receipts]
      intro receipt
      obtain ⟨other, member, identified⟩ := List.mem_map.mp (held.1.receipt_published receipt)
      have lower := held.1.serials.ledger other member
      rw [identified, same] at lower
      exact Nat.lt_irrefl _ lower
    exact unaccepted

private theorem blockedPacketFacts_environment
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : message.payload.call.event? (graph setup) = some event)
    (held : blockedPacketFacts event message execution) :
    blockedPacketFacts event message next := by
  have step := contractStep_environment (runtime setup) leaks execution next command reached
  obtain ⟨inputsEq, _, _⟩ := environmentStep_shape setup leaks execution next command reached
  refine ⟨settledFacts_environment execution next command held.1 reached,
    publiclyBlocked_step step event message held.2.1, ?_⟩
  intro emitted
  have prior : Emitted setup leaks execution message := by
    unfold Emitted at emitted ⊢
    rw [inputsEq] at emitted
    exact emitted
  intro accepted
  obtain ⟨state, handled, _⟩ := newly_accepted held.1 reached prior (held.2.2 prior) accepted
  obtain ⟨_, actual, addressed, ready, _, _⟩ :=
    accepted_inclusion execution.application state message handled
  rw [named] at addressed
  cases Option.some.inj addressed
  rcases held.2.1 with completed | ⟨_, blocked⟩
  · exact ready.1 completed
  · exact blocked (handle_publicConditions execution.application state message.id
      message.payload.call (reactiveHandle_call handled))

private def blockedPacketAtState (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup))) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => blockedPacketFacts event message control.execution

private theorem blockedPacketAtState_transition
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : message.payload.call.event? (graph setup) = some event)
    (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (held : blockedPacketAtState event message before)
    (reached : after ∈ ((application setup leaks).transition (initialLaw setup) horizon
      scheduler before joint).support) : blockedPacketAtState event message after := by
  cases before with
  | none => exact held.elim
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          exact blockedPacketFacts_respond execution who _ event message held
      | none =>
          cases remaining with
          | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact held
          | succ remaining =>
              obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
              exact blockedPacketFacts_environment execution next command supported event
                message named held

private theorem blockedPacketAtState_reaches
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {first last :
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin
      fuel first last) (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (named : message.payload.call.event? (graph setup) = some event)
    (held : blockedPacketAtState event message first.state) :
    blockedPacketAtState event message last.state := by
  induction path with
  | refl => exact held
  | step joint legal reached rest ih =>
      exact ih (blockedPacketAtState_transition event message named _ _ joint held reached)

/-- Actual public impossibility at a ready event, or its prior completion,
prevents a fresh packet from ever acquiring an accepting receipt. -/
theorem publiclyBlockedPacket_not_accepted_reaches
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {first last :
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (application setup leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (blocked : event ∈ before.execution.application.config.cut.completed ∨
      (before.execution.application.config.cut.Ready event ∧
        ¬ PublicConditions setup before.execution.application message.payload.call))
    (named : message.payload.call.event? (graph setup) = some event)
    (fresh : message.id = (message.sender, before.execution.network.nextSerial message.sender))
    (emitted : Emitted setup leaks after.execution message) :
    (message.id, true) ∉ after.execution.receipts := by
  have initial : blockedPacketAtState event message first.state := by
    rw [firstState]
    have facts := settledFacts_history (initialLaw setup) horizon scheduler
      (firstState ▸ first.trace)
    refine ⟨facts, blocked, ?_⟩
    intro prior
    have lower := facts.emitted_serial prior
    rw [fresh] at lower
    exact (Nat.lt_irrefl _ lower).elim
  have final := blockedPacketAtState_reaches path event message named initial
  rw [lastState] at final
  exact final.2.2 emitted

/-- Complete play turns the derived absence of an accepting receipt into the
actual final settled verdict, without a send-time audit predicate. -/
theorem publiclyBlockedPacket_forbidden_reaches
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {first last :
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (application setup leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup)))
    (blocked : event ∈ before.execution.application.config.cut.completed ∨
      (before.execution.application.config.cut.Ready event ∧
        ¬ PublicConditions setup before.execution.application message.payload.call))
    (named : message.payload.call.event? (graph setup) = some event)
    (fresh : message.id = (message.sender, before.execution.network.nextSerial message.sender))
    (emitted : Emitted setup leaks after.execution message)
    (complete : after.execution.application.config.cut.Terminal) :
    ((runtime setup).settledRecord leaks after.execution).permits message = false := by
  have unaccepted := publiclyBlockedPacket_not_accepted_reaches path before after firstState
    lastState event message blocked named fresh emitted
  apply SettledRecord.permits_eq_false_of_settled
    ((runtime setup).settledRecord leaks after.execution) message event named ?_
    (fun accepted => unaccepted accepted.1)
  apply (after.execution.application.config.history_exact event).mpr
  rw [complete]
  exact Finset.mem_univ event

/-- Wrong handle ownership or the wrong public binding association fails the
runtime's actual public conditions independently of certificate authenticity
and public guard success. -/
theorem wrongOpeningAssociation_publicConditions
    (state : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (wrong : candidate.1 ≠ owner ∨ state.publicView.accepted binding.field ≠ some candidate) :
    ¬ PublicConditions setup state (.opening event candidate raw) := by
  intro conditions
  simp only [PublicConditions, node] at conditions
  rcases wrong with ownerWrong | associationWrong
  · exact ownerWrong conditions.2.1
  · exact associationWrong conditions.2.2.1

/-- A fresh opening of a ready resolution using the wrong owner or accepted
handle is forbidden after every complete continuation. Neither a hidden-value
premise nor a promised final rejection is supplied by the caller. -/
theorem wrongAssociationOpening_forbidden_reaches
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {first last :
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).ReachesWithin
      fuel first last)
    (before after : (application setup leaks).Control)
    (firstState : first.state = some before) (lastState : last.state = some after)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (ready : before.execution.application.config.cut.Ready event)
    (message : Message Player (WitnessedPacket (graph setup)))
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opened : message.payload.call = .opening event candidate raw)
    (wrong : candidate.1 ≠ owner ∨
      before.execution.application.publicView.accepted binding.field ≠ some candidate)
    (fresh : message.id = (message.sender, before.execution.network.nextSerial message.sender))
    (emitted : Emitted setup leaks after.execution message)
    (complete : after.execution.application.config.cut.Terminal) :
    ((runtime setup).settledRecord leaks after.execution).permits message = false := by
  apply publiclyBlockedPacket_forbidden_reaches path before after firstState lastState event
    message (Or.inr ⟨ready, ?_⟩) ?_ fresh emitted complete
  · rw [opened]
    exact wrongOpeningAssociation_publicConditions before.execution.application event owner payload
      binding checks outputEq codeEq node candidate raw wrong
  · rw [opened]
    rfl

end Vegas
