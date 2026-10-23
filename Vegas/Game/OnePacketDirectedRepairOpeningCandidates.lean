/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDirectedRepairOpeningTrace
import Vegas.Game.OnePacketSwapGuardSite
import Vegas.Pending.ReactiveBindingSubmittedResponse

/-! # Authentic signed opening candidates survive directed repair -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- The certificate emitted by an actual opening names its true current
candidate value, including certificates obtained by forwarding. -/
theorem onePacket_opening_candidate
    {control : (application setup leaks).Control}
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (who : Player) (material : WitnessedSubmission (graph setup))
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (packet : material.call.packet = .opening event candidate raw)
    (certified : ((runtime setup).localEnvelope leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) material).payload.evidence =
        some ⟨candidate, raw⟩) :
    control.execution.application.candidates.lookup candidate = .openable raw := by
  let app := application setup leaks
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler prior
  have count := (runtime setup).countRecall_history leaks rawTrace
  have sound : ((runtime setup).packetEvidence leaks).Sound control.execution :=
    ((runtime setup).packetEvidence leaks).history_sound (initialLaw setup) horizon scheduler
      rawTrace
  have unchanged : app.submit control.execution.application who material =
      control.execution.application := by
    rcases material with ⟨⟨submitted, opening⟩, evidence⟩
    dsimp only at packet
    subst submitted
    cases opening <;> rfl
  have envelope := (runtime setup).localEnvelope_eq_of_recall leaks control.execution count.1
    count.2.1 who material
  have emitted := (congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
    message.payload.evidence) envelope).symm.trans certified
  rw [unchanged] at emitted
  exact material.emit_sound control.execution.application who (control.execution.network.known who)
    (fun message member fact evidence => sound.known who message member fact (by
      simp only [packetEvidence, evidence, Option.toList_some, List.mem_singleton]))
    ⟨candidate, raw⟩ emitted

namespace DirectedBindingFrame

/-- Signed opening handles have the same authentic raw value after repair.
Output handles use the original-success part of the submitted-binding records;
initial handles use the actual initialized binding invariant. -/
theorem opening_candidate_of_signed
    {memory : BindingMemory (runtime setup) leaks} {owner : Player}
    {original repaired : (application setup leaks).Control}
    (frame : DirectedBindingFrame memory owner original.execution repaired.execution)
    (recorded : memory.RecordsSubmittedBindings (runtime setup) leaks owner
      original.execution repaired.execution)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some original))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some repaired))
    (material : WitnessedSubmission (graph setup))
    {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (candidate : Handle (graph setup)) (value : L.Val payload)
    (leftFixed : original.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (signed : SignedBinding
      (EarlierOwnPacket ((application setup leaks).outputs (original.execution.recall owner))
        ((runtime setup).localEnvelope leaks owner (original.execution.recall owner)
          (original.execution.observe (application setup leaks) owner) material))
      owner candidate binding.field) :
    candidate.1 = owner ∧ repaired.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩ := by
  have rawTrace := (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup)
    horizon scheduler prior
  have count := (runtime setup).countRecall_history leaks rawTrace
  have clean := (bounds.onePacketMenu_countClean (runtime setup) leaks scheduler).history
    (initialLaw setup) horizon (fun state _ => (runtime setup).countClean_initial leaks state) prior
  cases field : binding.field with
  | inl input =>
      simp only [SignedBinding, field] at signed
      subst candidate
      have layoutEq : (graph setup).inputLayout input = .binding owner payload := by
        simpa only [field, EventGraph.layout, EventGraph.fieldLayout, Sum.elim_inl,
          Sum.elim_inr] using binding.layout_eq
      have accepted := accepted_initial_of_trace prior layoutEq
      have valid := bindingInvariant_of_history bounds horizon scheduler ⟨some original, prior⟩ rfl
      have validImage := bindingInvariant_of_history bounds horizon scheduler
        ⟨some repaired, imagePrior⟩ rfl
      have stored := valid.opening_stored binding (owner, .initial input) value
        (by simpa only [field] using accepted) leftFixed
      obtain ⟨_, found, associated, _, _, _, rightFixed⟩ :=
        frame.toFrame.successful_opening valid validImage binding value stored
      have same : found = (owner, .initial input) :=
        Option.some.inj (associated.symm.trans (by simpa only [field] using accepted))
      subst found
      exact ⟨rfl, rightFixed⟩
  | inr event =>
      simp only [SignedBinding, field] at signed
      obtain ⟨message, earlier, call⟩ := signed
      have input : message ∈ original.execution.network.inputs := by
        have output := earlier.1
        rw [← count.1 owner] at output
        exact (List.mem_filter.mp output).1
      have sender : message.sender = owner := earlier.2.1
      have correct := ((countPermits_eq_true_iff _ _).mp (clean.2 message input)).2.1
      unfold CountCallCorrect at correct
      rw [call] at correct
      have owned := correct.2.2.1.trans sender
      have outputEq : (graph setup).outputLayout event = .binding owner payload := by
        simpa only [field, EventGraph.layout, EventGraph.fieldLayout, Sum.elim_inl,
          Sum.elim_inr] using binding.layout_eq
      have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = .bind owner payload := by
        generalize cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event) = code
        cases code
        rfl
      have node := nodeView_eq_bind outputEq codeEq
      obtain ⟨_, _, _, _, successes⟩ := recorded message input sender event candidate call payload
        outputEq codeEq node
      have originalSuccess := (State.bindingResult_eq_success_iff original.execution.application
        candidate payload value).mpr leftFixed
      exact ⟨owned, (State.bindingResult_eq_success_iff repaired.execution.application candidate
        payload value).mp (successes value originalSuccess)⟩

end DirectedBindingFrame

end Vegas
