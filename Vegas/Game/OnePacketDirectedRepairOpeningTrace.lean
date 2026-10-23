/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairResponderTrace
import Vegas.Pending.ReactiveBindingGuardedStep
import Vegas.Game.OnePacketDirectedRepairMenu

/-! # Actual unchanged opening traces through directed binding repair

An authentic candidate that is unchanged by repair has the same normalized
opening response on both sides. Bounded availability transports by the actual
known envelopes, and count permission transports by the before/after network
identity. The repaired trace is therefore an actual one-packet trace with the
same complete operational record.
-/

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

namespace DirectedBindingFrame

variable {memory nextMemory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

omit [Fintype Player] in
private theorem opening_countPermits
    (frame : DirectedBindingFrame memory owner original repaired)
    (originalCount : (runtime setup).CountRecall leaks original)
    (repairedCount : (runtime setup).CountRecall leaks repaired)
    (material : WitnessedSubmission (graph setup))
    (after : BindingMemory.Frame (runtime setup) leaks nextMemory owner
      (original.respond (application setup leaks) owner ⟨some material⟩)
      (repaired.respond (application setup leaks) owner ⟨some material⟩))
    (permitted : (runtime setup).OnePacketResponse leaks owner (original.recall owner)
      (original.observe (application setup leaks) owner) ⟨some material⟩) :
    (runtime setup).OnePacketResponse leaks owner (repaired.recall owner)
      (repaired.observe (application setup leaks) owner) ⟨some material⟩ := by
  have inputs := congrArg (fun net => net.inputs) after.network
  have first := ((runtime setup).countPermits_respond leaks original originalCount owner
    material).1
  have second := ((runtime setup).countPermits_respond leaks repaired repairedCount owner
    material).1
  change (original.respond (application setup leaks) owner ⟨some material⟩).network.inputs =
    (repaired.respond (application setup leaks) owner ⟨some material⟩).network.inputs at inputs
  rw [first, second, frame.network] at inputs
  have envelope := List.singleton_inj.mp (List.append_cancel_left inputs)
  obtain ⟨chosen, selected, permits⟩ := permitted
  cases Option.some.inj selected
  refine ⟨material, rfl, ?_⟩
  rw [← outputs_eq_of_operationalRecall frame.recalled, ← envelope]
  exact permits

/-- A normalized opening of the same authentic candidate on both sides remains
a legal response and extends the actual repaired trace. No success of the
publication or deadline premise is needed for this transmission step. -/
theorem normalized_opening_trace
    (frame : DirectedBindingFrame memory owner original repaired)
    (remaining : Nat)
    (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, original⟩))
    (imagePrior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
      (some ⟨remaining, some owner, repaired⟩))
    (records : operationalRecord setup leaks bounds horizon scheduler prior =
      operationalRecord setup leaks bounds horizon scheduler imagePrior)
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (owned : candidate.1 = owner)
    (leftFixed : original.application.candidates.lookup candidate = .openable raw)
    (rightFixed : repaired.application.candidates.lookup candidate = .openable raw)
    (member : (⟨some ((disclosureSubmission (.opening event candidate raw)).normalizeReactive
        owner ((application setup leaks).observePlayer original.application owner)
          (original.network.known owner))⟩ : (application setup leaks).Action) ∈
      bounds.onePacketActions (runtime setup) leaks owner (original.recall owner)
        (original.observe (application setup leaks) owner)) :
    let app := application setup leaks
    let material := (disclosureSubmission (.opening event candidate raw)).normalizeReactive owner
      (app.observePlayer original.application owner) (original.network.known owner)
    let response : app.Action := ⟨some material⟩
    let remembered := memory.record (runtime setup) leaks
      (memory.shadow.inputView (runtime setup) leaks (repaired.observe app owner)) response
    DirectedBindingFrame remembered owner (original.respond app owner response)
        (repaired.respond app owner response) ∧
      ∃ trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace
          (some ⟨remaining, none, repaired.respond app owner response⟩),
        operationalRecord setup leaks bounds horizon scheduler trace =
          operationalState setup leaks (some ⟨remaining, none, original.respond app owner response⟩)
            :: operationalRecord setup leaks bounds horizon scheduler prior := by
  intro app material response remembered
  have originalCount := (runtime setup).countRecall_history leaks
    ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      prior)
  have repairedCount := (runtime setup).countRecall_history leaks
    ((bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      imagePrior)
  have materialShape : material = ⟨⟨.opening event candidate raw, none⟩, material.evidence⟩ := by
    simp only [material, WitnessedSubmission.normalizeReactive,
      Submission.normalizeReactive_none, disclosureSubmission]
  have authentic : (material.emit original.application owner
      (original.network.known owner)).evidence = some ⟨candidate, raw⟩ := by
    have normalized := WitnessedSubmission.normalizeReactive_emit (runtime setup) leaks
      original.application owner (original.network.known owner)
      (disclosureSubmission (.opening event candidate raw))
    have evidence := congrArg WitnessedPacket.evidence normalized
    change (material.emit original.application owner (original.network.known owner)).evidence =
      ((disclosureSubmission (.opening event candidate raw)).emit original.application owner
        (original.network.known owner)).evidence at evidence
    exact evidence.trans (WitnessedSubmission.emit_owned _ _ _ _ _ owned leftFixed)
  have after := frame.toFrame.opening_submission event candidate raw material.evidence rightFixed
    (by rw [← materialShape]; exact authentic)
  have responseEq : response = ⟨some ⟨⟨.opening event candidate raw, none⟩, material.evidence⟩⟩ :=
    congrArg (fun call => (⟨some call⟩ : app.Action)) materialShape
  dsimp only at after
  rw [← responseEq] at after
  change BindingMemory.Frame (runtime setup) leaks remembered owner
    (original.respond app owner response) (repaired.respond app owner response) at after
  have parts := (bounds.mem_onePacketActions (runtime setup) leaks owner (original.recall owner)
    (original.observe app owner) _).mp member
  have targetEffective := frame.toFrame.normalized_opening_available bounds originalCount.1
    repairedCount.1 event candidate raw owned leftFixed rightFixed parts.1
  rw [← frame.toFrame.normalized_opening_eq event candidate raw owned leftFixed rightFixed]
    at targetEffective
  have targetMember : response ∈ bounds.onePacketActions (runtime setup) leaks owner
      (repaired.recall owner) (repaired.observe app owner) := by
    apply (bounds.mem_onePacketActions (runtime setup) leaks owner (repaired.recall owner)
      (repaired.observe app owner) _).mpr
    refine ⟨targetEffective, Or.inr ?_⟩
    apply opening_countPermits frame originalCount repairedCount material after
    rcases parts.2 with impossible | permitted
    · cases impossible
    · exact permitted
  exact frame.responder_trace remaining owner prior imagePrior records response response
    targetMember after

end DirectedBindingFrame

end Vegas
