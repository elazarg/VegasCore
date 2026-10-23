/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketDirectedRepairFrame

/-! # One-packet legality under directed hidden-binding repair

Replacing the private material of a binding at a fresh prepared slot preserves
its signed envelope and count verdict. The replacement is a bounded normal
response for every bounded opening, including a typed default replacing missing
or mistyped material. No canonical choice of the fresh slot is needed.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- Equal operational recalls retain precisely the same authored envelopes. -/
theorem outputs_eq_of_operationalRecall
    {first second : List (application setup leaks).PlayerEntry}
    (same : operationalRecall (setup := setup) (leaks := leaks) first =
      operationalRecall second) :
    (application setup leaks).outputs first = (application setup leaks).outputs second := by
  have projected := congrArg (List.filterMap (fun entry : OperationalView setup leaks ×
    Option (Message Player (application setup leaks).Payload) => entry.2)) same
  simpa only [operationalRecall, List.filterMap_map, ReactiveApplication.outputs,
    Function.comp_def] using projected

namespace EventGraphRuntime.BindingMemory.Frame

variable {memory : BindingMemory (runtime setup) leaks} {owner : Player}
  {original repaired : (application setup leaks).Execution}

/-- Fresh serials and readiness tokens of a raw binding are unchanged when only
its private material is replaced under a repair frame. -/
theorem localEnvelope_rawBinding
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (originalCount : (runtime setup).CountRecall leaks original)
    (repairedCount : (runtime setup).CountRecall leaks repaired)
    (event : (graph setup).EventId) (serial : Nat) (first second : Option (Raw L)) :
    (runtime setup).localEnvelope leaks owner (original.recall owner)
        (original.observe (application setup leaks) owner)
        ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩ =
      (runtime setup).localEnvelope leaks owner (repaired.recall owner)
        (repaired.observe (application setup leaks) owner)
        ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩ := by
  change Message.mk (owner, (application setup leaks).submissionCount (original.recall owner))
      (⟨.commitment event (owner, .prepared serial), none,
        original.application.publicView.tokenFor (.commitment event (owner, .prepared serial))⟩ :
        WitnessedPacket (graph setup)) =
    Message.mk (owner, (application setup leaks).submissionCount (repaired.recall owner))
      ⟨.commitment event (owner, .prepared serial), none,
        repaired.application.publicView.tokenFor (.commitment event (owner, .prepared serial))⟩
  rw [← originalCount.2.1 owner, ← repairedCount.2.1 owner, frame.network, frame.publicView]

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- Every admitted raw binding remains admitted after replacement of its
private opening by any bounded opening at the same fresh prepared slot. -/
theorem onePacket_rawBinding
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (setup := setup) (leaks := leaks)
        (original.recall owner) = Vegas.operationalRecall (repaired.recall owner))
    (originalCount : (runtime setup).CountRecall leaks original)
    (repairedCount : (runtime setup).CountRecall leaks repaired)
    (event : (graph setup).EventId) (serial : Nat) (first second : Option (Raw L))
    (fresh : repaired.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (bounded : bounds.AllowsOpening second)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), first⟩, .none⟩⟩ :
      (application setup leaks).Action) ∈ bounds.onePacketActions (runtime setup) leaks owner
        (original.recall owner) (original.observe (application setup leaks) owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), second⟩, .none⟩⟩ :
      (application setup leaks).Action) ∈ bounds.onePacketActions (runtime setup) leaks owner
        (repaired.recall owner) (repaired.observe (application setup leaks) owner) := by
  obtain ⟨effective, permitted⟩ := (bounds.mem_onePacketActions (runtime setup) leaks owner
    (original.recall owner) (original.observe (application setup leaks) owner) _).mp member
  have fields := (bounds.menu_mem (runtime setup) leaks owner (original.recall owner)
    (original.observe (application setup leaks) owner) _).mp effective
  have packetBound := fields.1.1.1
  apply (bounds.mem_onePacketActions (runtime setup) leaks owner (repaired.recall owner)
    (repaired.observe (application setup leaks) owner) _).mpr
  refine ⟨?_, Or.inr ⟨_, rfl, ?_⟩⟩
  · apply (bounds.menu_mem (runtime setup) leaks owner (repaired.recall owner)
      (repaired.observe (application setup leaks) owner) _).mpr
    refine ⟨⟨⟨packetBound, bounded⟩, trivial⟩, ?_⟩
    simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
      WitnessedSubmission.normalizeReactive, Submission.normalizeReactive, openingEffective,
      show (repaired.observe (application setup leaks) owner).application.candidates
        (.prepared serial) = .fresh from fresh,
      and_self, ↓reduceIte, EvidenceRequest.normalize_none]
  · rcases permitted with impossible | ⟨material, sent, permits⟩
    · cases impossible
    · have materialEq := Option.some.inj sent
      subst material
      rw [← outputs_eq_of_operationalRecall recalled,
        ← frame.localEnvelope_rawBinding originalCount repairedCount event serial first second]
      exact permits

/-- The actual private binding-repair implementation preserves the one-packet
menu on its complete raw binding branch. Missing and wrongly typed material are
replaced by a covered typed default; usable bounded material stays unchanged. -/
theorem repairResponse_onePacket
    (frame : Frame (runtime setup) leaks memory owner original repaired)
    (recalled : Vegas.operationalRecall (setup := setup) (leaks := leaks)
        (original.recall owner) = Vegas.operationalRecall (repaired.recall owner))
    (originalCount : (runtime setup).CountRecall leaks original)
    (repairedCount : (runtime setup).CountRecall leaks repaired)
    (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L))
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (covered : bounds.CoversOutputValues)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩ :
      (application setup leaks).Action) ∈ bounds.onePacketActions (runtime setup) leaks owner
        (original.recall owner) (original.observe (application setup leaks) owner)) :
    (memory.repairResponse (runtime setup) leaks owner
      (repaired.observe (application setup leaks) owner)
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩).1 ∈
      bounds.onePacketActions (runtime setup) leaks owner (repaired.recall owner)
        (repaired.observe (application setup leaks) owner) := by
  have actualFresh := (frame.slots (.prepared serial)).mp fresh
  have originalFresh : (memory.shadow.inputView (runtime setup) leaks
      (repaired.observe (application setup leaks) owner)).application.candidates
      (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  cases decoded : opening.bind (fun raw => raw.as? payload) with
  | none =>
      rw [memory.repairResponse_unusable (runtime setup) leaks owner _ event payload outputEq
        codeEq node serial opening originalFresh actualFresh decoded]
      have valueBound := covered event
      rw [outputEq] at valueBound
      exact frame.onePacket_rawBinding bounds recalled originalCount repairedCount event serial
        opening (some ⟨payload, L.someValue payload⟩) actualFresh (valueBound _) member
  | some value =>
      rw [memory.repairResponse_usable (runtime setup) leaks owner _ event payload outputEq codeEq
        node serial opening originalFresh actualFresh value decoded]
      have effective := ((bounds.mem_onePacketActions (runtime setup) leaks owner
        (original.recall owner) (original.observe (application setup leaks) owner) _).mp member).1
      have fields := (bounds.menu_mem (runtime setup) leaks owner (original.recall owner)
        (original.observe (application setup leaks) owner) _).mp effective
      exact frame.onePacket_rawBinding bounds recalled originalCount repairedCount event serial
        opening opening actualFresh fields.1.1.2 member

end EventGraphRuntime.BindingMemory.Frame

end Vegas
