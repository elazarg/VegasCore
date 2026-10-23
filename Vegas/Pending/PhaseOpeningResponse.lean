/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseLatestBindingHistory

/-! # Authentic opening responses in actual phased count menus -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An opening requests the immutable owned certificate; it prepares no new value. -/
def phaseOpeningResponse (event : graph.EventId) (candidate : Handle graph) (raw : Raw L) :
    (app).Action := ⟨some (disclosureSubmission (.opening event candidate raw))⟩

/-- A surviving accepted handle has exactly the latest signed binding required
by the count verdict for the owner's next envelope. -/
theorem latestSignedBinding_of_accepted (execution : (app).Execution)
    (physical : PhysicalBindings runtime leaks execution)
    (initial : ∀ input candidate,
      execution.application.current.native.accepted (.inl input) = some candidate →
        candidate = (candidate.1, .initial input))
    (owner : Player) (candidate : Handle graph) (owned : candidate.1 = owner)
    (field : graph.Field)
    (accepted : execution.application.current.native.accepted field = some candidate)
    (packet : CommitAttemptPacket graph) :
    LatestSignedBinding (Earlier execution.network.inputs
      ⟨(owner, execution.network.nextSerial owner), packet⟩) owner candidate field := by
  cases field with
  | inl input => simpa only [LatestSignedBinding, owned] using initial input candidate accepted
  | inr event =>
      let message : Message Player (CommitAttemptPacket graph) :=
        ⟨(owner, execution.network.nextSerial owner), packet⟩
      have clean : ∀ other ∈ execution.network.inputs,
          Permits execution.network.inputs other := fun other member =>
        (permits_eq_true_iff _ _).mp (physical.clean.2 other member)
      apply (latestSignedBinding_iff_last_of_clean execution.network.inputs message event
        candidate clean).mpr
      obtain ⟨origin, present, sender, call, latest⟩ := physical.active event candidate accepted
      refine ⟨origin, ⟨present, sender.trans owned, ?_⟩, call, ?_⟩
      · simpa only [message, Message.sender, show origin.id.1 = owner from sender.trans owned] using
          physical.clean.1.2.2.serial_lt present
      · intro later before handle named
        exact latest later before.1 (before.2.1.trans (sender.trans owned).symm) handle named

/-- A first opening of the surviving accepted value satisfies the actual
physical count rule. It uses the full retained traffic, including retired attempts. -/
theorem phaseOpeningResponse_permitted (execution : (app).Execution)
    (physical : PhysicalBindings runtime leaks execution)
    (initial : ∀ input candidate,
      execution.application.current.native.accepted (.inl input) = some candidate →
        candidate = (candidate.1, .initial input))
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (candidate : Handle graph) (value : L.Val payload) (owned : candidate.1 = owner)
    (accepted : execution.application.current.native.accepted binding.field = some candidate)
    (verified : execution.application.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (execution.recall owner),
      event? message.payload ≠ some ⟨execution.application.attempt, event⟩) :
    OnePacketResponse runtime leaks owner (execution.recall owner)
      (execution.observe app owner)
      (phaseOpeningResponse runtime leaks event candidate ⟨payload, value⟩) := by
  let material := disclosureSubmission (.opening event candidate ⟨payload, value⟩)
  let packet : CommitAttemptPacket graph := ⟨execution.application.attempt,
    ⟨.opening event candidate ⟨payload, value⟩, some ⟨candidate, ⟨payload, value⟩⟩,
      some ⟨event⟩⟩⟩
  let message : Message Player (CommitAttemptPacket graph) :=
    ⟨(owner, execution.network.nextSerial owner), packet⟩
  have allowed : allows execution.application.publicView material.call.packet = true := by
    rw [allows_publicView]
    obtain ⟨phase, member, inside⟩ := request.2.1
    simp only [PhaseRuntimeState.allows, Option.mem_def.mp member, material,
      disclosureSubmission, Payload.event?]
    exact decide_eq_true inside
  have unexcluded : excludedCall execution.application.publicView material.call.packet = false := by
    simp only [excludedCall, material, disclosureSubmission, Payload.event?,
      request.2.2.2.1, Option.any_some]
    exact decide_eq_false request.2.2.2.2
  have token := execution.application.current.native.publicView_tokenFor_of_ready
    material.call.packet event (by rfl) request.2.2.1
  have envelope : localEnvelope runtime leaks owner (execution.recall owner)
      (execution.observe app owner) material = message := by
    rw [localEnvelope_eq_of_recall runtime leaks execution physical.clean.1.1
      physical.clean.1.2.1 owner material]
    change Message.mk _ ((execution.application.submit owner material).emit owner
      (execution.network.known owner) material) = message
    rw [emit_after_submit]
    have localVerified : (execution.application.current.native.playerView owner).candidates
        candidate.2 = .openable ⟨payload, value⟩ := by
      change execution.application.current.native.candidates.lookup (owner, candidate.2) = _
      simpa only [← owned, Prod.mk.eta] using verified
    have evidence : material.evidence.resolve owner
        (material.call.candidateAfter owner
          (execution.application.current.native.playerView owner).candidates)
        ((execution.network.known owner).map nativeMessage) =
          some ⟨candidate, ⟨payload, value⟩⟩ := by
      simp only [material, disclosureSubmission, Submission.candidateAfter_opening,
        EvidenceRequest.resolve, owned, localVerified, and_self, ↓reduceIte]
    change Message.mk _ ⟨_, maskPacket execution.application.publicView
      ⟨material.call.packet, _,
        execution.application.current.native.publicView.tokenFor material.call.packet⟩⟩ = message
    rw [evidence]
    simp only [maskPacket, allowed, unexcluded, Bool.false_eq_true, ↓reduceIte, token]
    rfl
  have latest := latestSignedBinding_of_accepted runtime leaks execution physical initial owner
    candidate owned binding.field accepted packet
  have ownEarlier : ∀ other, Earlier ((app).outputs (execution.recall owner)) message other ↔
      Earlier execution.network.inputs message other := by
    intro other
    have recalled := physical.clean.1.1 owner
    rw [← recalled]
    simp only [Earlier, List.mem_filter, decide_eq_true_eq, message, Message.sender]
    tauto
  refine ⟨material, rfl, ?_⟩
  rw [envelope, permits_congr _ execution.network.inputs message ownEarlier, permits_eq_true_iff]
  refine ⟨WitnessedPacket.tokenValid_opening _ _ _ _, ?_, ?_, ?_⟩
  · simp only [CountCallCorrect, nativeMessage, message, packet, node, certifiedOpening,
      decide_true, true_and]
    refine ⟨rfl, ?_⟩
    cases field : binding.field with
    | inl input =>
        simpa only [SignedBinding, LatestSignedBinding, field, Message.sender] using latest
    | inr event =>
        rw [field] at latest
        obtain ⟨origin, before, eligible, _⟩ := latest
        exact ⟨nativeMessage origin,
          (earlier_native _ message _).mpr ⟨origin, before, rfl⟩, eligible.1⟩
  · intro other before
    have retained : other ∈ (app).outputs (execution.recall owner) := by
      rw [← physical.clean.1.1 owner]
      exact List.mem_filter.mpr ⟨before.1, by
        simpa only [message, Message.sender, decide_eq_true_eq] using before.2.1⟩
    simpa only [message, packet, event?, Payload.event?, Option.map_some] using
      unsent other retained
  · simpa only [OpeningBinding, message, packet, node, Message.sender] using latest

end Vegas.EventGraphRuntime.PhaseCount
