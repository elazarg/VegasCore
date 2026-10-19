/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalShadowInertResponse
import Vegas.Pending.PhaseProposalShadowOpening
import Vegas.Pending.PhaseBindingOpeningRead

/-! # Actual truthful opening responses under general binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine counted opening reads an original successful binding. The
bad-only refinement preserves that exact value, so the original private
certificate request and inert preparation remain legal and emit the same
packet. A guard may still reject its actual subsequent publication. -/
theorem opening_response_external (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner) (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (preserved : left.application.current.native.config.store.BindingRefines
      right.application.current.native.config.store)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, right⟩))
    (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (preparation : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (left.recall owner) (left.observe app owner))
    (request : left.application.SeedRequest owner ⟨left.application.attempt, event⟩)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    let response : (app).Action :=
      ⟨some ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩⟩
    response ∈ PhaseCount.onePacketActions runtime leaks bounds owner (right.recall owner)
        (right.observe app owner) ∧
      PhaseStateFrame memory owner (left.respond app owner response).application
        (right.respond app owner response).application ∧
      (left.respond app owner response).network = (right.respond app owner response).network ∧
      phaseExternalObservation runtime leaks owner (left.respond app owner response) =
        phaseExternalObservation runtime leaks owner (right.respond app owner response) := by
  classical
  let material : WitnessedSubmission graph :=
    ⟨⟨.opening event candidate raw, preparation⟩, evidence⟩
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler rightTrace
  have countLeft := PhaseCount.countRecall_history runtime leaks rawLeft
  have countRight := PhaseCount.countRecall_history runtime leaks rawRight
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding := phaseBindingRecord_history runtime leaks plan inputs horizon
    scheduler rawRight
  obtain ⟨value, typed, successful, accepted, _fixed⟩ :=
    PhaseBindingRepair.opening_response_binding_success runtime leaks bounds plan inputs horizon
      scheduler remaining left owner leftTrace material event candidate raw rfl member request
        payload binding checks outputEq codeEq node
  obtain ⟨_rightStored, other, leftAccepted, _rightAccepted, _actor, _leftFixed, rightFixed⟩ :=
    frame.successful_opening owned preserved leftBinding.active rightBinding.active
      binding value successful
  have same : candidate = other := Option.some.inj (accepted.symm.trans leftAccepted)
  subst other
  have rightRaw : right.application.current.native.candidates.lookup candidate = .openable raw := by
    rw [typed]
    exact rightFixed
  let message := PhaseCount.localEnvelope runtime leaks owner (left.recall owner)
    (left.observe app owner) material
  have permitted : PhaseCount.permits ((app).outputs (left.recall owner)) message = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
      with impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  have named : message.payload.packet.call = .opening event candidate raw :=
    PhaseCount.maskPacket_call _ _
  rw [named] at correct
  obtain ⟨certifiedOpeningPacket, _resolves⟩ := correct
  have physicalCertificate : message.payload.packet.evidence = some ⟨candidate, raw⟩ := by
    unfold certifiedOpening at certifiedOpeningPacket
    rw [named] at certifiedOpeningPacket
    cases found : message.payload.packet.evidence with
    | none => simp only [found, Bool.false_eq_true] at certifiedOpeningPacket
    | some fact =>
        simp only [found, decide_eq_true_eq] at certifiedOpeningPacket
        exact congrArg some certifiedOpeningPacket
  have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks left
    countLeft.1 countLeft.2.1 owner material
  have certified : (material.emit left.application.current.native owner
      ((left.network.known owner).map PhaseCount.nativeMessage)).evidence =
        some ⟨candidate, raw⟩ := by
    have sameEnvelope := congrArg (fun packet : Message Player (CommitAttemptPacket graph) =>
      packet.payload.packet.evidence) envelope
    change message.payload.packet.evidence =
      (left.application.emit owner (left.network.known owner) material).packet.evidence
        at sameEnvelope
    rw [phase_emit_evidence] at sameEnvelope
    exact sameEnvelope.symm.trans physicalCertificate
  have rightCertified : (material.emit right.application.current.native owner
      ((right.network.known owner).map PhaseCount.nativeMessage)).evidence =
        some ⟨candidate, raw⟩ := by
    cases evidence with
    | none => cases certified
    | forward id =>
        change (((right.network.known owner).map PhaseCount.nativeMessage).find? _).bind _ = _
        rw [← network]
        exact certified
    | owned fact =>
        simp only [material, WitnessedSubmission.emit] at certified
        split at certified
        · rename_i available
          cases Option.some.inj certified
          exact WitnessedSubmission.emit_owned _ _ _ _ _ available.1 rightRaw
        · cases certified
  have nativePublic : left.application.current.native.publicView =
      right.application.current.native.publicView := by
    rw [frame.current]
    exact native_publicView owned _
  have nativePacket : material.emit left.application.current.native owner
      ((left.network.known owner).map PhaseCount.nativeMessage) =
      material.emit right.application.current.native owner
        ((right.network.known owner).map PhaseCount.nativeMessage) := by
    change WitnessedPacket.mk _ _ (left.application.current.native.publicView.tokenFor _) =
      WitnessedPacket.mk _ _ (right.application.current.native.publicView.tokenFor _)
    rw [nativePublic]
    exact congrArg (fun certificate => WitnessedPacket.mk (.opening event candidate raw)
      certificate (right.application.current.native.publicView.tokenFor
        (.opening event candidate raw))) (certified.trans rightCertified.symm)
  have publicEq := frame.publicView owned
  have attempts : left.application.attempt = right.application.attempt := by
    simp only [PhaseRuntimeState.attempt, frame.phases, frame.generation]
  have emitted : left.application.emit owner (left.network.known owner) material =
      right.application.emit owner (right.network.known owner) material := by
    rw [PhaseBindingRepair.emit_mask, PhaseBindingRepair.emit_mask, nativePacket,
      publicEq, attempts]
  exact respond_inert_external runtime leaks memory owner owned left right frame network receipts
    service recalled bounds countLeft countRight material rfl rfl emitted member

end Vegas.EventGraphRuntime.BindingShadow
