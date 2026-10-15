/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapMenu
import Vegas.Pending.ExclusionCountMenu
import Vegas.Pending.PhaseLatestBindings

/-! # Operational normalization of actual phased counted responses -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- Remove unused preparation data and replace evidence requests by their
actual canonical result. Phase identity, authorization and native effects stay fixed. -/
def normalization : (phaseApplication runtime leaks).SubmissionNormalization where
  normalize who view known material := material.normalizeReactive who view.1
    (known.map nativeMessage)
  idempotent who view known material :=
    WitnessedSubmission.normalizeReactive_idempotent who view.1 (known.map nativeMessage) material
  packet state who known material := by
    let nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
      fun _ _ => PMF.pure ∅
    have native := (Recovery.normalization runtime nativeLeaks).packet state.current who
      (known.map nativeMessage) material
    let mask : WitnessedPacket graph → CommitAttemptPacket graph := fun packet =>
      ⟨state.attempt, if state.allows packet.call then packet else { packet with token := none }⟩
    change mask ((state.current.submit who material).emit who (known.map nativeMessage)
        (material.normalizeReactive who (state.current.native.playerView who)
          (known.map nativeMessage))) =
      mask ((state.current.submit who material).emit who (known.map nativeMessage) material)
    exact congrArg mask native
  submit state who known material := by
    let nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
      fun _ _ => PMF.pure ∅
    have native := (Recovery.normalization runtime nativeLeaks).submit state.current who
      (known.map nativeMessage) material
    change ({ state with current := (state.current.submit who
      (material.normalizeReactive who (state.current.native.playerView who)
        (known.map nativeMessage))) } : PhaseRuntimeState graph) = _
    change state.current.submit who
      (material.normalizeReactive who (state.current.native.playerView who)
        (known.map nativeMessage)) = state.current.submit who material at native
    exact congrArg (fun current : RecoveryState graph =>
      ({ state with current := current } : PhaseRuntimeState graph)) native

/-- The local signed packet is unchanged even before imposing reachability of
the supplied local input. Its permanent audit verdict therefore stays fixed. -/
theorem localEnvelope_normalize (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (material : WitnessedSubmission graph) :
    localEnvelope runtime leaks who past view
        ((normalization runtime leaks).normalize who view.application
          (ReactiveApplication.ResponseMenu.knownPackets past view) material) =
      localEnvelope runtime leaks who past view material := by
  have candidates := funext (Submission.normalizeReactive_candidateAfter who
    view.application.1 material.call)
  unfold localEnvelope
  dsimp only [normalization, WitnessedSubmission.normalizeReactive]
  rw [Submission.normalizeReactive_packet, candidates, EvidenceRequest.resolve_normalize]

private theorem maskPacket_evidence (view : PhasePublicView graph)
    (packet : WitnessedPacket graph) : (maskPacket view packet).evidence = packet.evidence := by
  unfold maskPacket
  split <;> split <;> rfl

/-- A permitted binding discloses no certificate. Its canonical request is
therefore none, even when the raw request used arbitrary owned or forwarded evidence. -/
theorem normalize_binding_evidence_none (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (material : WitnessedSubmission graph)
    (event : graph.EventId) (candidate : Handle graph)
    (sent : material.call.packet = .commitment event candidate)
    (permitted : permits ((phaseApplication runtime leaks).outputs past)
      (localEnvelope runtime leaks who past view material) = true) :
    ((normalization runtime leaks).normalize who view.application
      (ReactiveApplication.ResponseMenu.knownPackets past view) material).evidence = .none := by
  have correct := ((permits_eq_true_iff _ _).mp permitted).2.1
  have callEq : (nativeMessage (localEnvelope runtime leaks who past view material)).payload.call =
      .commitment event candidate := by
    change (maskPacket _ _).call = _
    exact (maskPacket_call _ _).trans sent
  unfold CountCallCorrect at correct
  rw [callEq] at correct
  have absent := correct.2.1
  change (maskPacket _ _).evidence = none at absent
  rw [maskPacket_evidence] at absent
  change material.evidence.resolve who
    (material.call.candidateAfter who view.application.1.candidates)
    ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage) = none at absent
  change (material.evidence.normalize who
    (material.call.candidateAfter who view.application.1.candidates)
    ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage)) = .none
  unfold EvidenceRequest.normalize
  rw [absent]
  rfl

variable [Fintype Player] (bounds : MessageBounds graph)

/-- Canonicalization preserves the actual bounded raw menu. -/
theorem normalize_mem_rawMenu (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ (rawMenu runtime leaks bounds).actions who past view) :
    (normalization runtime leaks).action who past view response ∈
      (rawMenu runtime leaks bounds).actions who past view := by
  change response ∈ (ReactiveApplication.ResponseMenu.fromSubmissions _).actions _ _ _ at member
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member
  change (normalization runtime leaks).action who past view response ∈
    (ReactiveApplication.ResponseMenu.fromSubmissions _).actions _ _ _
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some material =>
      change material ∈ bounds.submissions _ at member
      change material.normalizeReactive who view.application.1
        ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage) ∈
          bounds.submissions _
      exact bounds.normalize_submission_mem who view.application.1 _ material member

/-- The physical count menu is closed under operational normalization;
first packets of voided attempts retain the same verdict. -/
theorem normalize_mem_onePacketActions (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ onePacketActions runtime leaks bounds who past view) :
    (normalization runtime leaks).action who past view response ∈
      onePacketActions runtime leaks bounds who past view := by
  rw [mem_onePacketActions] at member ⊢
  refine ⟨normalize_mem_rawMenu runtime leaks bounds who past view response member.1, ?_⟩
  rcases member.2 with silent | ⟨material, transmitted, permitted⟩
  · left
    rcases response with ⟨transmission⟩
    change transmission = none at silent
    subst silent
    rfl
  · right
    refine ⟨(normalization runtime leaks).normalize who view.application
      (ReactiveApplication.ResponseMenu.knownPackets past view) material, ?_, ?_⟩
    · rcases response with ⟨transmission⟩
      change transmission = some material at transmitted
      subst transmitted
      rfl
    · rw [localEnvelope_normalize]
      exact permitted

end Vegas.EventGraphRuntime.PhaseCount
