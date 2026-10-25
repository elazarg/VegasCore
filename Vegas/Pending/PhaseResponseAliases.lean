/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveNormalSubmissionCount
import Vegas.Pending.PhaseResponseNormalization

/-! # Physical phase menus preserve private response normalization

Recall normalization retains signed outputs and submission serials. Normalizing
the current material also retains its exact local envelope, including both token
masks and the attempt address, so the one-packet filter is closed under it.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem localEnvelope_normalize (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (material : (app).Submission) :
    localEnvelope runtime leaks who past view
        ((normalization runtime leaks).normalize who view.application
          (ReactiveApplication.ResponseMenu.knownPackets past view) material) =
      localEnvelope runtime leaks who past view material := by
  have candidates := funext
    (Submission.normalizeReactive_candidateAfter who view.application.1 material.call)
  simp only [localEnvelope, normalization, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_packet, candidates, EvidenceRequest.resolve_normalize]

theorem localEnvelope_recall (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (material : (app).Submission) :
    localEnvelope runtime leaks actor (normal.recall who past) view material =
      localEnvelope runtime leaks actor past view material := by
  simp only [localEnvelope, normal.recall_submissionCount,
    ReactiveApplication.ResponseMenu.knownPackets, normal.recall_outputs]

variable [Fintype Player] (bounds : MessageBounds graph)

theorem rawMenu_eq_of_outputs (who : Player)
    (first second : List (app).PlayerEntry) (view : (app).PlayerView)
    (same : (app).outputs first = (app).outputs second) :
    (rawMenu runtime leaks bounds).actions who first view =
      (rawMenu runtime leaks bounds).actions who second view := by
  classical
  simp only [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions,
    ReactiveApplication.ResponseMenu.knownPackets, same]

theorem rawMenu_recall (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) :
    (rawMenu runtime leaks bounds).actions who
        ((normalization runtime leaks).recall who past) view =
      (rawMenu runtime leaks bounds).actions who past view :=
  rawMenu_eq_of_outputs runtime leaks bounds who _ _ view
    ((normalization runtime leaks).recall_outputs who past)

theorem rawMenu_closed (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : (app).Action)
    (member : response ∈ (rawMenu runtime leaks bounds).actions who past view) :
    (normalization runtime leaks).action who past view response ∈
      (rawMenu runtime leaks bounds).actions who past view := by
  classical
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member ⊢
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some material => exact bounds.normalize_submission_mem who view.application.1 _ _ member

theorem onePacketActions_recall (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    onePacketActions runtime leaks bounds actor (normal.recall who past) view =
      onePacketActions runtime leaks bounds actor past view := by
  classical
  have raw := rawMenu_eq_of_outputs runtime leaks bounds actor _ _ view
    (normal.recall_outputs who past)
  ext response
  simp only [mem_onePacketActions, raw, OnePacketResponse,
    normal.recall_outputs, localEnvelope_recall]

theorem onePacketMenu_recall (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) :
    (onePacketMenu runtime leaks bounds).actions who
        ((normalization runtime leaks).recall who past) view =
      (onePacketMenu runtime leaks bounds).actions who past view :=
  onePacketActions_recall runtime leaks bounds (normalization runtime leaks) who who past view

theorem onePacketMenu_closed (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) (response : (app).Action)
    (member : response ∈ (onePacketMenu runtime leaks bounds).actions who past view) :
    (normalization runtime leaks).action who past view response ∈
      (onePacketMenu runtime leaks bounds).actions who past view := by
  classical
  obtain ⟨raw, permitted⟩ := (mem_onePacketActions runtime leaks bounds who past view response).mp
    member
  apply (mem_onePacketActions runtime leaks bounds who past view _).mpr
  refine ⟨rawMenu_closed runtime leaks bounds who past view response raw, ?_⟩
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl rfl
  | some material =>
      obtain ⟨selected, sent, accepted⟩ := permitted.resolve_left (by simp)
      cases Option.some.inj sent
      right
      refine ⟨_, rfl, ?_⟩
      rw [localEnvelope_normalize]
      exact accepted

end Vegas.EventGraphRuntime.PhaseCount
