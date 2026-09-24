/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveNormalization
import Interaction.ReactiveFiniteAssessment

/-! # Complete finite response syntax under explicit message bounds

Bounds specify a finite raw-value alphabet and a range of prepared handles.
Every packet constructor is included, for every address and principal, including
malformed packets and invalid calls. Silent responses and all known replays are
available. Only operationally ineffective private distinctions are normalized.
These are explicit bounds on the modeled backend, not an EVM encoding theorem.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

structure MessageBounds (graph : Vegas.EventGraph Player L) where
  candidateCount : Nat
  values : Finset (Raw L)

namespace MessageBounds

variable (bounds : MessageBounds graph)

def AllowsHandle (handle : Handle graph) : Prop :=
  match handle.2 with
  | .initial _ => True
  | .prepared serial => serial < bounds.candidateCount

def AllowsPacket : Payload graph → Prop
  | .commitment _ handle => bounds.AllowsHandle handle
  | .opening _ handle raw => bounds.AllowsHandle handle ∧ raw ∈ bounds.values
  | .withhold _ => True
  | .malformed raw => raw ∈ bounds.values

def AllowsOpening : Option (Raw L) → Prop
  | none => True
  | some raw => raw ∈ bounds.values

variable [Fintype Player]

def handles : Finset (Handle graph) := by
  classical
  exact Finset.univ.biUnion fun who =>
    (Finset.univ.image fun input => (who, Slot.initial input)) ∪
      ((Finset.range bounds.candidateCount).image fun serial => (who, Slot.prepared serial))

theorem handles_mem (handle : Handle graph) :
    handle ∈ bounds.handles ↔ bounds.AllowsHandle handle := by
  classical
  rcases handle with ⟨owner, slot⟩
  cases slot <;> simp [handles, AllowsHandle]

def packets : Finset (Payload graph) := by
  classical
  exact ((Finset.univ ×ˢ bounds.handles).image fun pair => .commitment pair.1 pair.2) ∪
    (((Finset.univ ×ˢ bounds.handles) ×ˢ bounds.values).image fun pair =>
      .opening pair.1.1 pair.1.2 pair.2) ∪
    (Finset.univ.image Payload.withhold) ∪ (bounds.values.image Payload.malformed)

theorem packets_mem (packet : Payload graph) :
    packet ∈ bounds.packets ↔ bounds.AllowsPacket packet := by
  classical
  cases packet <;> simp [packets, handles_mem, AllowsPacket]

def submissions : Finset (Submission graph) := by
  classical
  exact bounds.packets.biUnion fun packet =>
    insert ⟨packet, none⟩ (bounds.values.image fun raw => ⟨packet, some raw⟩)

theorem submissions_mem (submission : Submission graph) :
    submission ∈ bounds.submissions ↔
      bounds.AllowsPacket submission.packet ∧ bounds.AllowsOpening submission.opening := by
  classical
  rcases submission with ⟨packet, opening⟩
  cases opening <;> simp [submissions, packets_mem, AllowsOpening]

theorem normalize_submission_mem (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) (member : submission ∈ bounds.submissions) :
    submission.normalizeReactive who view ∈ bounds.submissions := by
  classical
  rw [submissions_mem] at member ⊢
  refine ⟨member.1, ?_⟩
  change bounds.AllowsOpening (if openingEffective who view submission.packet then
    submission.opening else none)
  split
  · exact member.2
  · trivial

variable [DecidableEq Player]

def rawMenu (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) :
    (runtime.reactiveApplication leaks).ResponseMenu :=
  ReactiveApplication.ResponseMenu.fromSubmissions bounds.submissions

def menu (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) :
    (runtime.reactiveApplication leaks).ResponseMenu :=
  (runtime.reactiveNormalization leaks).menu (bounds.rawMenu runtime leaks)

theorem rawMenu_closed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ (bounds.rawMenu runtime leaks).actions who past view) :
    (runtime.reactiveNormalization leaks).action who past view response ∈
      (bounds.rawMenu runtime leaks).actions who past view := by
  classical
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member ⊢
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some transmission =>
      cases transmission with
      | submit submission => exact bounds.normalize_submission_mem who view.application _ member
      | replay id =>
          change ReactiveApplication.SubmissionNormalization.ReplayKnown past view id at member
          rw [ReactiveApplication.SubmissionNormalization.action, ite_eq_left member]
          exact member

/-- Exact completeness: every bounded normal response is admitted, including
all packet errors; every admitted response is bounded and normal. -/
theorem menu_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    response ∈ (bounds.menu runtime leaks).actions who past view ↔
      (match response.transmission with
      | none => True
      | some (.submit submission) =>
          bounds.AllowsPacket submission.packet ∧ bounds.AllowsOpening submission.opening
      | some (.replay id) => ReactiveApplication.SubmissionNormalization.ReplayKnown past view id) ∧
      (runtime.reactiveNormalization leaks).action who past view response = response := by
  rw [menu, ReactiveApplication.SubmissionNormalization.menu_mem_iff_of_closed
    _ _ _ _ _ (bounds.rawMenu_closed runtime leaks who past view), rawMenu,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact and_congr_left fun _ => bounds.submissions_mem submission
      | replay id => rfl

/-- Ineffective private material need not satisfy any bound. Only the packet
and the opening that survives normalization enter this premise. -/
theorem normalized_submission_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (submission : Submission graph)
    (packet : bounds.AllowsPacket submission.packet)
    (opening : bounds.AllowsOpening
      (submission.normalizeReactive who view.application).opening) :
    (runtime.reactiveNormalization leaks).action who past view ⟨some (.submit submission)⟩ ∈
      (bounds.menu runtime leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨⟨packet, opening⟩,
    (runtime.reactiveNormalization leaks).action_idempotent who past view _⟩

theorem known_replay_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (id : MessageId Player)
    (known : ReactiveApplication.SubmissionNormalization.ReplayKnown past view id) :
    (⟨some (.replay id)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      (bounds.menu runtime leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨known, by simp [ReactiveApplication.SubmissionNormalization.action, known]⟩

end MessageBounds
end Vegas.EventGraphRuntime
