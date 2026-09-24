/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveNormalization
import Interaction.ReactiveFiniteAssessment

/-! # Complete finite response syntax under explicit message bounds

Bounds specify a finite raw-value alphabet and a range of prepared handles.
Every packet constructor is included, for every address and principal, including
malformed packets and invalid calls. Every bounded certificate request and every
known forwarding reference are available, independently of the call. Silent
responses and all known replays are available. Only operationally ineffective
private distinctions are normalized.
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

def calls : Finset (Submission graph) := by
  classical
  exact bounds.packets.biUnion fun packet =>
    insert ⟨packet, none⟩ (bounds.values.image fun raw => ⟨packet, some raw⟩)

theorem calls_mem (submission : Submission graph) :
    submission ∈ bounds.calls ↔
      bounds.AllowsPacket submission.packet ∧ bounds.AllowsOpening submission.opening := by
  classical
  rcases submission with ⟨packet, opening⟩
  cases opening <;> simp [calls, packets_mem, AllowsOpening]

theorem normalize_call_mem (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) (member : submission ∈ bounds.calls) :
    submission.normalizeReactive who view ∈ bounds.calls := by
  classical
  rw [calls_mem] at member ⊢
  refine ⟨member.1, ?_⟩
  change bounds.AllowsOpening (if openingEffective who view submission.packet then
    submission.opening else none)
  split
  · exact member.2
  · trivial

def AllowsEvidence (known : List (Message Player (WitnessedPacket graph))) :
    EvidenceRequest graph → Prop
  | .none => True
  | .owned fact => bounds.AllowsHandle fact.handle ∧ fact.raw ∈ bounds.values
  | .forward id => ∃ message ∈ known, message.id = id

def facts : Finset (OpeningFact graph) := by
  classical
  exact (bounds.handles ×ˢ bounds.values).image (fun pair => ⟨pair.1, pair.2⟩)

theorem facts_mem (fact : OpeningFact graph) :
    fact ∈ bounds.facts ↔ bounds.AllowsHandle fact.handle ∧ fact.raw ∈ bounds.values := by
  classical
  rcases fact with ⟨handle, raw⟩
  simp [facts, handles_mem]

def requests (known : List (Message Player (WitnessedPacket graph))) :
    Finset (EvidenceRequest graph) := by
  classical
  exact insert .none ((bounds.facts.image EvidenceRequest.owned) ∪
    (known.map (fun message => EvidenceRequest.forward message.id)).toFinset)

theorem requests_mem (known : List (Message Player (WitnessedPacket graph)))
    (request : EvidenceRequest graph) :
    request ∈ bounds.requests known ↔ bounds.AllowsEvidence known request := by
  classical
  cases request <;> simp [requests, facts_mem, AllowsEvidence, eq_comm]

def submissions (known : List (Message Player (WitnessedPacket graph))) :
    Finset (WitnessedSubmission graph) := by
  classical
  exact (bounds.calls ×ˢ bounds.requests known).image (fun pair => ⟨pair.1, pair.2⟩)

theorem submissions_mem (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) :
    submission ∈ bounds.submissions known ↔
      (bounds.AllowsPacket submission.call.packet ∧ bounds.AllowsOpening submission.call.opening) ∧
        bounds.AllowsEvidence known submission.evidence := by
  classical
  rcases submission with ⟨call, evidence⟩
  simp [submissions, calls_mem, requests_mem]

variable [DecidableEq Player]

omit [Fintype Player] in
theorem normalize_evidence_mem (known : List (Message Player (WitnessedPacket graph)))
    (request : EvidenceRequest graph) (member : bounds.AllowsEvidence known request) :
    bounds.AllowsEvidence known (request.normalizeKnown known) := by
  cases request with
  | none | owned => exact member
  | forward id =>
      change (∃ message ∈ known, message.id = id) at member
      simp only [EvidenceRequest.normalizeKnown, member, ↓reduceIte, AllowsEvidence]

theorem normalize_submission_mem (who : Player) (view : ReactivePlayerView graph)
    (known : List (Message Player (WitnessedPacket graph)))
    (submission : WitnessedSubmission graph) (member : submission ∈ bounds.submissions known) :
    submission.normalizeReactive who view known ∈ bounds.submissions known := by
  rw [submissions_mem] at member ⊢
  exact ⟨(bounds.calls_mem _).mp (bounds.normalize_call_mem who view submission.call
    ((bounds.calls_mem _).mpr member.1)), bounds.normalize_evidence_mem known _ member.2⟩


def rawMenu (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).ResponseMenu :=
  ReactiveApplication.ResponseMenu.fromSubmissions (fun _ past view =>
    bounds.submissions (ReactiveApplication.ResponseMenu.knownPackets past view))

def menu (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) :
    (runtime.reactiveApplication leaks).ResponseMenu :=
  (runtime.reactiveNormalization leaks).menu (bounds.rawMenu runtime leaks)

theorem rawMenu_closed (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
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
      | submit submission => exact bounds.normalize_submission_mem who view.application _ _ member
      | replay id =>
          change ReactiveApplication.SubmissionNormalization.ReplayKnown past view id at member
          rw [ReactiveApplication.SubmissionNormalization.action, ite_eq_left member]
          exact member

/-- Exact completeness: every bounded normal response is admitted, including
all packet errors; every admitted response is bounded and normal. -/
theorem menu_mem (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action) :
    response ∈ (bounds.menu runtime leaks).actions who past view ↔
      (match response.transmission with
      | none => True
      | some (.submit submission) =>
          (bounds.AllowsPacket submission.call.packet ∧
            bounds.AllowsOpening submission.call.opening) ∧
            bounds.AllowsEvidence (ReactiveApplication.ResponseMenu.knownPackets past view)
              submission.evidence
      | some (.replay id) => ReactiveApplication.SubmissionNormalization.ReplayKnown past view id) ∧
      (runtime.reactiveNormalization leaks).action who past view response = response := by
  rw [menu, ReactiveApplication.SubmissionNormalization.menu_mem_iff_of_closed
    _ _ _ _ _ (bounds.rawMenu_closed runtime leaks who past view), rawMenu,
    ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  cases response.transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit submission => exact and_congr_left fun _ => bounds.submissions_mem _ submission
      | replay id => rfl

/-- Ineffective private opening material need not satisfy a bound. Certificate
requests are independently checked against the bounded facts and known messages. -/
theorem normalized_submission_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (submission : WitnessedSubmission graph)
    (packet : bounds.AllowsPacket submission.call.packet)
    (opening : bounds.AllowsOpening
      (submission.call.normalizeReactive who view.application).opening)
    (evidence : bounds.AllowsEvidence (ReactiveApplication.ResponseMenu.knownPackets past view)
      (submission.evidence.normalizeKnown
        (ReactiveApplication.ResponseMenu.knownPackets past view))) :
    (runtime.reactiveNormalization leaks).action who past view ⟨some (.submit submission)⟩ ∈
      (bounds.menu runtime leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨⟨⟨packet, opening⟩, evidence⟩,
    (runtime.reactiveNormalization leaks).action_idempotent who past view _⟩

theorem known_replay_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (id : MessageId Player)
    (known : ReactiveApplication.SubmissionNormalization.ReplayKnown past view id) :
    (⟨some (.replay id)⟩ : (runtime.reactiveApplication leaks).Action) ∈
      (bounds.menu runtime leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨known, by simp [ReactiveApplication.SubmissionNormalization.action, known]⟩

/-- Forwarding can refer to any actually known envelope. Its numeric identifier
does not need to fit a static bound, and the call may be malformed or rejected. -/
theorem known_forward_available (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (call : Submission graph)
    (packet : bounds.AllowsPacket call.packet)
    (opening : bounds.AllowsOpening (call.normalizeReactive who view.application).opening)
    (id : MessageId Player)
    (known : ∃ message ∈ ReactiveApplication.ResponseMenu.knownPackets past view, message.id = id) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨call, .forward id⟩)⟩ ∈
      (bounds.menu runtime leaks).actions who past view := by
  apply bounds.normalized_submission_available runtime leaks who past view _ packet opening
  rw [EvidenceRequest.normalizeKnown_forward _ id known]
  exact known

omit [Fintype Player] in
/-- A guessed reference with no known envelope cannot manufacture evidence.
Erasing that request preserves the emitted packet, as certified by normalization. -/
theorem unknown_forward_normalizes (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) (call : Submission graph)
    (id : MessageId Player)
    (unknown : ¬ ∃ message ∈ ReactiveApplication.ResponseMenu.knownPackets past view,
      message.id = id) :
    (runtime.reactiveNormalization leaks).action who past view
        ⟨some (.submit ⟨call, .forward id⟩)⟩ =
      ⟨some (.submit ⟨call.normalizeReactive who view.application, .none⟩)⟩ := by
  simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    WitnessedSubmission.normalizeReactive]
  rw [EvidenceRequest.normalizeKnown_unknown _ id unknown]

end MessageBounds
end Vegas.EventGraphRuntime
