/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReactiveValueSwap
import Vegas.Pending.OnePacketValueSwap
import Vegas.Pending.PhaseCountMenu

/-! # Counted phase responses under hidden-value replay -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

namespace HiddenSwap

variable (swap : HiddenSwap graph)

theorem phaseOutputs_entry (past : List (phaseApplication runtime leaks).PlayerEntry) :
    (phaseApplication runtime leaks).outputs (past.map swap.phaseEntry) =
      (phaseApplication runtime leaks).outputs past := by
  simp only [ReactiveApplication.outputs, List.filterMap_map]
  rfl

theorem phaseKnownPackets_entry (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ReactiveApplication.ResponseMenu.knownPackets (past.map swap.phaseEntry) (swap.phaseView view) =
      ReactiveApplication.ResponseMenu.knownPackets past view := by
  simp only [ReactiveApplication.ResponseMenu.knownPackets, phaseOutputs_entry]
  rfl

theorem phaseSubmissionCount_entry (past : List (phaseApplication runtime leaks).PlayerEntry) :
    (phaseApplication runtime leaks).submissionCount (past.map swap.phaseEntry) =
      (phaseApplication runtime leaks).submissionCount past := by
  simp only [ReactiveApplication.submissionCount, List.countP_map]
  congr 1
  funext entry
  rcases entry with ⟨_, ⟨transmission⟩, _⟩
  cases transmission <;> rfl

/-- The signed next packet, including its dynamic attempt and authorization,
remains identical when its resolved evidence is fixed. -/
theorem phaseLocalEnvelope_entry (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (owner : view.application.1.who = who)
    (submission : WitnessedSubmission graph) (fixed : submission.evidence.FixedBy swap) :
    PhaseCount.localEnvelope runtime leaks who (past.map swap.phaseEntry) (swap.phaseView view)
        (submission.swap swap) =
      PhaseCount.localEnvelope runtime leaks who past view submission := by
  have candidates : (submission.swap swap).call.candidateAfter who
      (PlayerView.swap swap view.application.1).candidates =
      swap.ownCandidates who
        (submission.call.candidateAfter who view.application.1.candidates) := by
    funext query
    have result := swap.candidateAfter_swap submission.call who view.application.1.candidates query
    rw [WitnessedSubmission.swap_call]
    change (submission.call.swap swap).candidateAfter who
      (swap.ownCandidates view.application.1.who view.application.1.candidates) query = _
    rw [owner]
    exact result
  unfold PhaseCount.localEnvelope
  rw [phaseSubmissionCount_entry, phaseKnownPackets_entry]
  change Message.mk _ (CommitAttemptPacket.mk _ (PhaseCount.maskPacket _
    (WitnessedPacket.mk submission.call.packet
      (submission.evidence.resolve who ((submission.swap swap).call.candidateAfter who
        (PlayerView.swap swap view.application.1).candidates) _) _))) = _
  rw [candidates, swap.resolve_swap _ who _ _ fixed]
  rfl

/-- Native evidence normalization commutes with the phase recall projection;
its actual known signed packets are unchanged. -/
theorem phaseNormalize_entry (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (owner : view.application.1.who = who)
    (submission : WitnessedSubmission graph) (fixed : submission.evidence.FixedBy swap) :
    (submission.swap swap).normalizeReactive who (PlayerView.swap swap view.application.1)
        ((ReactiveApplication.ResponseMenu.knownPackets (past.map swap.phaseEntry)
          (swap.phaseView view)).map PhaseCount.nativeMessage) =
      WitnessedSubmission.swap swap (submission.normalizeReactive who view.application.1
        ((ReactiveApplication.ResponseMenu.knownPackets past view).map
          PhaseCount.nativeMessage)) := by
  rw [swap.phaseKnownPackets_entry]
  exact swap.witnessedNormalize_swap who view.application.1 owner _ submission fixed

end HiddenSwap

namespace PhaseCount

variable [Fintype Player] (bounds : MessageBounds graph) (swap : HiddenSwap graph)

/-- Bounded raw menus contain the replayed private preparation whenever the
bounded value set is closed under the existing native swap. -/
theorem swap_mem_rawMenu (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ (rawMenu runtime leaks bounds).actions who past view)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    swap.phaseAction response ∈ (rawMenu runtime leaks bounds).actions who
      (past.map swap.phaseEntry) (swap.phaseView view) := by
  change response ∈ (ReactiveApplication.ResponseMenu.fromSubmissions _).actions _ _ _ at member
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem] at member
  change swap.phaseAction response ∈
    (ReactiveApplication.ResponseMenu.fromSubmissions _).actions _ _ _
  rw [ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => trivial
  | some submission =>
      change submission.swap swap ∈ bounds.submissions _
      change submission ∈ bounds.submissions
        ((ReactiveApplication.ResponseMenu.knownPackets past view).map nativeMessage) at member
      rw [bounds.submissions_mem] at member ⊢
      obtain ⟨⟨packet, opening⟩, evidence⟩ := member
      refine ⟨⟨packet, ?_⟩, ?_⟩
      · change bounds.AllowsOpening (submission.call.swap swap).opening
        rcases callEq : submission.call with ⟨call, prepared⟩
        rw [callEq] at opening
        cases prepared with
        | none => cases call <;> trivial
        | some raw =>
            cases call with
            | commitment event candidate => exact bounded candidate raw opening
            | opening | malformed => exact opening
      · change bounds.AllowsEvidence
          ((ReactiveApplication.ResponseMenu.knownPackets (past.map swap.phaseEntry)
            (swap.phaseView view)).map nativeMessage) submission.evidence
        rw [swap.phaseKnownPackets_entry]
        exact evidence

/-- Exact emitted packets preserve the permanent count verdict, including
firstness and the latest surviving signed binding identity. -/
theorem swap_mem_onePacketActions (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) (owner : view.application.1.who = who)
    (response : (phaseApplication runtime leaks).Action)
    (member : response ∈ onePacketActions runtime leaks bounds who past view)
    (fixed : ∀ submission, response.transmission = some submission →
      submission.evidence.FixedBy swap)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values) :
    swap.phaseAction response ∈ onePacketActions runtime leaks bounds who
      (past.map swap.phaseEntry) (swap.phaseView view) := by
  rw [mem_onePacketActions] at member ⊢
  refine ⟨swap_mem_rawMenu bounds swap who past view response member.1 bounded, ?_⟩
  rcases member.2 with silent | ⟨submission, transmitted, permitted⟩
  · left
    change response.transmission.map _ = none
    rw [silent]
    rfl
  · right
    refine ⟨submission.swap swap, ?_, ?_⟩
    · change response.transmission.map _ = some _
      rw [transmitted]
      rfl
    · rw [swap.phaseOutputs_entry,
        swap.phaseLocalEnvelope_entry who past view owner submission (fixed submission transmitted)]
      exact permitted

end PhaseCount
end Vegas.EventGraphRuntime
