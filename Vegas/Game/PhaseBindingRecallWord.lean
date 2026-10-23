/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphBacktranslation
import Vegas.Pending.PhaseBindingEncodingLaw
import Interaction.ReactivePolicyMixture

/-! # Effective binding actions read from actual private raw recall

The decoder reads the immutable submitted preparation, not a later candidate
catalogue. Silence and opening responses contribute no commitment action. The
physical attempt and static interval select one block's chronological word.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (whole : SourceProgram Player L Γ O) (mode : ExecutionMode)
  (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph whole).withMode mode)))

/-- Decode the source action recorded by a raw binding preparation. A received
unusable or wrong-typed preparation is an effective failed binding. -/
def phaseBindingAction? (response : (phaseApplication runtime leaks).Action) :
    Option (OwnAction Player L) :=
  match response.transmission with
  | none => none
  | some material =>
      match material.call.packet with
      | .commitment event _ =>
          match kind : ((toEventGraph whole).withMode mode).outputLayout event with
          | .binding _ payload =>
              let result : PublicationResult (L.Val payload) :=
                ((material.call.opening.bind fun raw => raw.as? payload).map
                  PublicationResult.success).getD .failure
              decodeEventAction whole event (cast (congrArg EventField.Action kind.symm) result)
          | _ => none
      | _ => none

/-- Every supported canonical or slot send records its exact original typed
source action, including an accepted failure. -/
theorem phaseBindingAction?_response (who : Player)
    (event : ((toEventGraph whole).withMode mode).EventId) (payload : L.Ty)
    (binding : ((toEventGraph whole).withMode mode).outputLayout event = .binding who payload)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    phaseBindingAction? whole mode runtime leaks
        (phaseBindingResponse runtime leaks who event payload result serial) =
      decodeEventAction whole event (cast (congrArg EventField.Action binding.symm) result) := by
  change (toEventGraph whole).outputLayout event = .binding who payload at binding
  cases result <;>
    simp only [phaseBindingAction?, phaseBindingResponse]
  all_goals
    split
    · rename_i kind
      have same := kind.symm.trans binding
      cases same
      first | rfl | simp [Raw.as?_mk]
    · rename_i absent
      exact (absent who payload binding).elim

/-- A literal wait records no effective binding action. -/
theorem phaseBindingAction?_silence :
    phaseBindingAction? whole mode runtime leaks ⟨none⟩ = none := rfl

/-- The current block's word is selected from the actual observed attempt and
raw actions, in physical recall order. It does not insert latent foreign moves. -/
def phaseCommitRecallWord (low high generation : Nat)
    (past : List (phaseApplication runtime leaks).PlayerEntry) : List (OwnAction Player L) :=
  past.filterMap fun entry =>
    if entry.beforeView.application.2.attempt = ⟨low, generation⟩ then
      match entry.action.transmission with
      | none => none
      | some material =>
          match material.call.packet with
          | .commitment event _ =>
              if low ≤ event.val ∧ event.val < high then
                phaseBindingAction? whole mode runtime leaks entry.action
              else none
          | _ => none
    else none

/-- Chronological private recall appends the corresponding effective action
when the response is an addressed send in this attempt and block. -/
theorem phaseCommitRecallWord_send (low high generation : Nat)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (entry : (phaseApplication runtime leaks).PlayerEntry) (who : Player)
    (event : ((toEventGraph whole).withMode mode).EventId) (payload : L.Ty)
    (binding : ((toEventGraph whole).withMode mode).outputLayout event = .binding who payload)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (sent : entry.action = phaseBindingResponse runtime leaks who event payload result serial)
    (attempt : entry.beforeView.application.2.attempt = ⟨low, generation⟩)
    (inside : low ≤ event.val ∧ event.val < high) :
    phaseCommitRecallWord whole mode runtime leaks low high generation (past ++ [entry]) =
      phaseCommitRecallWord whole mode runtime leaks low high generation past ++
        Option.toList (decodeEventAction whole event
          (cast (congrArg EventField.Action binding.symm) result)) := by
  have encoded := phaseBindingAction?_response whole mode runtime leaks who event payload binding
    result serial
  simp only [phaseBindingResponse] at encoded
  simp only [phaseCommitRecallWord, List.filterMap_append, List.filterMap_cons,
    List.filterMap_nil, attempt, ite_true, sent]
  change _ = _
  simp only [phaseBindingResponse, ite_eq_left inside]
  rw [encoded]
  rfl

/-- A literal wait leaves the decoded current-block own word unchanged. -/
theorem phaseCommitRecallWord_wait (low high generation : Nat)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (entry : (phaseApplication runtime leaks).PlayerEntry) (silent : entry.action = ⟨none⟩) :
    phaseCommitRecallWord whole mode runtime leaks low high generation (past ++ [entry]) =
      phaseCommitRecallWord whole mode runtime leaks low high generation past := by
  by_cases attempt : entry.beforeView.application.2.attempt = ⟨low, generation⟩ <;>
    simp [phaseCommitRecallWord, silent, attempt]

variable [Fintype Player]

end Vegas
