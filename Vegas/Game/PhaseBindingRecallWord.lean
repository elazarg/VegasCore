/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphBacktranslation
import Vegas.Pending.PhaseBindingSlotPolicy
import Vegas.EventGraph.Sequential

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

variable [Fintype Player]

end Vegas
