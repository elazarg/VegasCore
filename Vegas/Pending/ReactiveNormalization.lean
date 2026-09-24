/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveRuntime
import Interaction.ReactiveResponseNormalization

/-! # Semantic normal forms of event submissions

Opening material has an effect only when a submission fixes a fresh owned
prepared handle. Other opening material is a private representation artifact.
Normalization preserves the entire public packet, including malformed contents,
and changes no application or network effect. It uses only the sender's view.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def openingEffective (who : Player) (view : ReactivePlayerView graph) : Payload graph → Prop
  | .commitment _ (owner, .prepared serial) =>
      owner = who ∧ view.candidates (.prepared serial) = .fresh
  | _ => False

open Classical in
def Submission.normalizeReactive (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) : Submission graph :=
  ⟨submission.packet, if openingEffective who view submission.packet then submission.opening
    else none⟩

theorem Submission.normalizeReactive_packet (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).packet = submission.packet := rfl

theorem Submission.normalizeReactive_idempotent (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) :
    (submission.normalizeReactive who view).normalizeReactive who view =
      submission.normalizeReactive who view := by
  classical
  simp only [normalizeReactive]
  split <;> rfl

/-- No metadata is removed when it can fix a commitment meaning. -/
theorem Submission.normalizeReactive_effective (who : Player) (view : ReactivePlayerView graph)
    (submission : Submission graph) (effective : openingEffective who view submission.packet) :
    submission.normalizeReactive who view = submission := by
  simp only [normalizeReactive, effective, ↓reduceIte]

theorem Submission.normalizeReactive_none (who : Player) (view : ReactivePlayerView graph)
    (packet : Payload graph) :
    (⟨packet, none⟩ : Submission graph).normalizeReactive who view = ⟨packet, none⟩ := by
  simp only [normalizeReactive, ite_self]

variable [DecidableEq Player]

theorem Submission.normalizeReactive_register (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) (who : Player)
    (state : State graph) (submission : Submission graph) :
    (submission.normalizeReactive who
        ((runtime.reactiveApplication leaks).observePlayer state who)).register state who =
      submission.register state who := by
  classical
  rcases submission with ⟨packet, material⟩
  cases packet with
  | commitment event candidate =>
      rcases candidate with ⟨owner, slot⟩
      cases slot with
      | initial index => simp [normalizeReactive, openingEffective, register]
      | prepared serial =>
          by_cases same : owner = who
          · subst owner
            by_cases fresh : state.candidates.lookup (who, .prepared serial) = .fresh
            · simp [normalizeReactive, openingEffective, reactiveApplication, fresh]
            · cases material with
              | none => simp [normalizeReactive, openingEffective, reactiveApplication, fresh]
              | some raw =>
                  simp [normalizeReactive, openingEffective, reactiveApplication, fresh, register,
                    state.candidates.prepare_eq_self_of_not_fresh who (.prepared serial) raw fresh]
          · cases material <;> simp [normalizeReactive, openingEffective, register, same]
  | opening event candidate raw | withhold event | malformed raw =>
      cases material <;> simp [normalizeReactive, openingEffective, register]

def reactiveNormalization (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (Payload graph)) :
    (runtime.reactiveApplication leaks).SubmissionNormalization where
  normalize := Submission.normalizeReactive
  idempotent := Submission.normalizeReactive_idempotent
  packet := Submission.normalizeReactive_packet
  submit state who submission := by
    change submitStep _ who _ = submitStep _ who _
    rw [Submission.normalizeReactive_register, Submission.normalizeReactive_packet]

end Vegas.EventGraphRuntime
