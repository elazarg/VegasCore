/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedProjection
import Vegas.Compile.ApplicationImageReadout

/-! # Source readout under activation projection -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Erasing public activation metadata preserves the first private registration. -/
theorem registrationCache_erasePlayerEntry
    (runtime : WindowedApplication P L) (original : ApplicationImage P L) (slot : Nat)
    (history : List runtime.application.PlayerEntry) :
    ((ApplicationImage.registrationEncoding slot).privateCommand runtime.application).cachedValue
        runtime.application history =
      original.registrationCache slot (history.map fun entry =>
        show original.application.PlayerEntry from runtime.erasePlayerEntry entry) := by
  induction history with
  | nil => rfl
  | cons entry history ih =>
      rcases entry with ⟨view, command⟩
      cases command <;>
        simp only [ApplicationImage.registrationCache, ChoiceEncoding.cachedValue, List.map_cons,
          WindowedApplication.erasePlayerEntry, WindowedApplication.erasePlayerCommand,
          ChoiceEncoding.privateCommand_decode_private, ChoiceEncoding.privateCommand_decode_submit,
          ChoiceEncoding.privateCommand_decode_replay, ChoiceEncoding.privateCommand_decode_wait]
          at ih ⊢ <;> rw [ih]

/-- Activation erasure retains every encoded submission in its original position. -/
theorem cachedValue_erasePlayerEntry
    (runtime : WindowedApplication P L) (original : ApplicationImage P L) {Value : Type}
    (encoding : ChoiceEncoding Value (ApplicationImage.Payload P L))
    (history : List runtime.application.PlayerEntry) :
    (encoding.submission runtime.application).cachedValue runtime.application history =
      (encoding.submission original.application).cachedValue original.application
        (history.map fun entry =>
          show original.application.PlayerEntry from runtime.erasePlayerEntry entry) := by
  induction history with
  | nil => rfl
  | cons entry history ih =>
      rcases entry with ⟨view, command⟩
      cases command <;>
        simp only [ChoiceEncoding.cachedValue, List.map_cons,
          WindowedApplication.erasePlayerEntry, WindowedApplication.erasePlayerCommand,
          ChoiceEncoding.submission_decode_private, ChoiceEncoding.submission_decode_submit,
          ChoiceEncoding.submission_decode_replay, ChoiceEncoding.submission_decode_wait, ih]

/-- Source readout uses the common wire and memory formats of both images. -/
theorem ownerReadout?_erasePlayerEntry
    (runtime : WindowedApplication P L) (original : ApplicationImage P L) (who : P)
    (refs : Finset (FieldRef L)) (history : List runtime.application.PlayerEntry)
    (view : runtime.application.View) :
    runtime.image.ownerReadout? who refs
        (history.map fun entry =>
          show runtime.image.application.PlayerEntry from runtime.erasePlayerEntry entry)
        (runtime.eraseView view) =
      original.ownerReadout? who refs
        (history.map fun entry =>
          show original.application.PlayerEntry from runtime.erasePlayerEntry entry)
        (runtime.eraseView view) := by
  unfold ApplicationImage.ownerReadout? ApplicationImage.ownerReadStore
    ApplicationImage.registrationCache
  congr 2
  funext field
  generalize (runtime.eraseView view).application.store field = stored
  cases stored with
  | some value => rfl
  | none =>
      generalize (runtime.eraseView view).application.accepted field = accepted
      cases accepted with
      | none => rfl
      | some disposition =>
          cases disposition with
          | publicDefault value => rfl
          | «opaque» handle =>
              dsimp only
              by_cases heq : handle = (who, field)
              · simp only [heq, ↓reduceIte]
                induction history with
                | nil => rfl
                | cons entry history ih =>
                    rcases entry with ⟨entryView, command⟩
                    simp only [WindowedApplication.erasePlayerEntry,
                      WindowedApplication.erasePlayerCommand] at ih
                    cases command <;>
                      simp only [List.map_cons, WindowedApplication.erasePlayerEntry,
                        WindowedApplication.erasePlayerCommand, ChoiceEncoding.cachedValue,
                        ChoiceEncoding.privateCommand_decode_private,
                        ChoiceEncoding.privateCommand_decode_submit,
                        ChoiceEncoding.privateCommand_decode_replay,
                        ChoiceEncoding.privateCommand_decode_wait, ih]
              · simp only [heq, ↓reduceIte]

end Vegas.WindowedApplication
