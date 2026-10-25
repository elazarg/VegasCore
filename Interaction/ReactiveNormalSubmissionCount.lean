/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveNormalRecall
import Interaction.ReactiveSubmissionSerial

/-! # Submission serials ignore private response aliases -/

namespace Interaction.ReactiveApplication.SubmissionNormalization

variable {Principal : Type} {app : ReactiveApplication Principal}
  (normal : app.SubmissionNormalization)

theorem action_isSubmission (who : Principal) (past : List app.PlayerEntry)
    (view : app.PlayerView) (response : app.Action) :
    (normal.action who past view response).isSubmission app = response.isSubmission app := by
  cases response with
  | mk transmission => cases transmission <;> rfl

theorem recall_submissionCount (who : Principal) (past : List app.PlayerEntry) :
    app.submissionCount (normal.recall who past) = app.submissionCount past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [normal.recall_append, app.submissionCount_append, app.submissionCount_append, ih]
      simp only [submissionCount, List.countP_cons, List.countP_nil, action_isSubmission]

end Interaction.ReactiveApplication.SubmissionNormalization
