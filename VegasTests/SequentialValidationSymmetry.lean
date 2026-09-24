/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationInformation

/-! # The source posterior is symmetric in the unrevealed type -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability

def SourcePath.flipType : SourcePath → SourcePath
  | .root => .root
  | .drawn bit => .drawn (!bit)
  | .bound bit dummy => .bound (!bit) dummy
  | .dummyPublished bit dummy first => .dummyPublished (!bit) dummy first
  | .secretPublished bit dummy first second => .secretPublished (!bit) dummy first second
  | .done bit dummy first second guess => .done (!bit) dummy first second guess

@[simp] theorem SourcePath.flipType_flipType (path : SourcePath) :
    path.flipType.flipType = path := by
  cases path <;> simp [flipType]

def flipSourceHistory (history : sourceArena.History) : sourceArena.History :=
  (decodeSource history.state).flipType.history

@[simp] theorem flipSourceHistory_path (path : SourcePath) :
    flipSourceHistory path.history = path.flipType.history := by
  simp only [flipSourceHistory, SourcePath.history_state, decodeSource_state]

theorem flipSourceHistory_involutive : Function.Involutive flipSourceHistory := by
  intro history
  obtain ⟨path, same⟩ := source_history_complete history.trace
  change history = path.history at same
  subst history
  simp only [flipSourceHistory_path, SourcePath.flipType_flipType]

theorem flipSourceHistory_info (site : sourceModel.InformationSite true)
    (failed : sourceSecretResult site.1 = .failure)
    (history : sourceModel.InformationHistory true site.1) :
    sourceModel.infoOf true (flipSourceHistory history.1).trace = site.1 := by
  obtain ⟨bit, dummy, first, second, same⟩ := source_bob_history site history
  have flag : ((first && dummy.isSuccess) || !second) = true := by
    have result := congrArg sourceSecretResult history.2
    rw [same, source_secret_info, failed] at result
    split at result
    · assumption
    · cases result
  rw [same, flipSourceHistory_path]
  exact (secret_bob_info (!bit) bit dummy first second flag).trans
    ((congrArg (fun h => sourceModel.infoOf true h.trace) same).symm.trans history.2)

def sourceFlip (site : sourceModel.InformationSite true)
    (failed : sourceSecretResult site.1 = .failure) :
    sourceModel.InformationHistory true site.1 ≃ sourceModel.InformationHistory true site.1 where
  toFun history := ⟨flipSourceHistory history.1, flipSourceHistory_info site failed history⟩
  invFun history := ⟨flipSourceHistory history.1, flipSourceHistory_info site failed history⟩
  left_inv history := Subtype.ext (flipSourceHistory_involutive history.1)
  right_inv history := Subtype.ext (flipSourceHistory_involutive history.1)

theorem source_belief_flip (site : sourceModel.InformationSite true)
    (failed : sourceSecretResult site.1 = .failure) :
    (sourceAssessment.belief true site).map (sourceFlip site failed) =
      sourceAssessment.belief true site := by
  classical
  apply FinDist.ext_of_prob
  intro history
  obtain ⟨previous, rfl⟩ := (sourceFlip site failed).surjective history
  rw [FinDist.prob_map_of_injective _ (sourceFlip site failed).injective,
    source_belief_prob, source_belief_prob]

end VegasTests.SequentialValidation
