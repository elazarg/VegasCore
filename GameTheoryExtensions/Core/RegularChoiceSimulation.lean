/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Core.RegularChoice
import GameTheoryExtensions.Math.Probability.RegularCoupling

/-! # Exact deviation laws for regular selection

The same selection lottery works for prescribed submissions and every optional
response. Only the fresh branch needs a translated source lottery. The
translation depends on the selection rule and response, not on utilities or
future random choices.
-/

noncomputable section

namespace GameTheory.PendingChoice.RegularSelection

open Math.Probability

variable {Action Outcome : Type*}

def displacedLaw (rule : RegularSelection Action) : FinDist Action :=
  Classical.choose (FinDist.regular_option_restore rule.retained rule.selection rule.regular)

theorem retained_restore (rule : RegularSelection Action) :
    rule.retained = rule.selection.bind (fun selected => selected.elim rule.displacedLaw
      FinDist.pure) :=
  Classical.choose_spec (FinDist.regular_option_restore rule.retained rule.selection rule.regular)

def translateResponse (rule : RegularSelection Action)
    (response : Option Action) : FinDist Action :=
  response.elim rule.displacedLaw FinDist.pure

def translateResponses (rule : RegularSelection Action)
    (responses : FinDist (Option Action)) : FinDist Action :=
  responses.bind rule.translateResponse

theorem includeLaw_factor (rule : RegularSelection Action) (response : Option Action) :
    rule.includeLaw response = rule.selection.bind (fun selected =>
      selected.elim (rule.translateResponse response) FinDist.pure) := by
  cases response with
  | none => exact rule.retained_restore
  | some action =>
      simp only [includeLaw, FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro selected _
      cases selected <;> rfl

theorem translateResponses_prescribed (rule : RegularSelection Action) (law : FinDist Action) :
    rule.translateResponses (law.map some) = law := by
  simp only [translateResponses, FinDist.bind_map, translateResponse, Option.elim_some,
    FinDist.bind_pure]

/-- The branch weights are fixed before choosing the alternative response. -/
theorem responseLaw_factor (rule : RegularSelection Action)
    (responses : FinDist (Option Action)) :
    rule.responseLaw responses = rule.selection.bind (fun selected =>
      selected.elim (rule.translateResponses responses) FinDist.pure) := by
  change (responses.bind fun response => rule.includeLaw response) = _
  simp_rw [includeLaw_factor]
  rw [FinDist.bind_comm]
  apply FinDist.bind_congr
  intro selected _
  cases selected with
  | none => rfl
  | some action => exact FinDist.bind_const responses (FinDist.pure action)

theorem prescribedLaw_factor (rule : RegularSelection Action) (law : FinDist Action) :
    rule.responseLaw (law.map some) = rule.selection.bind (fun selected =>
      selected.elim law FinDist.pure) := by
  rw [rule.responseLaw_factor, rule.translateResponses_prescribed]

/-- Factorization commutes with any common downstream stochastic kernel. -/
theorem continuationLaw_factor (rule : RegularSelection Action)
    (responses : FinDist (Option Action)) (continuation : Action → FinDist Outcome) :
    (rule.responseLaw responses).bind continuation = rule.selection.bind (fun selected =>
      selected.elim ((rule.translateResponses responses).bind continuation) continuation) := by
  rw [rule.responseLaw_factor, FinDist.bind_bind]
  apply FinDist.bind_congr
  intro selected _
  cases selected <;> simp

end GameTheory.PendingChoice.RegularSelection
