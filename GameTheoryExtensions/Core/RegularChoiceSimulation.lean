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

def displacedLaw (rule : RegularSelection Action) : PMF Action :=
  Classical.choose (PMF.regular_option_restore rule.retained rule.selection rule.regular)

theorem retained_restore (rule : RegularSelection Action) :
    rule.retained = rule.selection.bind (fun selected => selected.elim rule.displacedLaw
      PMF.pure) :=
  Classical.choose_spec (PMF.regular_option_restore rule.retained rule.selection rule.regular)

def translateResponse (rule : RegularSelection Action)
    (response : Option Action) : PMF Action :=
  response.elim rule.displacedLaw PMF.pure

def translateResponses (rule : RegularSelection Action)
    (responses : PMF (Option Action)) : PMF Action :=
  responses.bind rule.translateResponse

theorem includeLaw_factor (rule : RegularSelection Action) (response : Option Action) :
    rule.includeLaw response = rule.selection.bind (fun selected =>
      selected.elim (rule.translateResponse response) PMF.pure) := by
  cases response with
  | none => exact rule.retained_restore
  | some action =>
      simp only [includeLaw, ← PMF.bind_pure_comp, Function.comp_def]
      apply bind_congr_on_support _
      intro selected _
      cases selected <;> rfl

theorem translateResponses_prescribed (rule : RegularSelection Action) (law : PMF Action) :
    rule.translateResponses (law.map some) = law := by
  simp only [translateResponses, PMF.bind_map, translateResponse, Option.elim_some,
    PMF.bind_pure]

/-- The branch weights are fixed before choosing the alternative response. -/
theorem responseLaw_factor (rule : RegularSelection Action)
    (responses : PMF (Option Action)) :
    rule.responseLaw responses = rule.selection.bind (fun selected =>
      selected.elim (rule.translateResponses responses) PMF.pure) := by
  change (responses.bind fun response => rule.includeLaw response) = _
  simp_rw [includeLaw_factor]
  rw [PMF.bind_comm]
  apply bind_congr_on_support _
  intro selected _
  cases selected with
  | none => rfl
  | some action => exact PMF.bind_const responses (PMF.pure action)

theorem prescribedLaw_factor (rule : RegularSelection Action) (law : PMF Action) :
    rule.responseLaw (law.map some) = rule.selection.bind (fun selected =>
      selected.elim law PMF.pure) := by
  rw [rule.responseLaw_factor, rule.translateResponses_prescribed]

/-- Factorization commutes with any common downstream stochastic kernel. -/
theorem continuationLaw_factor (rule : RegularSelection Action)
    (responses : PMF (Option Action)) (continuation : Action → PMF Outcome) :
    (rule.responseLaw responses).bind continuation = rule.selection.bind (fun selected =>
      selected.elim ((rule.translateResponses responses).bind continuation) continuation) := by
  rw [rule.responseLaw_factor, PMF.bind_bind]
  apply bind_congr_on_support _
  intro selected _
  cases selected <;> simp

end GameTheory.PendingChoice.RegularSelection
