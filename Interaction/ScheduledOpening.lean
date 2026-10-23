/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactivePolicyMixture
import GameTheory.Math.Probability.ConditionalObservation
import GameTheory.Math.Probability.ExpectationConditioning

/-! # A scheduled mixture stops after its first opening

An opening action disjoint from the waiting policy identifies the selected
slot in the player's own response recall. All later behavior uses the waiting
policy, including after other zero-probability recorded responses. This proves
the off-path stop rule for fully mixed scheduled approximants; it does not
identify a zero-weight mixture's fallback with their limit.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal)

theorem policyMixture_posterior_pure_snoc {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past : List app.PlayerEntry) (entry : app.PlayerEntry)
    (index : Index) (fixed : (app.policyMixture initial policies).posterior past =
      PMF.pure index) :
    (app.policyMixture initial policies).posterior (past ++ [entry]) =
      PMF.pure index := by
  rw [Implementation.posterior_snoc, fixed]
  change (fiberPosterior ((PMF.pure index).bind (fun value =>
    (policies value past entry.beforeView).map fun action => (action, value)))
      Prod.fst entry.action).map Prod.snd = PMF.pure index
  rw [PMF.pure_bind]
  have paired : (policies index past entry.beforeView).map (fun action => (action, index)) =
      bindPairLaw (policies index past entry.beforeView) (fun _ => (PMF.pure index)) := by
    simp only [bindPairLaw, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind]
  rw [paired, fiberPosterior_snd_bindPairLaw_const]

theorem policyMixture_posterior_pure_append {Index : Type} (initial : PMF Index)
    (policies : Index → app.Policy) (past suffix : List app.PlayerEntry) (index : Index)
    (fixed : (app.policyMixture initial policies).posterior past = PMF.pure index) :
    (app.policyMixture initial policies).posterior (past ++ suffix) = PMF.pure index := by
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using fixed
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc]
      exact app.policyMixture_posterior_pure_snoc initial policies _ entry index ih

end Interaction.ReactiveApplication
