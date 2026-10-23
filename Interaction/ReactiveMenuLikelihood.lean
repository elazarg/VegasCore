/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveMixtureLikelihood
import Interaction.ReactiveMenuPolicy
import Interaction.ReactiveOwnPlay

/-! # Finite-menu probabilities of the actual new response suffix -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

/-- Forgetting a finite menu witness gives the exact physical response atom
at every covered input. No probability of a chosen witness is substituted. -/
theorem restrictPolicy_atom (who : Principal) (policy : app.Policy)
    (past : List app.PlayerEntry) (view : app.PlayerView) (action : app.Action)
    (covered : ∀ response ∈ (policy past view).support,
      response ∈ menu.actions who past view) :
    (((menu.restrictPolicy initial horizon scheduler who policy) (some (past, view))).map
        Subtype.val) (some action) = policy past view action := by
  rw [menu.restrictPolicy_map_val initial horizon scheduler who policy past view covered]
  exact pmf_map_apply_of_injective _ (Option.some_injective _) action

/-- The complete NEW native own-play factor is exactly its literal physical
response product at the original recall prefixes. All old records stay in the
input, and the finite Choice witnesses disappear only through their projection. -/
theorem ownPlayFrom_restrictPolicy (who : Principal) (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ menu.actions who past view)
    (past records : List app.PlayerEntry) :
    (menu.information initial horizon scheduler).ownPlayReachProbability
        (menu.restrictPolicy initial horizon scheduler who policy)
          (app.ownPlayFrom past records) =
      (((app.privateTranscriptFrom past records).map (fun record =>
        policy record.1.1 record.1.2 record.2)).prod).toReal := by
  induction records using List.reverseRecOn with
  | nil => rfl
  | append_singleton records entry ih =>
      rw [app.ownPlayFrom_append,
        GameTheory.Protocol.InformationModel.ownPlayReachProbability,
        menu.restrictPolicy_atom initial horizon scheduler who policy
          (past ++ records) entry.beforeView entry.action (covered _ _), ih]
      have singleton : app.privateTranscriptFrom (past ++ records) [entry] =
          [((past ++ records, entry.beforeView), entry.action)] := rfl
      rw [app.privateTranscriptFrom_append, singleton]
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons,
        List.prod_nil, mul_one, ENNReal.toReal_mul]


end Interaction.ReactiveApplication.ResponseMenu
