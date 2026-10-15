/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecallEntries
import GameTheory.Analysis.Protocol.BeliefTransport

/-! # Focal interventions along an actual reactive recall

The replay policy fixes the focal responses in one actual information fiber.
It does not explain raw-mixture responses as draws from a latent source word.
The original opponents, scheduler and initial draw remain unchanged.
-/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
  (scheduler : app.Scheduler)

local notation "M" => menu.information initial horizon scheduler

/-- At each recorded response index, replay its exact raw action whenever it
is legal. All other inputs retain the selected baseline policy. -/
def recallReplayPolicy (who : Principal) (reference : List app.PlayerEntry)
    (baseline : (M).BehavioralPolicy who) : (M).BehavioralPolicy who := by
  classical
  intro observed
  cases observed with
  | none => exact baseline none
  | some data =>
      exact if next : (reference[data.1.length]?).isSome then
        let response := (reference[data.1.length]?.get next).action
        if permitted : response ∈ menu.actions who data.1 data.2 then
          PMF.pure ⟨some response, response, permitted, rfl⟩
        else baseline (some data)
      else baseline (some data)

/-- Every actual recorded response is selected with probability one. -/
theorem recallReplayPolicy_at_record (who : Principal) (reference past : List app.PlayerEntry)
    (baseline : (M).BehavioralPolicy who) (entry : app.PlayerEntry)
    (next : reference[past.length]? = some entry)
    (permitted : entry.action ∈ menu.actions who past entry.beforeView) :
    ((menu.recallReplayPolicy initial horizon scheduler who reference baseline
      (some (past, entry.beforeView))).map Subtype.val) (some entry.action) = 1 := by
  classical
  simp only [recallReplayPolicy, next, Option.isSome_some, dite_true, Option.get_some,
    permitted, PMF.pure_map, PMF.pure_apply_self]

/-- Replaying a legal prefix assigns unit own reach to its complete actual
response word, including prior raw-mixture sends and silent callbacks. -/
theorem recallReplayPolicy_ownReach (who : Principal) (reference : List app.PlayerEntry)
    (baseline : (M).BehavioralPolicy who)
    (legal : ∀ index : Fin reference.length,
      reference[index].action ∈ menu.actions who (reference.take index) reference[index].beforeView)
    (past : List app.PlayerEntry) (within : past.IsPrefix reference) :
    (M).ownPlayReachProbability
      (menu.recallReplayPolicy initial horizon scheduler who reference baseline)
        (app.recallOwnPlay past) = 1 := by
  classical
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past.IsPrefix reference := (List.prefix_append _ _).trans within
      have earlierReach := ih earlier
      obtain ⟨rest, same⟩ := within
      have next : reference[past.length]? = some entry := by
        rw [← same]
        simp only [List.append_assoc, List.singleton_append, List.getElem?_append_right
          (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
      have inside : past.length < reference.length := by
        rw [← same, List.length_append, List.length_append, List.length_singleton]
        omega
      have entryEq : reference[past.length] = entry := by
        exact Option.some.inj ((List.getElem?_eq_getElem inside).symm.trans next)
      have prefixEq : reference.take past.length = past := by
        rw [← same, List.append_assoc, List.take_append_of_le_length (Nat.le_refl _),
          List.take_length]
      have permitted := legal ⟨past.length, inside⟩
      change reference[past.length].action ∈ menu.actions who (reference.take past.length)
        reference[past.length].beforeView at permitted
      rw [entryEq, prefixEq] at permitted
      rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability,
        menu.recallReplayPolicy_at_record initial horizon scheduler who reference past baseline
          entry next permitted, ENNReal.toReal_one, earlierReach, one_mul]

variable [Fintype Principal]

/-- The focal policy can be replaced by exact recall replay without changing
Bayes beliefs. Positivity of the replayed fiber is derived from the original
positive fiber, rather than assumed for a new latent-source construction. -/
theorem bayesBelief_eq_recallReplay
    (profile : ∀ who, (M).BehavioralPolicy who) (who : Principal)
    (site : (M).InformationSite who)
    (positive : 0 < (M).informationMass profile who site)
    (reference : (M).InformationHistory who site.1)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view)) :
    let selected := Function.update profile who
      (menu.recallReplayPolicy initial horizon scheduler who past (profile who))
    ∃ selectedPositive : 0 < (M).informationMass selected who site,
      (M).bayesBelief profile who site
          (menu.decisionInformationAntichain initial horizon scheduler who site) positive =
        (M).bayesBelief selected who site
          (menu.decisionInformationAntichain initial horizon scheduler who site) selectedPositive ∧
      ∀ history : (M).InformationHistory who site.1,
        (M).playerReachProbability selected who history.1.trace = 1 := by
  classical
  intro selected
  have legal (index : Fin past.length) : past[index].action ∈
      menu.actions who (past.take index) past[index].beforeView :=
    menu.recall_entry_legal initial horizon scheduler who reference.1 past view
      (reference.2.trans observed) index index.isLt
  have ownOne (history : (M).InformationHistory who site.1) :
      (M).playerReachProbability selected who history.1.trace = 1 := by
    rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability,
      menu.ownPlay_of_info_some initial horizon scheduler who history.1 past view
        (history.2.trans observed)]
    rw [show selected who =
      menu.recallReplayPolicy initial horizon scheduler who past (profile who) from
        by simp only [selected, Function.update_self]]
    exact menu.recallReplayPolicy_ownReach initial horizon scheduler who past (profile who)
      legal past (List.prefix_refl _)
  have off : ∀ other, other ≠ who → profile other = selected other := by
    intro other different
    exact (Function.update_of_ne different _ _).symm
  obtain ⟨history, reached⟩ := (InformationModel.informationMass_pos_iff
    (M) profile who site).mp positive
  have reachedReal : 0 < ((M).historyReachWeight profile history.1).toReal :=
    ENNReal.toReal_pos reached.ne' (PMF.apply_ne_top _ _)
  have factor := (M).historyReachProbability_eq_player_mul_counterfactual
    profile who history.1.trace
  have counterPositive : 0 < (M).counterfactualReachProbability profile who
      history.1.trace := by
    have ownNonnegative : 0 ≤ (M).playerReachProbability profile who history.1.trace := by
      rw [InformationModel.playerReachProbability_eq_ownPlayReachProbability]
      exact InformationModel.ownPlayReachProbability_nonneg _ _ _
    rw [factor] at reachedReal
    exact pos_of_mul_pos_right reachedReal ownNonnegative
  have selectedReached : 0 < (M).historyReachWeight selected history.1 := by
    suffices reached : 0 < ((M).historyReachWeight selected history.1).toReal from
      (ENNReal.toReal_pos_iff.mp reached).1
    rw [(M).historyReachProbability_eq_player_mul_counterfactual selected who history.1.trace,
      ownOne history, one_mul,
      ← (M).counterfactualReachProbability_eq_of_eq_off off history.1.trace]
    exact counterPositive
  have selectedPositive := (InformationModel.informationMass_pos_iff
    (M) selected who site).mpr ⟨history, selectedReached⟩
  refine ⟨selectedPositive, ?_, ownOne⟩
  exact (M).bayesBelief_eq_of_eq_off profile selected who site
    (menu.decisionInformationAntichain initial horizon scheduler who site) off
    (menu.commonPlayerReachAt initial horizon scheduler profile who site)
    (menu.commonPlayerReachAt initial horizon scheduler selected who site) positive selectedPositive

end Interaction.ReactiveApplication.ResponseMenu
