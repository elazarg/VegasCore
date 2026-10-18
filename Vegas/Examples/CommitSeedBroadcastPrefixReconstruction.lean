/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastSurgeryLikelihood
import GameTheory.Protocol.BehavioralBayes

/-! # A repaired prefix and its original seed determine its native preimage -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability
open scoped ENNReal

/-- The recorded native actions are replayed by their own response index.
Beyond that word the literal response is silence. -/
def replayRecordedResponses (reference : List app.PlayerEntry) : app.Policy :=
  fun past _ => PMF.pure (((reference[past.length]?).map
    ReactiveApplication.PlayerEntry.action).getD ⟨none⟩)

private theorem replay_record_atom (reference past : List app.PlayerEntry)
    (entry : app.PlayerEntry) (next : reference[past.length]? = some entry) :
    ((app.encodePolicy (replayRecordedResponses reference) (some (past, entry.beforeView))).map
      Subtype.val) (some entry.action) = 1 := by
  simp only [ReactiveApplication.encodePolicy, replayRecordedResponses, next,
    Option.map_some, Option.getD_some, PMF.pure_map, PMF.pure_apply_self]

private theorem replay_recorded_ownReach (owner : Player)
    (reference past : List app.PlayerEntry) (within : past <+: reference) :
    (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
      (app.encodePolicy (replayRecordedResponses reference)) (app.recallOwnPlay past) = 1 := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      have earlier : past <+: reference := (List.prefix_append _ _).trans within
      obtain ⟨rest, same⟩ := within
      have next : reference[past.length]? = some entry := by
        rw [← same]
        simp only [List.append_assoc, List.singleton_append,
          List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem?_cons_zero]
      rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability]
      change (((app.encodePolicy (replayRecordedResponses reference)
          (some (past, entry.beforeView))).map Subtype.val) (some entry.action)).toReal *
        (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
          (app.encodePolicy (replayRecordedResponses reference)) (app.recallOwnPlay past) = 1
      have atom := congrArg ENNReal.toReal (replay_record_atom reference past entry next)
      exact (congrArg₂ (fun left right : ℝ => left * right) atom (ih earlier)).trans
        (by norm_num)

private theorem replay_extra_silent_ownReach (owner : Player)
    (reference : List app.PlayerEntry) (entry : app.PlayerEntry)
    (silent : entry.action = (⟨none⟩ : app.Action)) :
    (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
      (app.encodePolicy (replayRecordedResponses reference))
      (app.recallOwnPlay (reference ++ [entry])) = 1 := by
  have beyond : reference[reference.length]? = none := List.getElem?_eq_none_iff.mpr le_rfl
  have atom : ((app.encodePolicy (replayRecordedResponses reference)
      (some (reference, entry.beforeView))).map Subtype.val) (some entry.action) = 1 := by
    simp only [ReactiveApplication.encodePolicy, replayRecordedResponses, beyond,
      Option.map_none, Option.getD_none, silent, PMF.pure_map, PMF.pure_apply_self]
  rw [app.recallOwnPlay_append, InformationModel.ownPlayReachProbability]
  change (((app.encodePolicy (replayRecordedResponses reference)
      (some (reference, entry.beforeView))).map Subtype.val) (some entry.action)).toReal *
    (app.information initial horizon scheduler).ownPlayReachProbability (who := owner)
      (app.encodePolicy (replayRecordedResponses reference)) (app.recallOwnPlay reference) = 1
  exact (congrArg₂ (fun left right : ℝ => left * right) (congrArg ENNReal.toReal atom)
    (replay_recorded_ownReach owner reference reference (List.prefix_refl _))).trans
      (by norm_num)

/-- The old seed contributes unit transition mass, and every retained action
or removed silent action is selected with probability one by the same replay. -/
theorem family_replayed_history_unit (seed : Seeds) (target : app.Execution)
    (source : app.Control)
    (trace : (app.protocol initial horizon (family seed)).Trace (some source))
    (words : ∀ owner, source.execution.recall owner = target.recall owner ∨
      ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
        source.execution.recall owner = target.recall owner ++ [entry]) :
    ((app.information initial horizon (family seed)).historyReachWeight
      (fun owner => app.encodePolicy (replayRecordedResponses (target.recall owner)))
      ⟨some source, trace⟩).toReal = 1 := by
  rw [family_history_response_factor]
  unfold nativeResponseLikelihood
  apply Finset.prod_eq_one
  intro owner _member
  rcases words owner with same | ⟨entry, silent, same⟩
  · rw [same]
    exact replay_recorded_ownReach owner _ _ (List.prefix_refl _)
  · rw [same]
    exact replay_extra_silent_ownReach owner _ entry silent

private theorem unit_information_histories_eq (seed : Seeds) (owner : Player)
    (site : (app.information initial horizon (family seed)).InformationSite owner)
    (profile : ∀ who, (app.information initial horizon (family seed)).BehavioralPolicy who)
    (first second : (app.information initial horizon (family seed)).InformationHistory
      owner site.1)
    (firstUnit : ((app.information initial horizon (family seed)).historyReachWeight
      profile first.1).toReal = 1)
    (secondUnit : ((app.information initial horizon (family seed)).historyReachWeight
      profile second.1).toReal = 1) : first = second := by
  classical
  by_contra different
  let model := app.information initial horizon (family seed)
  have firstMass : model.historyReachWeight profile first.1 = 1 := by
    exact (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm.trans
      ((congrArg ENNReal.ofReal firstUnit).trans ENNReal.ofReal_one)
  have secondMass : model.historyReachWeight profile second.1 = 1 := by
    exact (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm.trans
      ((congrArg ENNReal.ofReal secondUnit).trans ENNReal.ofReal_one)
  have pair := ENNReal.sum_le_tsum (f := fun history : model.InformationHistory owner site.1 =>
    model.historyReachWeight profile history.1) ({first, second} : Finset _)
  have upper := model.informationMass_le_one profile owner site
    (app.decisionInformationAntichain initial horizon (family seed) owner site)
  have impossible : (2 : ℝ≥0∞) ≤ 1 := by
    have lower : (2 : ℝ≥0∞) ≤ model.informationMass profile owner site := by
      have evaluated : (∑ history ∈ ({first, second} : Finset
          (model.InformationHistory owner site.1)), model.historyReachWeight profile history.1) =
          model.historyReachWeight profile first.1 + model.historyReachWeight profile second.1 :=
        Finset.sum_pair different
      calc
        _ = model.historyReachWeight profile first.1 +
            model.historyReachWeight profile second.1 := by rw [firstMass, secondMass]; norm_num
        _ = _ := evaluated.symm
        _ ≤ _ := pair
    exact lower.trans upper
  norm_num at impossible

/-- Two same-input source prefixes of a fixed original seed cannot map to the
same retained response word. No fresh prior or average seed-tagged bound is used. -/
theorem family_replay_preimage_unique (seed : Seeds) (owner : Player)
    (target first second : app.Execution) (firstRemaining secondRemaining : Nat)
    (firstTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨firstRemaining, some owner, first⟩))
    (secondTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨secondRemaining, some owner, second⟩))
    (sameInput : (first.recall owner, first.observe app owner) =
      (second.recall owner, second.observe app owner))
    (firstWords : ∀ who, first.recall who = target.recall who ∨
      ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
        first.recall who = target.recall who ++ [entry])
    (secondWords : ∀ who, second.recall who = target.recall who ∨
      ∃ entry : app.PlayerEntry, entry.action = (⟨none⟩ : app.Action) ∧
        second.recall who = target.recall who ++ [entry]) :
    (⟨some ⟨firstRemaining, some owner, first⟩, firstTrace⟩ :
      (app.protocol initial horizon (family seed)).History) =
        ⟨some ⟨secondRemaining, some owner, second⟩, secondTrace⟩ := by
  let model := app.information initial horizon (family seed)
  let firstHistory : (app.protocol initial horizon (family seed)).History :=
    ⟨some ⟨firstRemaining, some owner, first⟩, firstTrace⟩
  let secondHistory : (app.protocol initial horizon (family seed)).History :=
    ⟨some ⟨secondRemaining, some owner, second⟩, secondTrace⟩
  have available : some (⟨none⟩ : app.Action) ∈
      model.menu owner (model.infoOf owner firstTrace) := by
    change true = ((app.signals initial horizon (family seed)).infoOf owner firstTrace).isSome
    rw [app.info]
    simp only [ReactiveApplication.observe, ite_true, Option.isSome_some]
  let site := model.informationSite owner firstHistory ⟨none⟩
    (by
      intro stopped
      have impossible : (some owner : Option Player) = none := stopped.2
      cases impossible) available
  let firstAt : model.InformationHistory owner site.1 := ⟨firstHistory, rfl⟩
  let secondAt : model.InformationHistory owner site.1 := ⟨secondHistory, by
    change (app.signals initial horizon (family seed)).infoOf owner secondTrace =
      (app.signals initial horizon (family seed)).infoOf owner firstTrace
    rw [app.info, app.info]
    simp only [ReactiveApplication.observe, ite_true]
    exact congrArg some sameInput.symm⟩
  have equal := unit_information_histories_eq seed owner site
    (fun who => app.encodePolicy (replayRecordedResponses (target.recall who))) firstAt secondAt
    (family_replayed_history_unit seed target _ firstTrace firstWords)
    (family_replayed_history_unit seed target _ secondTrace secondWords)
  exact congrArg Subtype.val equal

end Vegas.Examples.CommitSeedBroadcast
