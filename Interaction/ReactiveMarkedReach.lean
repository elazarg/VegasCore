/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveRecallReplay
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # Counterfactual factors of actual reactive path coefficients -/

noncomputable section

namespace Interaction.ReactiveApplication.ResponseMenu

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] [Fintype Principal]
  {app : ReactiveApplication Principal} (menu : app.ResponseMenu)
  (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)

local notation "N" => menu.information initial horizon scheduler
local notation "E" => menu.protocol initial horizon scheduler

/-- A transition coefficient common to all profiles determines the REAL
counterfactual reach exactly. Replaying the selected owner's actual legal
recall gives unit own reach, so no observed response probability is divided
out and zero-probability response atoms remain admissible. -/
theorem counterfactual_of_history_factor
    (control : app.Control) (trace : (E).Trace (some control)) (chance : ℝ)
    (factor : ∀ profile : ∀ who, (N).BehavioralPolicy who,
      ((N).historyReachWeight profile ⟨some control, trace⟩).toReal =
        chance * ∏ who, (N).ownPlayReachProbability (profile who) ((N).ownPlay who trace))
    (profile : ∀ who, (N).BehavioralPolicy who) (who : Principal) :
    (N).counterfactualReachProbability profile who trace =
      chance * ∏ other ∈ Finset.univ.erase who,
        (N).ownPlayReachProbability (profile other) ((N).ownPlay other trace) := by
  classical
  have ownEq (observer : Principal) : (N).ownPlay observer trace =
      app.recallOwnPlay (control.execution.recall observer) := by
    change (menu.signals initial horizon scheduler).ownPlay observer trace = _
    rw [← menu.ownPlay_toRawTrace initial horizon scheduler observer trace, app.trace_ownPlay]
    rfl
  have legal (index : Fin (control.execution.recall who).length) :
      (control.execution.recall who)[index].action ∈ menu.actions who
        ((control.execution.recall who).take index)
          (control.execution.recall who)[index].beforeView := by
    have present := app.recallOwnPlay_entry_mem (control.execution.recall who) index.val index.isLt
    rw [← ownEq who] at present
    have permitted := (N).ownPlay_mem_menu who trace present
    change ∃ response ∈ menu.actions who _ _, some _ = some response at permitted
    obtain ⟨response, permitted, same⟩ := permitted
    cases Option.some.inj same
    exact permitted
  let selected := Function.update profile who
    (menu.recallReplayPolicy initial horizon scheduler who (control.execution.recall who)
      (profile who))
  have unit : (N).ownPlayReachProbability (selected who) ((N).ownPlay who trace) = 1 := by
    rw [ownEq who]
    simp only [selected, Function.update_self]
    exact menu.recallReplayPolicy_ownReach initial horizon scheduler who
      (control.execution.recall who) (profile who) legal _ (List.prefix_refl _)
  have off : ∀ other, other ≠ who → profile other = selected other := by
    intro other different
    exact (Function.update_of_ne different _ _).symm
  have reached : ((N).historyReachWeight selected ⟨some control, trace⟩).toReal =
      (N).counterfactualReachProbability profile who trace := by
    rw [(N).historyReachProbability_eq_player_mul_counterfactual,
      InformationModel.playerReachProbability_eq_ownPlayReachProbability, unit, one_mul,
      ← (N).counterfactualReachProbability_eq_of_eq_off off trace]
  have product : (∏ observer, (N).ownPlayReachProbability (selected observer)
      ((N).ownPlay observer trace)) =
      ∏ observer ∈ Finset.univ.erase who,
        (N).ownPlayReachProbability (profile observer) ((N).ownPlay observer trace) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun observer => (N).ownPlayReachProbability (selected observer)
        ((N).ownPlay observer trace)) (Finset.mem_univ who), unit, one_mul]
    exact Finset.prod_congr rfl fun observer member =>
      congrArg (fun policy => (N).ownPlayReachProbability policy ((N).ownPlay observer trace))
        ((off observer (Finset.mem_erase.mp member).1).symm)
  exact reached.symm.trans ((factor selected).trans (congrArg (chance * ·) product))

end Interaction.ReactiveApplication.ResponseMenu
