/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeLabelOrbits
import Interaction.ReactiveFiniteAssessment
import GameTheory.Protocol.DecisionPlan

/-! # Actual uniform-menu response kernels along private-label orbits -/

noncomputable section
namespace Vegas.Examples.LateOpeningRuntimeLabelKernels

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLabelTrace
open LateOpeningRuntimeLabelHistories LateOpeningRuntimeLabelOrbits

variable (horizon : Nat) (scheduler : app.Scheduler)

local notation "M" => rawMenu.information initial horizon scheduler

theorem menu_permutation (permutation : Equiv.Perm (Fin 3))
    (history : (rawMenu.protocol initial horizon scheduler).History) (who : Player) :
    (M).menu who ((M).infoOf who (permuteHistory horizon scheduler permutation history).trace) =
      (M).menu who ((M).infoOf who history.trace) := by
  change (M).menu who ((rawMenu.signals initial horizon scheduler).infoOf who
    (permuteHistory horizon scheduler permutation history).trace) =
    (M).menu who ((rawMenu.signals initial horizon scheduler).infoOf who history.trace)
  rw [rawMenu.info, rawMenu.info]
  rcases history with ⟨state, trace⟩
  cases state with
  | none => rfl
  | some control =>
      by_cases active : control.actor = some who
      · simp only [permuteHistory, permuteProtocolState, Option.map_some, permuteControl,
          ReactiveApplication.observe, active, ↓reduceIte,
          ReactiveApplication.ResponseMenu.information]
        change {choice | ∃ action ∈ rawMenu.actions who
          ((permuteExecution permutation control.execution).recall who)
          ((permuteExecution permutation control.execution).observe app who),
          choice = some action} = _
        have observed := observe_replace control.execution
          (permuteInputs permutation control.execution.application.config.inputs)
          (permuteInputs_bit permutation _) who
        change {choice | ∃ action ∈ rawMenu.actions who
          ((replaceExecution control.execution _).recall who)
          ((replaceExecution control.execution _).observe app who), choice = some action} = _
        rw [observed]
        exact congrArg (fun actions : Finset app.Action =>
          {choice | ∃ action ∈ actions, choice = some action})
          (rawMenu_replace who (control.execution.recall who)
            (control.execution.observe app who) _)
      · simp only [
          ReactiveApplication.observe, active, ↓reduceIte,
          ReactiveApplication.ResponseMenu.information, permuteHistory, permuteProtocolState,
          Option.map_some, permuteControl]


private theorem uniform_subtype_map_eq {α : Type} (first second : Set α)
    [Finite first] [Nonempty first] [Finite second] [Nonempty second]
    (same : first = second) :
    (by
      letI := Fintype.ofFinite first
      exact (PMF.uniformOfFintype first).map Subtype.val) =
    (by
      letI := Fintype.ofFinite second
      exact (PMF.uniformOfFintype second).map Subtype.val) := by
  subst second
  rfl

theorem uniformPolicy_raw_permutation (permutation : Equiv.Perm (Fin 3))
    (history : (rawMenu.protocol initial horizon scheduler).History) (who : Player) :
    ((rawMenu.uniformPolicy initial horizon scheduler who)
        ((M).infoOf who (permuteHistory horizon scheduler permutation history).trace)).map
        Subtype.val =
      ((rawMenu.uniformPolicy initial horizon scheduler who)
        ((M).infoOf who history.trace)).map Subtype.val := by
  exact uniform_subtype_map_eq _ _ (menu_permutation horizon scheduler permutation history who)


theorem behavioralJoint_raw_permutation (permutation : Equiv.Perm (Fin 3))
    (profile : ∀ who, (M).BehavioralPolicy who)
    (uniformAlice : (profile alice).AgreesAtDecisions
      (rawMenu.uniformPolicy initial horizon scheduler alice))
    (history : (rawMenu.protocol initial horizon scheduler).History)
    (nonterminal : ¬ (rawMenu.protocol initial horizon scheduler).terminal history.state) :
    ((M).behavioralJoint profile
        (permuteHistory horizon scheduler permutation history).trace (by
          change ¬ app.terminal (permuteProtocolState permutation history.state)
          rw [permuteProtocolState_terminal]
          exact nonterminal)).map Subtype.val =
      ((M).behavioralJoint profile history.trace nonterminal).map Subtype.val := by
  rw [InformationModel.behavioralJoint_map_val, InformationModel.behavioralJoint_map_val]
  apply congrArg GameTheory.Math.Probability.independentProduct
  funext who
  change Fin 2 at who
  fin_cases who
  · change ((profile alice) ((M).infoOf alice
      (permuteHistory horizon scheduler permutation history).trace)).map Subtype.val =
      ((profile alice) ((M).infoOf alice history.trace)).map Subtype.val
    rw [uniformAlice.at_history (permuteHistory horizon scheduler permutation history) (by
      change ¬ app.terminal (permuteProtocolState permutation history.state)
      rw [permuteProtocolState_terminal]
      exact nonterminal), uniformAlice.at_history history nonterminal]
    exact uniformPolicy_raw_permutation horizon scheduler permutation history alice
  · change ((profile bob) ((rawMenu.signals initial horizon scheduler).infoOf bob
      (permuteHistory horizon scheduler permutation history).trace)).map Subtype.val = _
    rw [permuteHistory_info_bob]
    rfl

end Vegas.Examples.LateOpeningRuntimeLabelKernels
