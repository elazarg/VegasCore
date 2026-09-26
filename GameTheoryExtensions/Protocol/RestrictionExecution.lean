/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.ActionRestriction
import GameTheory.Analysis.Protocol.CounterfactualDecomposition

/-! # Execution laws derived from a structural action restriction

The pure one-step square determines every compliant behavioral continuation
law. Neither the target's behavior at new information sites nor any equilibrium
condition is needed for this correspondence.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] {E T : ExecutionProtocol Player}
  {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)

theorem joint_law (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile source target)
    (original : E.History) (running : ¬ E.terminal original.state) :
    (FinDist.pi fun who => target who (N.infoOf who (restriction.history original).trace)) =
      (FinDist.pi fun who => source who (M.infoOf who original.trace)).map
        (fun draws who => restriction.choiceAt who original (draws who)) := by
  have localLaws := funext (restriction.extends_at_history source target agrees original running)
  rw [localLaws]
  exact (FinDist.pi_map (fun who => restriction.choiceAt who original)
    (fun who => source who (M.infoOf who original.trace)))

/-- Complete behavioral laws follow from the local structural square. -/
theorem runFrom_law (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile source target) (fuel : Nat) (original : E.History) :
    (M.runBehavioralFrom source fuel original).map restriction.history =
      N.runBehavioralFrom target fuel (restriction.history original) := by
  induction fuel generalizing original with
  | zero => exact FinDist.map_pure _ _
  | succ fuel induction =>
      by_cases stopped : E.terminal original.state
      · rw [M.runBehavioralFrom_of_terminal source _ stopped,
          N.runBehavioralFrom_of_terminal target _ ((restriction.terminal original).mpr stopped),
          FinDist.map_pure]
      · rw [M.runBehavioralFrom_succ_localStep, N.runBehavioralFrom_succ_localStep,
          restriction.joint_law source target agrees original stopped,
          FinDist.map_bind, FinDist.bind_bind, FinDist.bind_map, FinDist.bind_bind]
        apply FinDist.bind_congr
        intro draws _
        have one := restriction.step original draws
        change (M.localStep original draws).map restriction.history =
          N.localStep (restriction.history original)
            (fun who => restriction.choiceAt who original (draws who)) at one
        rw [← one, FinDist.bind_map]
        exact FinDist.bind_congr fun next _ => induction next

theorem initialized_law (source : ∀ who, M.BehavioralPolicy who)
    (target : ∀ who, N.BehavioralPolicy who)
    (agrees : restriction.ExtendsProfile source target) (fuel : Nat) :
    (M.runBehavioral source fuel).map restriction.history = N.runBehavioral target fuel := by
  simpa only [runBehavioral, restriction.initial] using
    restriction.runFrom_law source target agrees fuel E.initHistory

/-- A retained belief fiber embeds into the full target fiber, which may also
contain histories requiring a forbidden action. -/
def informationHistory (who : Player) (site : M.InformationSite who) :
    M.InformationHistory who site.1 ↪ N.InformationHistory who (restriction.site who site).1 where
  toFun original := ⟨restriction.history original.1,
    (restriction.observed who original.1).trans
      (congrArg (restriction.information who) original.2)⟩
  inj' := by
    intro first second same
    exact Subtype.ext (restriction.history.injective (congrArg Subtype.val same))

omit [Fintype Player] in
theorem source_commonDepth (who : Player) (site : M.InformationSite who) (depth : Nat)
    (clock : InformationSite.CommonDepth N (restriction.site who site) depth) :
    InformationSite.CommonDepth M site depth := by
  intro original
  have target := clock (restriction.informationHistory who site original)
  exact (restriction.length original.1).symm.trans target

omit [Fintype Player] in
@[simp] theorem informationHistory_val (who : Player) (site : M.InformationSite who)
    (original : M.InformationHistory who site.1) :
    (restriction.informationHistory who site original).1 = restriction.history original.1 := rfl

omit [Fintype Player] in
theorem informationHistory_map_val (who : Player) (site : M.InformationSite who)
    (belief : FinDist (M.InformationHistory who site.1)) :
    (belief.map (restriction.informationHistory who site)).map Subtype.val =
      (belief.map Subtype.val).map restriction.history := by
  rw [FinDist.map_comp, FinDist.map_comp]
  rfl

end GameTheory.Protocol.InformationModel.ActionRestriction
