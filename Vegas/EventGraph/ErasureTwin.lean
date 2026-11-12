module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.DecisionTwin

@[expose] public section

/-! # Profiles that are twins up to erasure

Two profiles are twins up to erasure when, at every configuration and ready
event, their event steps have the same law of erased successors: they act alike,
or both default the owner with the same output. Twins have the same law of the
erased final configuration from every configuration under every public
scheduler, so every readout that ignores the decisions of defaulted players has
the same law under both.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- Two profiles whose event steps have the same law of erased successors. -/
def ErasureTwins (left right : graph.BehavioralProfile) : Prop :=
  ∀ (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event),
    (eventStep left config event ready).map Config.erase =
      (eventStep right config event ready).map Config.erase

/-- **Twins have one erased run law.** -/
theorem ErasureTwins.runPlan_map_erase {left right : graph.BehavioralProfile}
    (twins : ErasureTwins left right) (scheduler : graph.PublicScheduler) :
    ∀ (fuel : Nat) (config : graph.Config),
      (graph.runPlan (graph.policyPlan left scheduler) fuel config).map Config.erase =
        (graph.runPlan (graph.policyPlan right scheduler) fuel config).map Config.erase := by
  intro fuel
  induction fuel with
  | zero => intro config; rfl
  | succ fuel ih =>
      intro config
      by_cases terminal : config.cut.Terminal
      · simp only [EventGraph.runPlan, dite_eq_left terminal]
      · rw [runPlan_policyPlan_succ left scheduler fuel config terminal,
          runPlan_policyPlan_succ right scheduler fuel config terminal, PMF.map_bind,
          PMF.map_bind]
        refine congrArg₂ PMF.bind rfl (funext fun selected => ?_)
        have ready : config.cut.Ready selected.1 := (EventOrder.Cut.mem_enabled _ _).mp selected.2
        change ((eventStep left config selected.1 ready).bind _).map Config.erase =
          ((eventStep right config selected.1 ready).bind _).map Config.erase
        rw [PMF.map_bind, PMF.map_bind]
        simp only [ih]
        exact bind_eq_of_map_key_eq Config.erase Set.univ _ _ (Set.subset_univ _)
          (Set.subset_univ _) (twins config selected.1 ready) _ fun first _ second _ same => by
            rw [graph.runPlan_map_erase right scheduler fuel first,
              graph.runPlan_map_erase right scheduler fuel second, same]

/-- Twins give every erasure-invariant readout one run law. -/
theorem ErasureTwins.runPlan_map_of_erase_invariant {left right : graph.BehavioralProfile}
    (twins : ErasureTwins left right) (scheduler : graph.PublicScheduler) {Outcome : Type*}
    (read : graph.Config → Outcome) (invariant : ∀ config, read config.erase = read config)
    (fuel : Nat) (config : graph.Config) :
    (graph.runPlan (graph.policyPlan left scheduler) fuel config).map read =
      (graph.runPlan (graph.policyPlan right scheduler) fuel config).map read := by
  have factored : read = read ∘ Config.erase := by
    funext current
    exact (invariant current).symm
  rw [factored, ← PMF.map_comp, ← PMF.map_comp, twins.runPlan_map_erase scheduler fuel config]

/-- Profiles with the same action laws everywhere except at events where both
act with point masses whose completions have one erasure are twins. -/
theorem erasureTwins_of_pointwise {left right : graph.BehavioralProfile}
    (pointwise : ∀ (config : graph.Config) (event : graph.EventId)
      (ready : config.cut.Ready event),
      actionLaw left config event = actionLaw right config event ∨
        ∃ first second, actionLaw left config event = PMF.pure first ∧
          actionLaw right config event = PMF.pure second ∧
          (config.step event ready first).map Config.erase =
            (config.step event ready second).map Config.erase) :
    ErasureTwins left right := by
  intro config event ready
  unfold eventStep
  rcases pointwise config event ready with same | ⟨first, second, leftPure, rightPure, steps⟩
  · rw [same]
  · rw [leftPure, rightPure, PMF.pure_bind, PMF.pure_bind]
    exact steps

end Vegas.EventGraph
