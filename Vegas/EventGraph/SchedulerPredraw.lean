/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.SchedulerProtocol

/-! # Setup-wide finite predrawing of public schedulers

The finite table is drawn before the private initial environment. All player
policies and node chance kernels remain unchanged and randomized. No finite
carrier of payloads, stores, or information states is assumed.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

private theorem scheduler_runBehavioral_setup (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler) (fuel : Nat) :
    ((schedulerInformation profile inputs).runBehavioral
      (fun _ => schedulerBehavioral profile inputs scheduler) (fuel + 1)).map
        ExecutionProtocol.History.state =
      (inputs.bind fun initial =>
        graph.runPlan (graph.policyPlan profile scheduler) fuel (Config.initial initial)).map
          some := by
  simpa only [InformationModel.runBehavioral, schedulerRun,
    ExecutionProtocol.initHistory_state, FinDist.map_bind] using
      scheduler_runBehavioralFrom profile inputs scheduler (fuel + 1)
        (schedulerProtocol profile inputs).initHistory

/-- Every adaptive public scheduler has a finite mixture of deterministic
public schedulers with the same complete execution law for the fixed profile.
One mixture serves the entire private input law. -/
theorem exists_scheduler_mixture (profile : graph.BehavioralProfile)
    (inputs : FinDist graph.Inputs) (scheduler : graph.PublicScheduler) :
    ∃ mixture : FinDist graph.DeterministicPublicScheduler,
      (mixture.bind fun fixed => inputs.bind fun initial =>
        graph.runPolicies fixed.toPublic profile initial) =
      inputs.bind (graph.runPolicies scheduler profile) := by
  let M := schedulerInformation profile inputs
  let E := schedulerProtocol profile inputs
  let horizon := graph.order.eventCount + 1
  let policies := fun (_ : Unit) => schedulerBehavioral profile inputs scheduler
  obtain ⟨mixed, law⟩ := M.exists_mixed_runMixed_eq_runBehavioral
    (scheduler_actsOnce profile inputs) policies horizon
  let extract := fun pureProfile : (i : Unit) → M.Policy i =>
    schedulerOfPolicy profile inputs (pureProfile ())
  refine ⟨(FinDist.pi mixed).map extract, ?_⟩
  apply FinDist.map_injective (f := some) (Option.some_injective _)
  rw [FinDist.bind_map, FinDist.map_bind]
  calc
    _ = (M.runMixed mixed horizon).map ExecutionProtocol.History.state := by
      rw [InformationModel.runMixed, InformationModel.runMixedFrom, FinDist.map_bind]
      apply FinDist.bind_congr
      intro pureProfile _
      have pureLaw := scheduler_runBehavioral_setup profile inputs
        (extract pureProfile).toPublic graph.order.eventCount
      have policiesEq : (fun i => (pureProfile i).toBehavioral) =
          (fun (_ : Unit) => schedulerBehavioral profile inputs
            (extract pureProfile).toPublic) := by
        funext i
        cases i
        exact (schedulerBehavioral_schedulerOfPolicy profile inputs (pureProfile ())).symm
      rw [← InformationModel.runBehavioralFrom_toBehavioral]
      rw [policiesEq]
      exact pureLaw.symm
    _ = (M.runBehavioral policies horizon).map ExecutionProtocol.History.state := by rw [law]
    _ = _ := scheduler_runBehavioral_setup profile inputs scheduler graph.order.eventCount

end Vegas.EventGraph
