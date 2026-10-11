/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralEnvironment

/-! # Actual chance-command support in a unilateral execution -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every genuine chance command either stutters or shares its actual draw
with a reachable mixed source frontier, retaining the arbitrary focal policy. -/
theorem ReactiveUnilateralFrontier.sample_command_frontier_exists
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (consistent : ∀ owner, owner ≠ focal → (runtime.prescribedReactivePolicy
      leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supportedMemory : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (event : graph.EventId) (next : (runtime.reactiveApplication leaks).Execution)
    (reached : next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.executeSample event))).support) :
    ∃ nextFrontier, runtime.ReactiveUnilateralFrontier leaks focal next memories nextFrontier := by
  have stutter (law : environmentStep runtime execution.application (.executeSample event) =
      PMF.pure execution.application) :
      runtime.ReactiveUnilateralFrontier leaks focal next memories frontier := by
    simp only [ReactiveApplication.Execution.environmentStep, reactiveApplication, law,
      PMF.pure_map, PMF.mem_support_pure_iff] at reached
    subst next
    exact related.congr_execution runtime leaks _ _ focal memories frontier rfl rfl rfl
  by_cases ready : execution.application.config.cut.Ready event
  · cases node : nodeView graph event with
    | sample payload law outputEq codeEq =>
        obtain ⟨_, joint, physicalMarginal, _, preserves⟩ :=
          related.sample_coupling runtime leaks execution focal memories frontier profile consistent
            supportedMemory event ready payload law outputEq codeEq node
        rw [← physicalMarginal, PMF.support_map, Set.mem_image] at reached
        obtain ⟨pair, member, equal⟩ := reached
        exact ⟨pair.2, equal ▸ preserves pair member⟩
    | bind owner payload outputEq codeEq =>
        refine ⟨frontier, stutter ?_⟩
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
    | resolve owner payload binding checks outputEq codeEq =>
        refine ⟨frontier, stutter ?_⟩
        exact environmentStep_executeSample_of_nonsample runtime execution.application event ready
          (by
            intro payload law outputEq codeEq impossible
            rw [node] at impossible
            cases impossible)
  · exact ⟨frontier, stutter (environmentStep_executeSample_of_not_ready runtime
      execution.application event ready)⟩

end Vegas.EventGraphRuntime
