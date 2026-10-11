/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveUnilateralSampling

/-! # Actual unilateral callback posterior reconstruction -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every actual focal callback or supported foreign prescribed response
reconstructs a reachable mixed source frontier for every compatible posterior
memory, without conditioning the focal policy or assuming a source law. -/
theorem respond_policy_unilateral_frontier_exists (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution) (focal : Player)
    (consistent : ∀ owner, owner ≠ focal → (runtime.prescribedReactivePolicy
      leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option graph.Completion),
      memories focal = [] →
      (∀ owner, owner ≠ focal → memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveUnilateralFrontier leaks focal execution memories frontier)
    (who : Player)
    (quiet : ∀ entry ∈ execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (action : (runtime.reactiveApplication leaks).Action)
    (chosen : who ≠ focal → action ∈ (runtime.prescribedReactivePolicy leaks who (profile who)
      (execution.recall who) (execution.observe (runtime.reactiveApplication leaks) who)).support)
    (afterMemories : Player → List (Option graph.Completion))
    (empty : afterMemories focal = [])
    (supported : ∀ owner, owner ≠ focal → afterMemories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        ((execution.respond (runtime.reactiveApplication leaks) who action).recall owner)).support)
    :
    ∃ frontier, runtime.ReactiveUnilateralFrontier leaks focal
      (execution.respond (runtime.reactiveApplication leaks) who action)
        afterMemories frontier := by
  by_cases different : who = focal
  · subst who
    have prior : ∀ owner, owner ≠ focal → afterMemories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support := by
      intro owner foreign
      simpa only [(runtime.reactiveApplication leaks).respond_recall_other
        execution focal owner foreign action] using supported owner foreign
    obtain ⟨frontier, related⟩ := frontiers afterMemories empty prior
    exact ⟨frontier, related.respond_focal runtime leaks focal execution afterMemories
      frontier action⟩
  let implementation := runtime.prescribedReactiveImplementation leaks who (profile who)
  have posterior := supported who different
  rw [implementation.posterior_respond execution who action, PMF.support_map,
    Set.mem_image] at posterior
  obtain ⟨response, conditioned, memoryEq⟩ := posterior
  have positive : action ∈ (((implementation.posterior (execution.recall who)).bind fun memory =>
      implementation.respond memory
        (execution.recall who, execution.observe (runtime.reactiveApplication leaks) who)).map
          Prod.fst).support := chosen different
  have genuine := mem_support_fiberPosterior positive conditioned
  obtain ⟨memory, memorySupported, produced⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ genuine.2)
  have pairEq : response = (action, afterMemories who) := Prod.ext genuine.1 memoryEq
  rw [pairEq] at produced
  change (action, afterMemories who) ∈
    ((runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who) memory
      (execution.observe (runtime.reactiveApplication leaks) who)).map
        (fun response => (response.1, memory ++ [response.2]))).support at produced
  obtain ⟨⟨actual, saved⟩, produced, pairEq⟩ := PMF.support_map .. ▸ produced
  have actionEq : actual = action := congrArg Prod.fst pairEq
  have appended : memory ++ [saved] = afterMemories who := congrArg Prod.snd pairEq
  subst actual
  let memories := Function.update afterMemories who memory
  have prior : ∀ owner, owner ≠ focal → memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support := by
    intro owner foreign
    by_cases equal : owner = who
    · subst owner
      simpa only [memories, Function.update_self, implementation] using memorySupported
    · simpa only [memories, Function.update_of_ne equal,
        (runtime.reactiveApplication leaks).respond_recall_other execution who owner equal action]
        using supported owner foreign
  obtain ⟨frontier, related⟩ := frontiers memories
    (by simpa only [memories, Function.update_of_ne (Ne.symm different)] using empty) prior
  have produces : (action, saved) ∈
      (runtime.prescribedReactiveResponse leaks who (profile who) (execution.recall who)
        (memories who) (execution.observe (runtime.reactiveApplication leaks) who)).support := by
    simpa only [memories, Function.update_self] using produced
  have restored : Function.update memories who (memories who ++ [saved]) = afterMemories := by
    funext owner
    by_cases equal : owner = who
    · subst owner
      simpa only [memories, Function.update_self] using appended
    · simp only [Function.update_of_ne equal, memories]
  have aligned := (runtime.prescribedReactivePosterior_length leaks who (profile who)
    (consistent who different) (memories who) (prior who different)).symm
  cases saved with
  | none =>
      refine ⟨frontier, ?_⟩
      rw [← restored]
      exact related.respond_foreign_none runtime leaks execution focal memories frontier who
        different (profile who)
        aligned action produces
  | some remembered =>
      obtain ⟨_, next, _, nextRelated⟩ := related.respond_foreign_some runtime
        leaks execution focal memories
        frontier profile consistent prior who different quiet sent aligned action remembered
        produces
      exact ⟨next, restored ▸ nextRelated⟩


end Vegas.EventGraphRuntime
