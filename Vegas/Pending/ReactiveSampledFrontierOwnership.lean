/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOriginalResponseStability
import Vegas.Pending.ReactiveSampledFrontierFreshness

/-! # Owner-authenticated sampled frontiers -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every original event retained by a supported prescribed posterior belongs
to that player's own actor. No cross-owner intention can enter its memory. -/
theorem prescribedReactivePosterior_owned (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ remembered, some remembered ∈ intentions → graph.actor? remembered.event = some who := by
  induction consistent generalizing intentions with
  | nil =>
      intro remembered member
      have same : intentions = [] := (PMF.mem_support_pure_iff _ _).mp supported
      simp [same] at member
  | @snoc history latest consistent positive ih =>
      obtain ⟨previous, prior, saved, memoryEq, produced⟩ :=
        runtime.prescribedReactivePosterior_snoc_support leaks who policy history latest
          positive intentions supported
      intro remembered member
      rw [memoryEq] at member
      rcases List.mem_append.mp member with earlier | current
      · exact ih previous prior remembered earlier
      · have equal : some remembered = saved := List.mem_singleton.mp current
        rw [← equal] at produced
        exact (runtime.prescribedReactiveResponse_some_ready leaks who policy history previous
          latest.beforeView latest.action remembered produced).2

/-- Genuine source memory cannot make a new owned sampled event completed in
another owner's pending frontier. The event's actor uniquely determines who
could have sampled it. -/
theorem sampled_event_not_in_other_memories (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ who, (runtime.prescribedReactivePolicy leaks who (profile who)).Consistent
      (execution.recall who))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation leaks who (profile who)).posterior
        (execution.recall who)).support)
    (who : Player) (event : graph.EventId) (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    ∀ owner remembered, some remembered ∈ memories owner → remembered.event ≠ event := by
  intro owner remembered member sameEvent
  have owns := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
    (consistent owner) (memories owner) (supported owner) remembered member
  rw [sameEvent, actor, Option.some.injEq] at owns
  subst owner
  apply fresh
  exact List.mem_filterMap.mpr ⟨some remembered, member, by simp [sameEvent]⟩

/-- A fresh physically ready event is ready at the sampled frontier: all its
predecessors are already physically complete, and genuine retained memories
cannot contain the newly sampled event under any owner. -/
theorem sampledFrontier_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (profile : graph.BehavioralProfile)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ who, (runtime.prescribedReactivePolicy leaks who (profile who)).Consistent
      (execution.recall who))
    (supported : ∀ who, memories who ∈
      ((runtime.prescribedReactiveImplementation leaks who (profile who)).posterior
        (execution.recall who)).support)
    (frontier : graph.Config)
    (domain : ∀ event, event ∈ frontier.cut.completed ↔
      event ∈ execution.application.config.cut.completed ∨
        ∃ owner remembered, some remembered ∈ memories owner ∧ remembered.event = event)
    (who : Player) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event)) :
    frontier.cut.Ready event := by
  have absent := runtime.sampled_event_not_in_other_memories leaks profile execution
    memories consistent supported who event actor fresh
  constructor
  · intro completed
    rcases (domain event).mp completed with physically | ⟨owner, remembered, member, named⟩
    · exact ready.1 physically
    · exact absent owner remembered member named
  · intro predecessor dependency
    exact (domain predecessor).mpr (Or.inl (ready.2 dependency))

end Vegas.EventGraphRuntime
