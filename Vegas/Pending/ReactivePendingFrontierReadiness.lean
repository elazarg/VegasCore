/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSampledFrontierOwnership
import Vegas.Pending.ReactiveEventStability
import Vegas.EventGraph.BarrierInformation

/-! # Physical readiness of retained private intentions -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Retained original intentions have an actual ready sampling entry. -/
theorem prescribedReactivePosterior_ready_entry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)) (who : Player)
    (policy : graph.BehavioralPolicy who)
    {history : List (runtime.reactiveApplication leaks).PlayerEntry}
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent history)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior history).support) :
    ∀ remembered, some remembered ∈ intentions →
      ∃ entry ∈ history, entry.beforeView.application.publicView.EventReady remembered.event := by
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
      · obtain ⟨entry, retained, ready⟩ := ih previous prior remembered earlier
        exact ⟨entry, List.mem_append_left _ retained, ready⟩
      · have equal : some remembered = saved := List.mem_singleton.mp current
        rw [← equal] at produced
        exact ⟨latest, List.mem_append_right _ (by simp),
          (runtime.prescribedReactiveResponse_some_ready leaks who policy history previous
            latest.beforeView latest.action remembered produced).1⟩

/-- Unsettled sampled intentions are still physically ready, using genuine
entry-event persistence rather than a frontier readiness hypothesis. -/
theorem prescribedReactivePosterior_pending_ready (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (who : Player) (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (execution.recall who))
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).support)
    (remembered : graph.Completion) (retained : some remembered ∈ intentions)
    (unfinished : remembered.event ∉ execution.application.config.cut.completed) :
    execution.application.config.cut.Ready remembered.event := by
  obtain ⟨entry, member, ready⟩ := runtime.prescribedReactivePosterior_ready_entry leaks
    who policy consistent intentions supported remembered retained
  obtain ⟨extra, order, _⟩ := stable who entry member remembered.event ready unfinished
  exact ready_of_eventReady_extends order ready unfinished

/-- At an actual initialized protocol prefix, unfinished genuine intentions
remain physically ready. Entry persistence is derived from the raw trace. -/
theorem prescribedReactivePosterior_pending_ready_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (control.execution.recall who))
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (control.execution.recall who)).support)
    (remembered : graph.Completion) (retained : some remembered ∈ intentions)
    (unfinished : remembered.event ∉ control.execution.application.config.cut.completed) :
    control.execution.application.config.cut.Ready remembered.event := by
  exact runtime.prescribedReactivePosterior_pending_ready leaks control.execution
    (runtime.entryEventStable_history leaks (inputs.map State.initial) horizon scheduler trace)
    who policy consistent intentions supported remembered retained unfinished

/-- A fresh ready event has only foreign pending intentions under compilation
barriers: the owner's unique simultaneous event cannot be a prior intention. -/
theorem pending_intention_foreign_of_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (profile : graph.BehavioralProfile)
    (memories : Player → List (Option graph.Completion))
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support)
    (who : Player) (event : graph.EventId)
    (ready : execution.application.config.cut.Ready event)
    (actor : graph.actor? event = some who)
    (fresh : event ∉ (memories who).filterMap (fun saved => saved.map Completion.event))
    (owner : Player) (remembered : graph.Completion)
    (retained : some remembered ∈ memories owner)
    (unfinished : remembered.event ∉ execution.application.config.cut.completed) : owner ≠ who := by
  intro equal
  subst owner
  have pendingReady := runtime.prescribedReactivePosterior_pending_ready leaks execution stable
    who (profile who) (consistent who) (memories who) (supported who) remembered retained unfinished
  have pendingActor := runtime.prescribedReactivePosterior_owned leaks who (profile who)
    (consistent who) (memories who) (supported who) remembered retained
  have same := ordered.ready_actor_unique execution.application.config.cut ready pendingReady
    actor pendingActor
  apply fresh
  exact List.mem_filterMap.mpr ⟨some remembered, retained, by simp [same]⟩

end Vegas.EventGraphRuntime
