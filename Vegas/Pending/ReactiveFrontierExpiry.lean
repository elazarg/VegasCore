/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResolutionRecall
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveFrontierRecall
import Vegas.Pending.ReactivePosteriorUniqueness
import Vegas.EventGraph.ConfigRestriction
import Interaction.ReactiveRecallInvariant

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual due expiry appends the original authenticated silent intention to
reconstructed source history, preserving every earlier original completion. -/
theorem originalConfig_silent_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution after : (runtime.reactiveApplication leaks).Execution)
    (memories : Player → List (Option graph.Completion)) (owner : Player)
    (event : graph.EventId) (ready : execution.application.config.cut.Ready event)
    (entered : Nat) (activated : execution.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ execution.application.clock - entered)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ (execution.recall owner).zip (memories owner))
    (matching : runtime.ReactiveSilentDecision leaks owner entry remembered)
    (named : remembered.event = event)
    (distinct : ((memories owner).filterMap (fun saved => saved.map Completion.event)).Nodup)
    (supported : after ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire event))).support) :
    runtime.originalConfig leaks after memories =
      (runtime.originalConfig leaks execution memories).complete event ready
        (cast (congrArg graph.Action named) remembered.action)
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  let app := runtime.reactiveApplication leaks
  unfold ReactiveApplication.Execution.environmentStep at supported
  obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ moved
  change state ∈ (runtime.environmentStep execution.application (.expire event)).support at changed
  rw [environmentStep_expire_resolve_eq runtime execution.application event ready entered
    activated due owner payload binding checks outputEq codeEq node] at changed
  cases (PMF.mem_support_pure_iff _ _).mp changed
  have actor : graph.actor? event = some owner := by
    change (graph.nodes event).actor = some owner
    rw [← EventCode.actor_cast outputEq, codeEq]
    rfl
  have restored := runtime.reactiveOriginal_silent_of_unique_memory leaks owner
    (execution.recall owner) (memories owner) execution.receipts entry remembered
      ⟨event, cast (congrArg EventField.Action outputEq.symm) false⟩ retained matching named
      (by
        intro other member saved equal sameEvent
        subst other
        exact completion_eq_of_intention_events_nodup (memories owner) distinct saved remembered
          member (List.of_mem_zip retained).2 (sameEvent.trans named.symm)) (by simp only [node])
  apply Config.eq_of_fields
  · rfl
  · rfl
  · rfl
  · simp only [originalConfig, State.complete, Config.complete, List.map_append,
      List.map_cons, List.map_nil]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro completion member
      rfl
    · apply congrArg List.singleton
      unfold originalCompletion
      rw [actor]
      change runtime.reactiveOriginal leaks owner (execution.recall owner) (memories owner)
        execution.receipts ⟨event, cast (congrArg EventField.Action outputEq.symm) false⟩ = _
      rw [restored]
      cases named
      rfl

/-- Actual due expiry of a genuinely recorded silent resolution consumes its
 original intention and preserves the full reachable sampled frontier. -/
theorem ReactiveFrontier.expire_silent_resolution (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (ordered : graph.BarrierOrdered)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol initial horizon scheduler).Trace
      (some control))
    (valid : control.execution.application.BindingInvariant)
    (memories : Player → List (Option graph.Completion)) (frontier : graph.Config)
    (related : runtime.ReactiveFrontier leaks control.execution memories frontier)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (control.execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (control.execution.recall owner)).support)
    (who : Player)
    (quiet : ∀ entry ∈ control.execution.recall who,
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ entry ∈ control.execution.recall who, ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (entry : (runtime.reactiveApplication leaks).PlayerEntry) (remembered : graph.Completion)
    (retained : (entry, some remembered) ∈ (control.execution.recall who).zip (memories who))
    (matching : runtime.ReactiveSilentDecision leaks who entry remembered)
    (ready : control.execution.application.config.cut.Ready remembered.event)
    (entered : Nat)
    (activated : control.execution.application.activatedAt remembered.event = some entered)
    (due : runtime.deadline remembered.event ≤ control.execution.application.clock - entered)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding who payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout remembered.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes remembered.event) = .resolve who payload binding checks)
    (node : nodeView graph remembered.event = .resolve who payload binding checks outputEq codeEq)
    (after : (runtime.reactiveApplication leaks).Execution)
    (moved : after ∈ (control.execution.environmentStep (runtime.reactiveApplication leaks)
      (.application (.expire remembered.event))).support) :
    runtime.ReactiveFrontier leaks after memories frontier := by
  let execution := control.execution
  let event := remembered.event
  have distinct := runtime.prescribedReactivePosterior_events_nodup leaks who (profile who)
    (consistent who) quiet sent (memories who) (supported who)
  have originalEq := runtime.originalConfig_silent_expiry leaks execution after memories who
    event ready entered activated due payload binding checks outputEq codeEq node entry
      remembered retained matching rfl distinct moved
  have failed := runtime.reactiveSilentDecision_history_failure leaks initial horizon scheduler
    control trace valid who remembered ready payload binding checks outputEq codeEq node entry
      (List.of_mem_zip retained).1 matching
  have actor := runtime.prescribedReactivePosterior_owned leaks who (profile who)
    (consistent who) (memories who) (supported who) remembered (List.of_mem_zip retained).2
  have law := execution.application.config.step_eq_map_of_code event ready outputEq _ codeEq
    (cast (congrArg EventField.Action outputEq) remembered.action)
    (PMF.pure (PublicationResult.failure : PublicationResult (L.Val payload)))
    (by simp only [EventCode.eval?, execution, failed, Option.map_some])
  rw [PMF.pure_map] at law
  simp only [cast_cast, cast_eq] at law
  let semantic := execution.application.config.complete event ready remembered.action
    (cast (congrArg EventField.Value outputEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload)))
  have semanticStep : semantic ∈
      (execution.application.config.step event ready remembered.action).support := by
    rw [law, PMF.mem_support_pure_iff]
  have settled := related.settled.settle_sampled_owned _ _ _ related.inputs.symm
    (by simpa only [related.inputs] using related.reachable) remembered
    (List.mem_filter.mp (by
      rw [related.intentions who]
      exact List.mem_filterMap.mpr ⟨some remembered, (List.of_mem_zip retained).2, rfl⟩ :
        remembered ∈ graph.ownCompletions who frontier.history)).1 who actor ready semanticStep
  have configEq : after.application.config = execution.application.config.complete event ready
      (cast (congrArg EventField.Action outputEq.symm) false)
      (cast (congrArg EventField.Value outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) := by
    unfold ReactiveApplication.Execution.environmentStep at moved
    obtain ⟨next, selected, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ selected
    change state ∈ (runtime.environmentStep execution.application
      (.expire event)).support at changed
    rw [environmentStep_expire_resolve_eq runtime execution.application event ready entered
      activated due who payload binding checks outputEq codeEq node] at changed
    cases (PMF.mem_support_pure_iff _ _).mp changed
    rfl
  constructor
  · rw [configEq]
    exact related.reachable
  · rw [configEq]
    exact related.inputs
  · intro query
    rw [configEq, Config.complete_cut, EventOrder.Cut.mem_complete]
    constructor
    · intro completed
      rcases (related.domain query).mp completed with physical | saved
      · exact Or.inl (Or.inr physical)
      · exact Or.inr saved
    · rintro ((same | physical) | saved)
      · exact (related.domain query).mpr (Or.inr
          ⟨who, remembered, (List.of_mem_zip retained).2, same.symm⟩)
      · exact (related.domain query).mpr (Or.inl physical)
      · exact (related.domain query).mpr (Or.inr saved)
  · rw [configEq]
    simpa only [semantic, Config.CompletedOutputAgreement, Config.complete] using settled
  · exact related.intentions
  · intro observer
    rw [originalEq]
    change (graph.ownCompletions observer
      ((runtime.originalConfig leaks execution memories).history ++ [remembered])) <+:
        graph.ownCompletions observer frontier.history
    by_cases equal : observer = who
    · subst observer
      have suffix := related.pending_owner_suffix runtime leaks ordered execution
        (runtime.entryEventStable_history leaks initial horizon scheduler trace)
        memories frontier profile consistent supported who remembered
        (List.of_mem_zip retained).2 ready
      have ownAppend : graph.ownCompletions who
          ((runtime.originalConfig leaks execution memories).history ++ [remembered]) =
          graph.ownCompletions who (runtime.originalConfig leaks execution memories).history ++
            [remembered] := by simp [ownCompletions, actor]
      rw [ownAppend, ← suffix]
    · have foreign : graph.actor? remembered.event ≠ some observer := by
        simpa only [actor, Option.some.injEq, ne_eq] using Ne.symm equal
      simpa only [ownCompletions, List.filter_append, List.filter_cons, List.filter_nil,
        foreign, decide_false, Bool.false_eq_true, ↓reduceIte, List.append_nil, execution]
        using related.recalled observer

end Vegas.EventGraphRuntime
