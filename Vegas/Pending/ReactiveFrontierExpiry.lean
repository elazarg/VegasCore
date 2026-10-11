/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.ReactiveChronologicalRecall
import Vegas.Pending.ReactiveResolutionRecall
import Vegas.Pending.ReactivePolicyFacts
import Vegas.Pending.ReactiveFrontierRecall
import Vegas.Pending.ReactivePosteriorUniqueness
import Vegas.EventGraph.ConfigRestriction
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveRawRoundTrace
import Vegas.Pending.ReactiveSampledFrontierFreshness
import Vegas.Pending.ReactiveStateInvariant

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
    (ordered : graph.RevealRelaxedOrdered)
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

private theorem recordedClock_le_at_prefix {Entry : Type} (clock : Entry → Nat)
    (before later : List Entry) (timely sampled : Entry)
    (chronological : (before ++ [timely] ++ later).Pairwise
      (fun earlier next => clock earlier ≤
        clock next))
    (recorded : sampled ∈ before ++ [timely]) :
    clock sampled ≤
      clock timely := by
  have prefixOrdered := (List.pairwise_append.mp chronological).1
  have separated := (List.pairwise_append.mp prefixOrdered).2.2
  rcases List.mem_append.mp recorded with earlier | equal
  · exact separated sampled earlier timely (List.mem_singleton.mpr rfl)
  · cases List.mem_singleton.mp equal
    exact Nat.le_refl _

/-- Opportunity and actual recall provenance locate a sampled intention no later
 than the owner response delay, even when that response retained an older sample. -/
theorem late_owner_timely_sample_origin
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks (inputs.map State.initial) horizon scheduler delay)
    (ordered : graph.RevealRelaxedOrdered)
    (control : (runtime.reactiveApplication leaks).Control)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (event : graph.EventId) (who : Player) (actor : graph.actor? event = some who)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (late : entered + delay event < control.execution.application.clock)
    (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (control.execution.recall who))
    (quiet : ∀ record ∈ control.execution.recall who,
      record.action.transmission = none → record.emitted = none)
    (sent : ∀ record ∈ control.execution.recall who, ∀ material,
      record.action.transmission = some material → ∃ message,
        record.emitted = some message ∧ message.payload.call = material.call.packet)
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈ ((runtime.prescribedReactiveImplementation leaks who policy).posterior
      (control.execution.recall who)).support) :
    ∃ entry remembered,
      (entry, some remembered) ∈ (control.execution.recall who).zip intentions ∧
      remembered.event = event ∧
      entry.beforeView.application.publicView.clock ≤ entered + delay event ∧
      entry.beforeView.application.publicView.EventReady event ∧
      entry.beforeView.application.publicView.activatedAt event = some entered := by
  let app := runtime.reactiveApplication leaks
  have activatedOwner := opportunity control trace event who entered actor
    ((control.execution.application.publicView_eventReady event).mpr ready) activated late
  obtain ⟨before, _, _, response, retained, viewed, turn, _, responded⟩ :=
    runtime.owner_response_within_delay leaks (inputs.map State.initial) horizon scheduler delay
      opportunity ordered control trace idle event who entered actor activatedOwner
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp retained
  have split' : control.execution.recall who = (earlier ++ [response]) ++ later := by
    simpa only [List.append_assoc, List.singleton_append] using split
  have responseOwner : response.beforeView.application.who = who := by
    simp only [viewed, ReactiveApplication.Execution.observe, reactiveApplication,
      State.playerView]
  have turn' : response.beforeView.application.publicView.ownTurn? who = some event := by
    simpa only [viewed, ReactiveApplication.Execution.observe, app, reactiveApplication,
      State.playerView] using turn
  have responseReady :=
    (response.beforeView.application.publicView.ownTurn?_spec who event turn').1
  obtain ⟨remembered, sampling, priorMemory, _, priorSupport, _, named, paired, fullPair⟩ :=
    runtime.prescribedReactivePosterior_ready_prefix_origin leaks who policy earlier later response
      (split' ▸ consistent)
      (fun record member => quiet record (split' ▸ List.mem_append_left later member))
      (fun record member => sent record (split' ▸ List.mem_append_left later member))
      event turn' responseOwner responseReady actor intentions (split' ▸ supported)
  have sampleMember : sampling ∈ earlier ++ [response] := by
    have projected : sampling ∈ ((earlier ++ [response]).zip priorMemory).map Prod.fst :=
      List.mem_map.mpr ⟨(sampling, some remembered), paired, rfl⟩
    rw [List.map_fst_zip] at projected
    · exact projected
    · exact (runtime.prescribedReactivePosterior_length leaks who policy
        ((split' ▸ consistent).of_append) priorMemory priorSupport).symm.le
  have full : (sampling, some remembered) ∈ (control.execution.recall who).zip intentions :=
    split' ▸ fullPair
  obtain ⟨oldHistory, oldMemory, produced⟩ :=
    runtime.prescribedReactivePosterior_paired_response leaks who policy consistent intentions
      supported sampling remembered full
  have sampledReady := (runtime.prescribedReactiveResponse_some_ready leaks who policy oldHistory
    oldMemory sampling.beforeView sampling.action remembered produced).1
  have priorClock := recordedClock_le_at_prefix
    (fun entry : app.PlayerEntry => entry.beforeView.application.publicView.clock)
    earlier later response sampling
    (split' ▸ (runtime.chronologicalRecall_history leaks (inputs.map State.initial) horizon
      scheduler control trace).2 who) sampleMember
  have responseClock : response.beforeView.application.publicView.clock ≤
      entered + delay event := by
    simpa only [viewed, ReactiveApplication.Execution.observe, app, reactiveApplication,
      State.playerView, State.publicView] using responded
  have sampleRetained : sampling ∈ control.execution.recall who :=
    split' ▸ List.mem_append_left later sampleMember
  refine ⟨sampling, remembered, full, named, priorClock.trans responseClock,
    named ▸ sampledReady, ?_⟩
  exact runtime.recorded_ready_activatedAt leaks inputs horizon scheduler control trace who sampling
    sampleRetained event (named ▸ sampledReady) actor ready entered activated

/-- The first supported prescribed sample occurs within the readiness episode's
 opportunity delay; otherwise an earlier timely sample would already be remembered. -/
theorem prescribedReactiveResponse_within_delay (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks (inputs.map State.initial) horizon scheduler delay)
    (ordered : graph.RevealRelaxedOrdered)
    (remaining : Nat) (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (execution.recall who))
    (intentions : List (Option graph.Completion))
    (supported : intentions ∈ ((runtime.prescribedReactiveImplementation leaks who policy).posterior
      (execution.recall who)).support)
    (action : (runtime.reactiveApplication leaks).Action) (remembered : graph.Completion)
    (produced : (action, some remembered) ∈ (runtime.prescribedReactiveResponse leaks who policy
      (execution.recall who) intentions (execution.observe (runtime.reactiveApplication leaks)
        who)).support) :
    ∃ entered, execution.application.activatedAt remembered.event = some entered ∧
      execution.application.clock ≤ entered + delay remembered.event := by
  let app := runtime.reactiveApplication leaks
  let after := execution.respond app who action
  have positive : action ∈ (runtime.prescribedReactivePolicy leaks who policy
      (execution.recall who) (execution.observe app who)).support := by
    rw [runtime.prescribedReactivePolicy_apply, PMF.support_bind]
    refine Set.mem_iUnion₂.mpr ⟨intentions, supported, ?_⟩
    rw [PMF.support_map]
    exact ⟨(action, some remembered), produced, rfl⟩
  obtain ⟨afterTrace⟩ := app.raw_trace_respond (inputs.map State.initial) horizon scheduler
    remaining
    execution who action trace
  have afterConsistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (after.recall who) := by
    simp only [after, ReactiveApplication.Execution.respond, ↓reduceIte]
    exact .snoc _ consistent positive
  have afterSupported : intentions ++ [some remembered] ∈
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (after.recall who)).support := by
    apply (runtime.prescribedReactiveImplementation leaks who policy).mem_support_posterior_respond
      execution who intentions (intentions ++ [some remembered]) supported action
    change (action, intentions ++ [some remembered]) ∈
      ((runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
        (execution.observe app who)).map
          (fun response => (response.1, intentions ++ [response.2]))).support
    rw [PMF.support_map]
    exact ⟨(action, some remembered), produced, rfl⟩
  have beforeFaithful := runtime.reactiveEmission_history leaks (inputs.map State.initial) horizon
    scheduler ⟨remaining, some who, execution⟩ trace
  have afterFaithful := runtime.reactiveEmission_history leaks (inputs.map State.initial) horizon
    scheduler ⟨remaining, none, after⟩ afterTrace
  have eventFacts := runtime.prescribedReactiveResponse_some_ready leaks who policy
    (execution.recall who) intentions (execution.observe app who) action remembered produced
  have ready : execution.application.config.cut.Ready remembered.event :=
    (execution.application.publicView_eventReady remembered.event).mp eventFacts.1
  obtain ⟨_, _, invariant⟩ := runtime.reactive_history_invariant leaks inputs horizon scheduler
    trace
  obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor remembered.event
    ready (by simp only [eventFacts.2, Option.isSome_some])
  refine ⟨entered, activated, ?_⟩
  by_contra notWithin
  have responseFacts := runtime.reactive_respond_application leaks execution who action
  have afterReady : after.application.config.cut.Ready remembered.event := by
    change (execution.respond app who action).application.config.cut.Ready remembered.event
    rw [responseFacts.1]
    exact ready
  have clockEq : after.application.clock = execution.application.clock :=
    congrArg (fun view => view.clock) responseFacts.2
  have afterActivated : after.application.activatedAt remembered.event = some entered :=
    (congrArg (fun view => view.activatedAt remembered.event) responseFacts.2).trans activated
  have late : entered + delay remembered.event < after.application.clock := by
    rw [clockEq]
    omega
  obtain ⟨entry, original, paired, named, sampledWithin, _, _⟩ :=
    runtime.late_owner_timely_sample_origin leaks inputs horizon scheduler delay opportunity
      ordered ⟨remaining, none, after⟩ afterTrace rfl remembered.event who eventFacts.2 afterReady
      entered afterActivated late policy afterConsistent (afterFaithful who).1
      (afterFaithful who).2 (intentions ++ [some remembered]) afterSupported
  have aligned := (runtime.prescribedReactivePosterior_length leaks who policy consistent intentions
    supported).symm
  simp only [after, ReactiveApplication.Execution.respond, ↓reduceIte] at paired
  rw [List.zip_append aligned] at paired
  rcases List.mem_append.mp paired with earlier | current
  · have fresh := runtime.prescribedReactiveResponse_event_not_saved leaks who policy consistent
      (beforeFaithful who).1 (beforeFaithful who).2 intentions supported
      (execution.observe app who) action remembered produced
    apply fresh
    have inMemory : some original ∈ intentions := by
      have projected : some original ∈ ((execution.recall who).zip intentions).map Prod.snd :=
        List.mem_map.mpr ⟨(entry, some original), earlier, rfl⟩
      rw [List.map_snd_zip aligned.symm.le] at projected
      exact projected
    exact List.mem_filterMap.mpr ⟨some original, inMemory, by simp only [Option.map_some, named]⟩
  · have equal := List.mem_singleton.mp (by
      simpa only [List.zip_cons_cons, List.zip_nil_left] using current)
    have sameEntry := congrArg Prod.fst equal
    dsimp only at sameEntry
    rw [sameEntry] at sampledWithin
    exact notWithin sampledWithin

/-- Genuine prescribed transmissions reserve the contract's full inclusion bound
 before the deadline, using actual opportunity rather than assumed packet timing. -/
theorem prescribedReactivePolicy_inclusion_fits (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (delay bound : graph.EventId → Nat)
    (opportunity : runtime.Opportunity leaks (inputs.map State.initial) horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound) (ordered : graph.RevealRelaxedOrdered)
    (remaining : Nat) (execution : (runtime.reactiveApplication leaks).Execution) (who : Player)
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (policy : graph.BehavioralPolicy who)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (execution.recall who))
    (action : (runtime.reactiveApplication leaks).Action)
    (positive : action ∈ (runtime.prescribedReactivePolicy leaks who policy (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)).support) :
    ∀ event, runtime.submittedEvent? leaks action = some event →
      execution.application.publicView.InclusionFitsDeadline runtime bound event := by
  rw [runtime.prescribedReactivePolicy_apply] at positive
  obtain ⟨intentions, supported, produced⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ positive)
  obtain ⟨⟨response, intention⟩, issued, rfl⟩ := PMF.support_map .. ▸ produced
  intro event named
  obtain ⟨material, transmitted⟩ : ∃ material, response.transmission = some material := by
    cases transmission : response.transmission with
    | none => simp only [submittedEvent?, transmission] at named; cases named
    | some material => exact ⟨material, rfl⟩
  cases intention with
  | none =>
      have absent := runtime.prescribedReactiveResponse_none_silent leaks who policy
        (execution.recall who) intentions _ response issued
      rw [transmitted] at absent
      cases absent
  | some remembered =>
      have facts := runtime.prescribedReactiveResponse_transmitted_event leaks who policy
        (execution.recall who) intentions _ response remembered issued material transmitted
      have eventEq : remembered.event = event := by
        have actual : material.call.packet.event? graph = some event := by
          simpa only [submittedEvent?, transmitted] using named
        exact Option.some.inj (facts.2.2.symm.trans actual)
      obtain ⟨entered, activated, responded⟩ := runtime.prescribedReactiveResponse_within_delay
        leaks inputs horizon scheduler delay opportunity ordered remaining execution who trace
          policy consistent intentions supported response remembered issued
      rw [← eventEq]
      exact PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely
        execution.application.publicView remembered.event entered
        (by simp only [facts.2.1, Option.isSome_some]) activated responded

end Vegas.EventGraphRuntime
