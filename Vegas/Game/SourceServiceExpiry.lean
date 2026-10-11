/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingResources
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveFrontierEnvironment
import Vegas.Pending.ReactiveFrontierExpiry
import Vegas.Pending.ReactiveOwnerOpportunity
import Vegas.Pending.ReactiveSingleSubmission
import Vegas.Pending.ReactiveTimelyCalls
import Vegas.Game.SourceServiceAsyncTimeliness

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A genuinely conforming timely prescribed call excludes actual due expiry:
 protected inclusion settles it before its readiness episode can become due. -/
theorem freshCall_not_due (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control))
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ earlier ++ later,
      ¬ EmitsOtherFor (serviceRuntime setup mode deadline) leaks other event message.id)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered) :
    control.execution.application.clock - entered < deadline event := by
  by_contra notBefore
  have due : deadline event ≤ control.execution.application.clock - entered := by omega
  have retained : entry ∈ control.execution.recall owner := by
    rw [split]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  have stable := (serviceRuntime setup mode deadline).entryEventStable_history leaks
    (serviceInitialLaw setup mode) horizon scheduler trace
  obtain ⟨_, _, _, episode, _⟩ := stable owner entry retained event call.ready ready.1
  obtain ⟨beforeEntered, recorded, fits⟩ := call.fits.exists
  have same := episode owner owned beforeEntered recorded
  rw [activated] at same
  have equal := Option.some.inj same
  subst beforeEntered
  change entry.beforeView.application.publicView.clock - entered + bound event <
    deadline event at fits
  have late : entry.beforeView.application.publicView.clock + bound event <
      control.execution.application.clock := by omega
  have receipt := (prescribed_packet_settles setup leaks inclusion trace event owner owned
    earlier later entry message split call sole).1 late
  have settled := settlesFreshCalls_history setup leaks inclusion owner event owned trace
    earlier entry later message split call sole
  exact ready.1 (settled.2.2 receipt)

/-- Actual recorded prescribed transmissions satisfy protected inclusion from
 their recorded conformance and the derived timing of their callback. -/
theorem recorded_prescribed_transmission_not_due
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control))
    (owner : Player) (policy : (serviceGraph setup mode).BehavioralPolicy owner)
    (consistent : ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks owner
      policy).Consistent (control.execution.recall owner))
    (quiet : ∀ record ∈ control.execution.recall owner,
      record.action.transmission = none → record.emitted = none)
    (faithful : ∀ record ∈ control.execution.recall owner, ∀ material,
      record.action.transmission = some material → ∃ message,
        record.emitted = some message ∧ message.payload.call = material.call.packet)
    (conformance : (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks control.execution)
    (earlier later : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (entry : (serviceApplication setup mode deadline leaks).PlayerEntry)
    (split : control.execution.recall owner = earlier ++ entry :: later)
    (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (ready : control.execution.application.config.cut.Ready event)
    (beforeReady : entry.beforeView.application.publicView.EventReady event)
    (entered : Nat)
    (activated : control.execution.application.activatedAt event = some entered)
    (beforeActivated : entry.beforeView.application.publicView.activatedAt event = some entered)
    (responded : entry.beforeView.application.publicView.clock ≤ entered + delay event)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (transmitted : entry.action.transmission = some material)
    (addressed : material.call.packet.event? (serviceGraph setup mode) = some event)
    :
    control.execution.application.clock - entered < deadline event := by
  let runtime := serviceRuntime setup mode deadline
  have retained : entry ∈ control.execution.recall owner := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  obtain ⟨message, emitted, packet⟩ := faithful entry retained material transmitted
  have named : message.payload.call.event? (serviceGraph setup mode) = some event := by
    rw [packet]
    exact addressed
  have fits := PublicView.inclusionFitsDeadline_of_response_delay runtime delay bound timely
    entry.beforeView.application.publicView event entered
    (by simp only [owned, Option.isSome_some]) beforeActivated responded
  have recalled : control.execution.InputRecall
      (serviceApplication setup mode deadline leaks) :=
    (serviceApplication setup mode deadline leaks).history_inputRecall
      (serviceInitialLaw setup mode) horizon scheduler trace
  have recordedMessage : message ∈
      (serviceApplication setup mode deadline leaks).outputs (control.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, retained, emitted⟩
  rw [← recalled owner] at recordedMessage
  have authored : message.sender = owner := by
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp recordedMessage).2
  have call : FreshCall setup leaks owner event bound entry message :=
    ⟨⟨material, transmitted⟩, emitted, authored, named, beforeReady, fits,
      conformance owner entry retained message event emitted named fits.withinDeadline⟩
  have once := runtime.prescribedReactiveSubmittedEvents_nodup leaks owner policy
    consistent quiet faithful
  rw [split] at once
  have sole := runtime.prescribedReactiveEmission_sole leaks earlier later entry message event
    once emitted named
  exact freshCall_not_due setup leaks inclusion control trace event owner owned earlier later
    entry message split call sole ready entered activated

/-- A genuinely due source service event has a sampled silent original intention:
 any transmitted intention would already have settled under protected inclusion. -/
theorem due_prescribed_intention_silent
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (actor : (serviceGraph setup mode).actor? event = some who)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : deadline event ≤ control.execution.application.clock - entered)
    (policy : (serviceGraph setup mode).BehavioralPolicy who)
    (consistent : ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
      policy).Consistent (control.execution.recall who))
    (quiet : ∀ record ∈ control.execution.recall who,
      record.action.transmission = none → record.emitted = none)
    (sent : ∀ record ∈ control.execution.recall who, ∀ material,
      record.action.transmission = some material → ∃ message,
        record.emitted = some message ∧ message.payload.call = material.call.packet)
    (conformance : (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks control.execution)
    (intentions : List (Option (serviceGraph setup mode).Completion))
    (supported : intentions ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation
        leaks who policy).posterior (control.execution.recall who)).support) :
    ∃ entry remembered,
      (entry, some remembered) ∈ (control.execution.recall who).zip intentions ∧
      remembered.event = event ∧
      (serviceRuntime setup mode deadline).ReactiveSilentDecision leaks who entry remembered := by
  let runtime := serviceRuntime setup mode deadline
  let inputs : PMF (serviceGraph setup mode).Inputs :=
    setup.initialLaw.map setup.eventInputs
  have initialEq : inputs.map (State.initial (graph := serviceGraph setup mode)) =
      serviceInitialLaw setup mode := by
    simp only [inputs, PMF.map_comp, Function.comp_def, serviceInitialLaw]
  have margin := timely event (by simp only [actor, Option.isSome_some])
  change delay event + bound event < deadline event at margin
  obtain ⟨entry, remembered, paired, named, responded, beforeReady, beforeActivated⟩ :=
    runtime.late_owner_timely_sample_origin leaks inputs horizon scheduler delay
      (initialEq ▸ opportunity) ordered control (initialEq ▸ trace) idle event who actor
      ready entered activated (by omega) policy consistent quiet sent intentions supported
  obtain ⟨oldHistory, oldMemory, produced⟩ := runtime.prescribedReactivePosterior_paired_response
    leaks who policy consistent intentions supported entry remembered paired
  have retained : entry ∈ control.execution.recall who := by
    have lengthEq := runtime.prescribedReactivePosterior_length leaks who policy consistent
      intentions supported
    have projected : entry ∈ ((control.execution.recall who).zip intentions).map Prod.fst :=
      List.mem_map.mpr ⟨(entry, some remembered), paired, rfl⟩
    rwa [List.map_fst_zip lengthEq.symm.le] at projected
  have silent : entry.action.transmission = none := by
    cases transmitted : entry.action.transmission with
    | none => rfl
    | some material =>
        obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp retained
        have addressed := (runtime.prescribedReactiveResponse_transmitted_event leaks who policy
          oldHistory oldMemory entry.beforeView entry.action remembered produced material
          transmitted).2.2
        rw [named] at addressed
        have notDue := recorded_prescribed_transmission_not_due setup leaks delay bound timely
          inclusion control trace who policy consistent quiet sent conformance earlier later entry
          split event actor ready beforeReady entered activated beforeActivated responded material
          transmitted addressed
        omega
  exact ⟨entry, remembered, paired, named,
    runtime.prescribedReactivePosterior_silent_alignment leaks who policy consistent quiet
      intentions supported entry remembered paired silent⟩

/-- Authentic prescribed binding decisions cannot remain ready at a due expiry;
 the actual opportunity, retained sample and protected call already exclude it. -/
theorem source_prescribed_due_binding_impossible
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .bind who payload)
    (node : nodeView (serviceGraph setup mode) event = .bind who payload outputEq codeEq)
    (ready : control.execution.application.config.cut.Ready event)
    (entered : Nat) (activated : control.execution.application.activatedAt event = some entered)
    (due : deadline event ≤ control.execution.application.clock - entered)
    (policy : (serviceGraph setup mode).BehavioralPolicy who)
    (consistent : ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
      policy).Consistent (control.execution.recall who))
    (conformance : (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks control.execution)
    (intentions : List (Option (serviceGraph setup mode).Completion))
    (supported : intentions ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks who
        policy).posterior (control.execution.recall who)).support) : False := by
  let runtime := serviceRuntime setup mode deadline
  obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
    horizon scheduler control trace who
  obtain ⟨entry, remembered, paired, named, matching⟩ := due_prescribed_intention_silent setup leaks
    horizon scheduler delay bound opportunity timely inclusion ordered control trace idle who event
    (nodeView_bind_actor outputEq codeEq) ready entered activated due policy consistent quiet sent
    conformance intentions supported
  subst event
  have retained : entry ∈ control.execution.recall who := by
    have projected : entry ∈ ((control.execution.recall who).zip intentions).map Prod.fst :=
      List.mem_map.mpr ⟨_, paired, rfl⟩
    rwa [List.map_fst_zip (runtime.prescribedReactivePosterior_length leaks who policy
      consistent _ supported).symm.le] at projected
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map setup.eventInputs
  have initialEq : inputs.map State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  obtain ⟨serial, _, allocated⟩ := runtime.reactiveFreshSlot_recorded leaks inputs horizon scheduler
    control (initialEq.symm ▸ trace) who entry retained
  have actionEq := matching.2.2.2.2.2.2
  have sends := runtime.reactiveDecision_binding_eq leaks who who remembered.event payload
    outputEq codeEq node remembered.action entry.beforeView.application serial allocated
  have impossible := matching.2.1
  rw [actionEq, sends] at impossible
  cases impossible

/-- Every actual supported expiry under the existing source service guarantees
 preserves the sampled frontier; silence, timing and accepted settlement are derived. -/
theorem source_prescribed_expiry_frontier
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (inclusion : ProtectedInclusion (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (control : (serviceApplication setup mode deadline leaks).Control)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control)) (idle : control.actor = none)
    (valid : control.execution.application.BindingInvariant)
    (conformance : (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks control.execution)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (consistent : ∀ owner, ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      owner (profile owner)).Consistent (control.execution.recall owner))
    (quiet : ∀ owner entry, entry ∈ control.execution.recall owner →
      entry.action.transmission = none → entry.emitted = none)
    (sent : ∀ owner entry, entry ∈ control.execution.recall owner → ∀ material,
      entry.action.transmission = some material → ∃ message,
        entry.emitted = some message ∧ message.payload.call = material.call.packet)
    (supported : ∀ owner, memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
        (profile owner)).posterior (control.execution.recall owner)).support)
    (frontier : (serviceGraph setup mode).Config)
    (related : (serviceRuntime setup mode deadline).ReactiveFrontier leaks control.execution
      memories frontier)
    (event : (serviceGraph setup mode).EventId)
    (after : (serviceApplication setup mode deadline leaks).Execution)
    (moved : after ∈ (control.execution.environmentStep
      (serviceApplication setup mode deadline leaks) (.application (.expire event))).support) :
    (serviceRuntime setup mode deadline).ReactiveFrontier leaks after memories frontier := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  have movedOriginal := moved
  obtain ⟨updated, selected, rfl⟩ := PMF.support_map .. ▸ moved
  obtain ⟨next, changed, rfl⟩ := PMF.support_map .. ▸ selected
  change next ∈ (environmentStep runtime control.execution.application (.expire event)).support
    at changed
  have stutter (same : next = control.execution.application) :
      runtime.ReactiveFrontier leaks
        { control.execution with
          application := next
          environmentRecall := control.execution.environmentRecall ++
            [⟨control.execution.observeEnvironment app, .application (.expire event)⟩] }
        memories frontier := by
    subst next
    exact ReactiveFrontier.congr_execution runtime leaks _ _ memories frontier related rfl rfl rfl
  by_cases ready : control.execution.application.config.cut.Ready event
  · cases activated : control.execution.application.activatedAt event with
    | none =>
        rw [environmentStep_expire_of_not_activated runtime _ event ready activated,
          PMF.mem_support_pure_iff] at changed
        exact stutter changed
    | some entered =>
        by_cases due : deadline event ≤ control.execution.application.clock - entered
        · cases node : nodeView (serviceGraph setup mode) event with
          | sample payload law outputEq codeEq =>
              rw [environmentStep_expire_sample_eq runtime _ event ready entered activated due
                payload law outputEq codeEq node, PMF.mem_support_pure_iff] at changed
              exact stutter changed
          | bind owner payload outputEq codeEq =>
              exact (source_prescribed_due_binding_impossible setup leaks horizon scheduler delay
                bound opportunity timely inclusion ordered control trace idle owner event payload
                outputEq codeEq node ready entered activated due (profile owner) (consistent owner)
                conformance (memories owner) (supported owner)).elim
          | resolve owner payload binding checks outputEq codeEq =>
              have actor := nodeView_resolve_actor outputEq codeEq
              obtain ⟨entry, remembered, paired, named, matching⟩ :=
                due_prescribed_intention_silent setup leaks horizon scheduler delay bound
                  opportunity timely inclusion ordered control trace idle owner event actor ready
                  entered activated due (profile owner) (consistent owner)
                  (quiet owner) (sent owner) conformance
                  (memories owner) (supported owner)
              subst event
              exact ReactiveFrontier.expire_silent_resolution runtime leaks ordered
                (serviceInitialLaw setup mode) horizon scheduler control trace valid
                memories frontier related profile consistent supported owner
                (quiet owner) (sent owner)
                entry remembered paired matching ready entered activated due
                payload binding checks outputEq codeEq node _
                movedOriginal
        · rw [environmentStep_expire_of_not_due runtime _ event ready entered activated due,
            PMF.mem_support_pure_iff] at changed
          exact stutter changed
  · rw [environmentStep_expire_of_not_ready runtime _ event ready, PMF.mem_support_pure_iff]
      at changed
    exact stutter changed

end Vegas
