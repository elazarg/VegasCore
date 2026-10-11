/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceExpiry
import Vegas.Game.SourceServiceBindingMiss
import Vegas.Game.SourceServiceTurnSubmissions
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveRecovery
import Vegas.Game.SourceServiceReactiveLaw
import Vegas.Pending.ReactivePrescribedAllocation
import Vegas.Game.SourceServiceCleanContinuation
import Vegas.Game.SourceServiceAudit
import Vegas.Pending.ReactiveSingleSubmission

/-! # Authentic settled audits throughout initialized reactive source execution -/

noncomputable section
namespace Vegas
open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A genuine supported prescribed round cannot create a public binding miss:
 any new miss would be due binding expiry, which actual protected play excludes. -/
theorem source_prescribed_no_miss_round
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (remaining : Nat) (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (valid : execution.application.BindingInvariant ∧
      (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks execution)
    (consistent : ∀ who, ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
      (profile who)).Consistent (execution.recall who))
    (clear : ∀ who, execution.application.publicView.missedBindingBy who = false)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).round scheduler
      (fun who => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
        (profile who)) execution).support) :
    ∀ who, next.application.publicView.missedBindingBy who = false := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  intro who
  classical
  apply decide_eq_false
  rintro ⟨event, owned, missing⟩
  cases node : nodeView (serviceGraph setup mode) event with
  | sample payload law outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [PublicView.missedBinding, outputEq, Bool.false_eq_true] at missing
  | bind owner payload outputEq codeEq =>
      have equal : owner = who := Option.some.inj
        ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
      subst owner
      have oldClear : execution.application.publicView.missedBinding event = false := by
        apply Bool.eq_false_of_not_eq_true
        intro missed
        have flag := execution.application.publicView.missedBindingBy_of_event who event
          owned missed
        rw [clear who] at flag
        cases flag
      obtain ⟨command, _, middle, moved, effect⟩ := round_cases setup leaks reached
      have middleMiss : middle.application.publicView.missedBinding event = true := by
        rcases effect with ⟨_, rfl⟩ | ⟨actor, _, response, _, rfl⟩
        · exact missing
        · exact (congrArg (fun view => view.missedBinding event)
            (runtime.reactive_respond_application leaks middle actor response).2).symm.trans missing
      obtain ⟨_, ready, entered, activated, due⟩ := new_binding_miss_expiry command valid.1 moved
        event who payload outputEq codeEq node oldClear middleMiss
      obtain ⟨intentions, supported⟩ :=
        ((runtime.prescribedReactiveImplementation leaks who (profile who)).posterior
          (execution.recall who)).support_nonempty
      exact source_prescribed_due_binding_impossible setup leaks horizon scheduler delay bound
        contract.opportunity timely contract.inclusion ordered ⟨remaining + 1, none, execution⟩
        trace rfl who event payload outputEq codeEq node ready entered activated due (profile who)
        (consistent who) valid.2 intentions supported



/-- Every supported actual prescribed continuation retains a clear public
 binding-omission verdict, using the unchanged asynchronous service guarantees. -/
theorem source_prescribed_no_miss_runRounds
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (count remaining : Nat)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining + count, none, execution⟩))
    (valid : execution.application.BindingInvariant ∧
      (serviceRuntime setup mode deadline).RecordedTimelyCalls leaks execution)
    (consistent : ∀ who, ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
      (profile who)).Consistent (execution.recall who))
    (clear : ∀ who, execution.application.publicView.missedBindingBy who = false)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (fun who => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
        (profile who)) count execution).support) :
    ∀ who, next.application.publicView.missedBindingBy who = false := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := fun who => runtime.prescribedReactivePolicy leaks who (profile who)
  induction count generalizing execution next with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact clear
  | succ count ih =>
      have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨remaining + count + 1, none, execution⟩) := by
        simpa only [Nat.add_assoc] using trace
      obtain ⟨middle, first, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have one : middle ∈ (app.runRounds scheduler players 1 execution).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using first
      obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
        players (remaining + count) execution middle before first
      have nextValid := (runtime.recordedTimelyCalls_policyInvariant leaks profile).runRounds
        scheduler 1 execution middle valid one
      have nextConsistent := (app.consistentRecall_policyInvariant players).runRounds
        scheduler 1 execution middle consistent one
      have nextClear := source_prescribed_no_miss_round setup leaks horizon scheduler delay bound
        contract timely ordered profile (remaining + count) execution middle before valid
        consistent clear first
      exact ih middle next middleTrace nextValid nextConsistent nextClear later

/-- Initialized actual prescribed runs have no public binding omission for any
 owner; neither acceptance nor audit cleanliness is assumed. -/
theorem source_prescribed_initialized_no_miss
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (initial : State L setup.context) (supportedInitial : initial ∈ setup.initialLaw.support)
    (count : Nat) (within : count ≤ horizon)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (fun who => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks who
        (profile who)) count
          (.initial (serviceApplication setup mode deadline leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support) :
    ∀ who, next.application.publicView.missedBindingBy who = false := by
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := fun who => runtime.prescribedReactivePolicy leaks who (profile who)
  let execution := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have supportedState : EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs initial) ∈ (serviceInitialLaw setup mode).support := by
    rw [serviceInitialLaw, PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  obtain ⟨initialTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players 0 (Nat.zero_le horizon) execution (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨EventGraphRuntime.State.initial (setup.eventInputs initial),
        supportedState, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have valid : execution.application.BindingInvariant ∧ runtime.RecordedTimelyCalls leaks
      execution := by
    refine ⟨EventGraphRuntime.State.initial_bindingInvariant _, ?_⟩
    intro who entry retained
    exact (List.not_mem_nil retained).elim
  have consistent : ∀ who, (players who).Consistent (execution.recall who) := fun _ => .nil
  have clear : ∀ who, execution.application.publicView.missedBindingBy who = false := by
    intro who
    apply PublicView.missedBindingBy_clear
    intro event
    change (EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs initial)).publicView.missedBinding event = false
    cases output : (serviceGraph setup mode).outputLayout event <;>
      simp only [PublicView.missedBinding, output, EventGraphRuntime.State.publicView,
        EventGraphRuntime.State.initial, EventGraph.publicObserve, EventGraph.Config.initial,
        List.map_nil, List.not_mem_nil, decide_false, Bool.false_and]
  exact source_prescribed_no_miss_runRounds setup leaks horizon scheduler delay bound contract
    timely ordered profile count (horizon - count) execution next
    (by simpa only [Nat.sub_add_cancel within, Nat.sub_zero] using initialTrace) valid consistent
      clear reached


section
variable [Finite Player]

/-- Every actual initialized prescribed prefix has a supported operational frontier
 for every genuine joint private posterior, under the existing asynchronous contract. -/
theorem source_prescribed_prefix_frontiers
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (initial : State L setup.context) (supportedInitial : initial ∈ setup.initialLaw.support)
    (count : Nat) (within : count ≤ horizon)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
        owner (profile owner)) count
      (ReactiveApplication.Execution.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support) :
    ∀ memories : Player → List (Option (serviceGraph setup mode).Completion),
      (∀ owner, memories owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
          (profile owner)).posterior (next.recall owner)).support) →
      ∃ frontier, (serviceRuntime setup mode deadline).ReactiveFrontier leaks next memories
        frontier := by
  let _ := Fintype.ofFinite Player
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let graph := serviceGraph setup mode
  let inputs : PMF graph.Inputs := setup.initialLaw.map setup.eventInputs
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  let safe : app.Execution → Prop := fun execution =>
    execution.application.BindingInvariant ∧ runtime.RecordedTimelyCalls leaks execution
  have initialEq : inputs.map State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  have ordered := serviceGraph_barrierOrdered setup keepsReveals
  have invariant := runtime.recordedTimelyCalls_policyInvariant leaks profile
  have expiry : ∀ remaining execution,
      Nonempty (((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
        horizon scheduler).Trace (some ⟨remaining + 1, none, execution⟩)) → safe execution →
      (∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
        (execution.recall owner)) → ∀ memories frontier,
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
      runtime.ReactiveFrontier leaks execution memories frontier → ∀ event next,
        next ∈ (execution.environmentStep (runtime.reactiveApplication leaks)
          (.application (.expire event))).support →
        runtime.ReactiveFrontier leaks next memories frontier := by
    intro remaining execution ⟨trace⟩ valid consistent memories frontier supported related
      event next moved
    have sourceTrace := initialEq ▸ trace
    have faithful := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
      horizon scheduler ⟨remaining + 1, none, execution⟩ sourceTrace
    exact source_prescribed_expiry_frontier setup leaks horizon scheduler delay bound
      contract.opportunity timely contract.inclusion ordered ⟨remaining + 1, none, execution⟩
      sourceTrace rfl valid.1 valid.2 profile memories consistent
      (fun owner => (faithful owner).1) (fun owner => (faithful owner).2)
      supported frontier related event next moved
  let execution := ReactiveApplication.Execution.initial app
    (State.initial (setup.eventInputs initial))
  have supportedInput : setup.eventInputs initial ∈ inputs.support := by
    rw [PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  have supportedState : State.initial (graph := graph) (setup.eventInputs initial) ∈
      (inputs.map State.initial).support := by
    rw [PMF.support_map]
    exact ⟨setup.eventInputs initial, supportedInput, rfl⟩
  obtain ⟨initialTrace⟩ := app.raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler
    players 0 (Nat.zero_le horizon) execution (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨State.initial (setup.eventInputs initial), supportedState, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have valid : safe execution := by
    refine ⟨State.initial_bindingInvariant _, ?_⟩
    intro owner entry member
    exact (List.not_mem_nil member).elim
  have consistent : ∀ owner, (players owner).Consistent (execution.recall owner) :=
    fun _ => ReactiveApplication.Policy.Consistent.nil
  have frontiers : ∀ memories : Player → List (Option graph.Completion),
      (∀ owner, memories owner ∈
        ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
          (execution.recall owner)).support) →
        ∃ frontier, runtime.ReactiveFrontier leaks execution memories frontier := by
    intro memories supported
    have empty : memories = fun _ => [] := by
      funext owner
      exact (PMF.mem_support_pure_iff _ _).mp (supported owner)
    rw [empty]
    exact ⟨EventGraph.Config.initial (setup.eventInputs initial),
      runtime.reactiveFrontier_initial leaks (setup.eventInputs initial)⟩
  have horizonEq : horizon - count + count = horizon := Nat.sub_add_cancel within
  have trace : (app.protocol (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨horizon - count + count, none, execution⟩) := by
    simpa only [horizonEq, Nat.sub_zero] using initialTrace
  exact (runRounds_posterior_potential_of_expiry runtime leaks ordered profile inputs horizon
    scheduler safe invariant expiry count (horizon - count) execution trace valid consistent
      frontiers).2 next reached


end

/-- Genuine initialized prescribed callbacks emit canonical source-audit packets;
 timing and prepared serials follow from the actual operational invariants. -/
theorem source_prescribed_response_conforming
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (valid : execution.application.BindingInvariant)
    (consistent : ∀ owner, ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      owner (profile owner)).Consistent (execution.recall owner))
    (memories : Player → List (Option (serviceGraph setup mode).Completion))
    (supported : ∀ owner, memories owner ∈
      (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
        (profile owner)).posterior (execution.recall owner)).support)
    (frontier : (serviceGraph setup mode).Config)
    (related : (serviceRuntime setup mode deadline).ReactiveFrontier leaks execution memories
      frontier)
    (allocated : (serviceRuntime setup mode deadline).PrescribedCandidateAllocation leaks execution)
    (remembered : (serviceGraph setup mode).Completion)
    (material : WitnessedSubmission (serviceGraph setup mode))
    (produced : (⟨some material⟩, some remembered) ∈
      ((serviceRuntime setup mode deadline).prescribedReactiveResponse leaks who (profile who)
        (execution.recall who) (memories who)
          (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    (serviceRuntime setup mode deadline).freshServiceEnvelope execution.application.publicView
      ⟨(who, execution.network.nextSerial who),
        material.emit ((serviceApplication setup mode deadline leaks).submit execution.application
          who material) who (execution.network.known who)⟩ := by
  let runtime := serviceRuntime setup mode deadline
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map setup.eventInputs
  have initialEq : inputs.map State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  have eventFacts := runtime.prescribedReactiveResponse_some_ready leaks who (profile who)
    (execution.recall who) (memories who)
    (execution.observe (serviceApplication setup mode deadline leaks) who)
    ⟨some material⟩ remembered produced
  obtain ⟨quiet, sent⟩ := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
    horizon scheduler ⟨remaining, some who, execution⟩ trace who
  have fresh := runtime.prescribedReactiveResponse_event_not_saved leaks who (profile who)
    (consistent who) quiet sent (memories who) (supported who)
    (execution.observe (serviceApplication setup mode deadline leaks) who)
    ⟨some material⟩ remembered produced
  have prepared := related.fresh_preparedPrefix runtime leaks ordered inputs horizon scheduler
    ⟨remaining, some who, execution⟩ (initialEq.symm ▸ trace) profile memories consistent supported
    frontier allocated who remembered.event
    ((execution.application.publicView_eventReady remembered.event).mp eventFacts.1)
    eventFacts.2 fresh
  obtain ⟨entered, activated, responded⟩ := runtime.prescribedReactiveResponse_within_delay leaks
    inputs horizon scheduler delay (initialEq.symm ▸ opportunity) ordered remaining execution who
      (initialEq.symm ▸ trace) (profile who) (consistent who) (memories who) (supported who)
        ⟨some material⟩ remembered produced
  have within : execution.application.WithinDeadline runtime remembered.event := by
    change match execution.application.activatedAt remembered.event with
      | none => False
      | some entered => execution.application.clock - entered < deadline remembered.event
    rw [activated]
    have margin := timely remembered.event (by simp only [eventFacts.2, Option.isSome_some])
    change delay remembered.event + bound remembered.event < deadline remembered.event at margin
    omega
  exact runtime.prescribedReactiveResponse_emitted_conforming leaks execution valid who
    (profile who) (execution.recall who) (memories who) material remembered produced within prepared

/-- Every actual supported compiler callback inherits canonical conformance from
 the genuine joint posterior frontier and initialized allocation invariant. -/
theorem source_prescribed_policy_conforming
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (opportunity : (serviceRuntime setup mode deadline).Opportunity leaks
      (serviceInitialLaw setup mode) horizon scheduler delay)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (remaining : Nat) (execution : (serviceApplication setup mode deadline leaks).Execution)
    (who : Player)
    (trace : ((serviceApplication setup mode deadline leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (valid : execution.application.BindingInvariant)
    (consistent : ∀ owner, ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      owner (profile owner)).Consistent (execution.recall owner))
    (frontiers : ∀ memories : Player → List (Option (serviceGraph setup mode).Completion),
      (∀ owner, memories owner ∈
        (((serviceRuntime setup mode deadline).prescribedReactiveImplementation leaks owner
          (profile owner)).posterior (execution.recall owner)).support) →
      ∃ frontier, (serviceRuntime setup mode deadline).ReactiveFrontier leaks execution memories
        frontier)
    (allocated : (serviceRuntime setup mode deadline).PrescribedCandidateAllocation leaks execution)
    (action : (serviceApplication setup mode deadline leaks).Action)
    (positive : action ∈ ((serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
      who (profile who) (execution.recall who)
        (execution.observe (serviceApplication setup mode deadline leaks) who)).support) :
    ∀ material, action.transmission = some material →
      (serviceRuntime setup mode deadline).freshServiceEnvelope execution.application.publicView
        ⟨(who, execution.network.nextSerial who),
          (serviceApplication setup mode deadline leaks).packet
            ((serviceApplication setup mode deadline leaks).submit execution.application who
              material) who (execution.network.known who) material⟩ := by
  classical
  let runtime := serviceRuntime setup mode deadline
  rw [runtime.prescribedReactivePolicy_apply] at positive
  obtain ⟨intentions, supported, produced⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ positive)
  obtain ⟨⟨response, intention⟩, issued, rfl⟩ := PMF.support_map .. ▸ produced
  intro material transmitted
  cases intention with
  | none =>
      have silent := runtime.prescribedReactiveResponse_none_silent leaks who (profile who)
        (execution.recall who) intentions _ response issued
      rw [transmitted] at silent
      cases silent
  | some remembered =>
      have inhabited : ∀ owner, ∃ memory, memory ∈
          ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
            (execution.recall owner)).support := fun owner => PMF.support_nonempty _
      choose other otherSupported using inhabited
      let memories := Function.update other who intentions
      have allSupported : ∀ owner, memories owner ∈
          ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
            (execution.recall owner)).support := by
        intro owner
        by_cases same : owner = who
        · subst owner
          simpa only [memories, Function.update_self] using supported
        · simpa only [memories, Function.update_of_ne same] using otherSupported owner
      obtain ⟨frontier, related⟩ := frontiers memories allSupported
      have actual : response = (⟨some material⟩ :
          (serviceApplication setup mode deadline leaks).Action) := by
        cases response
        cases transmitted
        rfl
      subst response
      apply source_prescribed_response_conforming setup leaks horizon scheduler delay bound
        opportunity timely ordered profile remaining execution who trace valid
        consistent memories allSupported frontier related allocated remembered material
      simpa only [memories, Function.update_self] using issued


section
variable [Finite Player]

/-- Genuine initialized prescribed prefixes preserve authentic bound-aware calls
 and good settled packet content through the actual native scheduler rounds. -/
theorem source_prescribed_packetFacts_runRounds
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (initial : State L setup.context) (supportedInitial : initial ∈ setup.initialLaw.support)
    (count : Nat) (within : count ≤ horizon)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
        owner (profile owner)) count
      (.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support) :
    ∀ who, OwnFreshCalls setup leaks bound next who ∧ FreshCallsConform setup leaks next who ∧
      OneCallPerEvent setup leaks next who ∧
      ∀ message, message.sender = who → Emitted setup leaks next message →
        SettledGood setup leaks next message := by
  let _ := Fintype.ofFinite Player
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map setup.eventInputs
  have initialEq : inputs.map EventGraphRuntime.State.initial = serviceInitialLaw setup mode := by
    simp only [inputs, serviceInitialLaw, PMF.map_comp, Function.comp_def]
  let start := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have startSafe : start.application.BindingInvariant ∧
      runtime.RecordedTimelyCalls leaks start := by
    refine ⟨EventGraphRuntime.State.initial_bindingInvariant _, ?_⟩
    intro owner entry member
    exact (List.not_mem_nil member).elim
  have startConsistent : ∀ owner, (players owner).Consistent (start.recall owner) := fun _ => .nil
  have initialSupported : EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs initial) ∈ (serviceInitialLaw setup mode).support := by
    rw [serviceInitialLaw, PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players 0 (Nat.zero_le horizon) start (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨_, initialSupported, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  induction count generalizing next with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      intro owner
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro entry member
        exact (List.not_mem_nil member).elim
      · intro entry member
        exact (List.not_mem_nil member).elim
      · intro first member
        exact (List.not_mem_nil member).elim
      · intro message _ emitted
        exact (List.not_mem_nil emitted).elim
  | succ count ih =>
      have supportSplit : next ∈ ((app.runRounds scheduler players count start).bind
          (app.runRounds scheduler players 1)).support := by
        change next ∈ (app.runRounds scheduler players (count + 1) start).support at reached
        rwa [app.runRounds_add scheduler players count 1 start] at reached
      obtain ⟨execution, earlierSupport, last⟩ := Set.mem_iUnion₂.mp
        (PMF.support_bind .. ▸ supportSplit)
      have before := ih (by omega) execution earlierSupport
      have countWithin : count ≤ horizon := by omega
      have horizonEq : horizon - count + count = horizon := Nat.sub_add_cancel countWithin
      have initializedTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨horizon - count + count, none, start⟩) := by
        simpa only [horizonEq, Nat.sub_zero] using startTrace
      obtain ⟨executionTrace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon
        scheduler players (horizon - count) count start execution initializedTrace earlierSupport
      have executionSafe := (runtime.recordedTimelyCalls_policyInvariant leaks profile).runRounds
        scheduler count start execution startSafe earlierSupport
      have executionConsistent := (app.consistentRecall_policyInvariant players).runRounds
        scheduler count start execution startConsistent earlierSupport
      have executionFrontiers := source_prescribed_prefix_frontiers setup keepsReveals leaks
        horizon scheduler delay bound contract timely profile initial supportedInitial count
        countWithin execution earlierSupport
      have roundSupported : next ∈ (app.round scheduler players execution).support := by
        simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using last
      obtain ⟨command, selected, middle, moved, effect⟩ := round_cases setup leaks roundSupported
      have remainingEq : horizon - count = (horizon - (count + 1)) + 1 := by omega
      have idleTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨horizon - (count + 1) + 1, none, execution⟩) := by
        simpa only [remainingEq] using executionTrace
      obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon
        scheduler (horizon - (count + 1)) execution middle command idleTrace selected moved
      have facts := settledFacts_history (serviceInitialLaw setup mode) horizon scheduler idleTrace
      have middleFacts := fun owner => ownerPacketFacts_environment contract.inclusion facts moved
        middleTrace owner (before owner).1 (before owner).2.1 (before owner).2.2.1
          (before owner).2.2.2
      rcases effect with ⟨_, rfl⟩ | ⟨responder, active, response, positive, rfl⟩
      · exact middleFacts
      · rw [active] at middleTrace
        have activated : command = .activate responder := by
          cases command with
          | wait => cases active
          | activate owner =>
              exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
          | «include» id => cases active
          | application command => cases command <;> cases active
        have recallEq := app.environmentStep_recall execution middle command moved
        have middleSafe := (runtime.recordedTimelyCalls_policyInvariant leaks profile).environment
          execution middle command executionSafe moved
        have middleConsistent : ∀ owner, (players owner).Consistent (middle.recall owner) := by
          simpa only [recallEq] using executionConsistent
        have middleFrontiers : ∀ memories : Player →
            List (Option (serviceGraph setup mode).Completion),
            (∀ owner, memories owner ∈ ((runtime.prescribedReactiveImplementation leaks owner
              (profile owner)).posterior (middle.recall owner)).support) →
            ∃ frontier, runtime.ReactiveFrontier leaks middle memories frontier := by
          intro memories supported
          obtain ⟨frontier, related⟩ := executionFrontiers memories (by
            simpa only [recallEq] using supported)
          exact related.passive_command_frontier_exists runtime leaks execution memories frontier
            command (Or.inr (Or.inl ⟨responder, activated⟩)) middle moved
        have allocated := runtime.prescribedCandidateAllocation_runRounds leaks profile
          (setup.eventInputs initial) scheduler count execution earlierSupport
        have middleAllocated := allocated.environment runtime leaks execution middle
          (legalFacts setup leaks horizon scheduler _ idleTrace).provenance command moved
        have faithful := runtime.reactiveEmission_history leaks (serviceInitialLaw setup mode)
          horizon scheduler _ middleTrace responder
        have first := runtime.prescribedReactivePolicy_firstSubmission leaks responder
          (profile responder) (middle.recall responder) (middle.observe app responder) response
            positive faithful.2
        have fresh := source_prescribed_policy_conforming setup leaks horizon scheduler delay bound
          contract.opportunity timely (serviceGraph_barrierOrdered setup
            keepsReveals) profile (horizon - (count + 1)) middle responder middleTrace middleSafe.1
          middleConsistent middleFrontiers middleAllocated response positive
        intro owner
        by_cases same : owner = responder
        · subst owner
          exact ownerPacketFacts_respond middle responder response
            (settledFacts_history (serviceInitialLaw setup mode) horizon scheduler middleTrace)
            (middleFacts responder).1 (middleFacts responder).2.1
            (middleFacts responder).2.2.1 (middleFacts responder).2.2.2 first fresh
            (runtime.prescribedReactivePolicy_inclusion_fits leaks inputs horizon scheduler delay
              bound (initialEq.symm ▸ contract.opportunity) timely
              (serviceGraph_barrierOrdered setup keepsReveals) (horizon - (count + 1)) middle
              responder (initialEq.symm ▸ middleTrace) (profile responder)
              (middleConsistent responder) response positive)
        · exact ownerPacketFacts_respond_other middle owner responder same response
            (settledFacts_history (serviceInitialLaw setup mode) horizon scheduler middleTrace)
            (middleFacts owner).1 (middleFacts owner).2.1 (middleFacts owner).2.2.1
            (middleFacts owner).2.2.2

/-- Authentic sampling of the standard source settled audit is clean throughout
 genuine initialized prescribed execution, using the existing asynchronous service guarantees. -/
theorem source_prescribed_initialized_audit_clear
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : (serviceGraph setup mode).BehavioralProfile)
    (initial : State L setup.context) (supportedInitial : initial ∈ setup.initialLaw.support)
    (count : Nat) (within : count ≤ horizon)
    (next : (serviceApplication setup mode deadline leaks).Execution)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler
      (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks
        owner (profile owner)) count
      (.initial (serviceApplication setup mode deadline leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (who : Player) :
    GameTheory.Enforcement.TerminalAudit.charge
      ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample)
      (some ⟨horizon - count, none, next⟩) who = 0 := by
  let _ := Fintype.ofFinite Player
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (profile owner)
  let start := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  have noMiss := source_prescribed_initialized_no_miss setup leaks horizon scheduler delay bound
    contract timely (serviceGraph_barrierOrdered setup keepsReveals) profile initial
      supportedInitial count within next reached
  have packets := source_prescribed_packetFacts_runRounds setup keepsReveals leaks horizon scheduler
    delay bound contract timely profile initial supportedInitial count within next reached
  have initialSupported : EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
      (setup.eventInputs initial) ∈ (serviceInitialLaw setup mode).support := by
    rw [serviceInitialLaw, PMF.support_map]
    exact ⟨initial, supportedInitial, rfl⟩
  obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
    players 0 (Nat.zero_le horizon) start (by
      rw [ReactiveApplication.roundsFrom, PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨_, initialSupported, ?_⟩
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have horizonEq : horizon - count + count = horizon := Nat.sub_add_cancel within
  have initializedTrace : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨horizon - count + count, none, start⟩) := by
    simpa only [horizonEq, Nat.sub_zero] using startTrace
  obtain ⟨trace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon scheduler players
    (horizon - count) count start next initializedTrace reached
  have inputs := app.stateTraffic_inputs (serviceInitialLaw setup mode) horizon scheduler trace
  change (app.executionTraffic next).map ReactiveApplication.TrafficRecord.envelope =
    next.network.inputs at inputs
  unfold serviceSourceAudit
  rw [runtime.serviceAudit_charge, noMiss who]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply app.sampledTrafficAudit_sound
  · exact authentic _
  · intro record member _
    have emitted : Emitted setup leaks next record.envelope := by
      unfold Emitted
      rw [← inputs]
      exact List.mem_map.mpr ⟨record, member, rfl⟩
    exact ((packets record.envelope.sender).2.2.2 record.envelope rfl emitted).permits


/-- The unchanged standard audit realizes the full joint source-state and net-payoff law;
 the deposit is arbitrary and the original initial-state draw is retained literally. -/
theorem source_prescribed_terminal_settlement_law
    (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode} (keepsReveals : mode ≠ .concurrentReveals)
    {deadline : (serviceGraph setup mode).EventId → Nat}
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (horizon : Nat) (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (delay bound : (serviceGraph setup mode).EventId → Nat)
    (contract : (serviceRuntime setup mode deadline).AsyncContract leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
    (profile : SourceProgram.BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    setup.initialLaw.bind (fun initial =>
      ((serviceApplication setup mode deadline leaks).runRounds scheduler
        (fun owner => (serviceRuntime setup mode deadline).prescribedReactivePolicy leaks owner
          ((setup.eventGraph.toModeProfile mode (compileEventProfile setup.program profile)) owner))
        horizon (.initial (serviceApplication setup mode deadline leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).bind (fun next =>
        (GameTheory.Enforcement.TerminalAudit.settlement
          (serviceBaseUtility setup mode deadline leaks utility)
          ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks sample) deposit
          (some ⟨0, none, next⟩)).map (fun payoffs =>
            (initial, decodeState? (terminalRefs setup.program) next.application.config.store,
              payoffs)))) =
      setup.initialLaw.bind (fun initial =>
        (SourceProgram.run setup.program profile initial).map
          (fun final => (initial, some final, utility final))) := by
  let _ := Fintype.ofFinite Player
  let runtime := serviceRuntime setup mode deadline
  let app := serviceApplication setup mode deadline leaks
  let compiled := setup.eventGraph.toModeProfile mode (compileEventProfile setup.program profile)
  let players := fun owner => runtime.prescribedReactivePolicy leaks owner (compiled owner)
  let native := fun initial : State L setup.context => app.runRounds scheduler players horizon
    (.initial app (EventGraphRuntime.State.initial (setup.eventInputs initial)))
  have clean : ∀ initial ∈ setup.initialLaw.support, ∀ next ∈ (native initial).support,
      GameTheory.Enforcement.TerminalAudit.settlement
        (serviceBaseUtility setup mode deadline leaks utility)
        (runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup mode deadline leaks sample)
        deposit (some ⟨0, none, next⟩) =
          PMF.pure (fun owner => (decodeState? (terminalRefs setup.program)
            next.application.config.store).elim 0 (fun source => utility source owner)) := by
    intro initial supportedInitial next reached
    have clear := fun owner => source_prescribed_initialized_audit_clear setup keepsReveals
      leaks horizon scheduler delay bound contract timely compiled initial supportedInitial
        horizon (Nat.le_refl horizon) next reached sample authentic owner
    have initialSupported : EventGraphRuntime.State.initial (graph := serviceGraph setup mode)
        (setup.eventInputs initial) ∈ (serviceInitialLaw setup mode).support := by
      rw [serviceInitialLaw, PMF.support_map]
      exact ⟨initial, supportedInitial, rfl⟩
    let start := ReactiveApplication.Execution.initial app
      (EventGraphRuntime.State.initial (setup.eventInputs initial))
    obtain ⟨startTrace⟩ := app.raw_trace_roundsFrom (serviceInitialLaw setup mode) horizon scheduler
      players 0 (Nat.zero_le horizon) start (by
        rw [ReactiveApplication.roundsFrom, PMF.support_bind]
        refine Set.mem_iUnion₂.mpr ⟨_, initialSupported, ?_⟩
        exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    obtain ⟨trace⟩ := app.raw_trace_runRounds (serviceInitialLaw setup mode) horizon scheduler
      players
      0 horizon start next (by simpa only [Nat.zero_add, Nat.sub_zero] using startTrace) reached
    have terminal := contract.completes ⟨0, none, next⟩ trace ⟨rfl, rfl⟩
    rw [GameTheory.Enforcement.TerminalAudit.settlement_clean _ _ _ deposit _ (by
      simpa only [Nat.sub_self] using clear)]
    congr 1
    funext owner
    simp only [serviceBaseUtility, serviceSourceReadout, Option.bind_some, terminal, ↓reduceIte]
  have settled : setup.initialLaw.bind (fun initial =>
      (native initial).bind (fun next =>
        (GameTheory.Enforcement.TerminalAudit.settlement
          (serviceBaseUtility setup mode deadline leaks utility)
          (runtime.serviceAuditObservation leaks)
        (serviceSourceAudit setup mode deadline leaks sample)
          deposit (some ⟨0, none, next⟩)).map (fun payoffs =>
            (initial, decodeState? (terminalRefs setup.program) next.application.config.store,
              payoffs)))) =
      setup.initialLaw.bind (fun initial => (native initial).map (fun next =>
        (initial, decodeState? (terminalRefs setup.program) next.application.config.store,
          fun owner => (decodeState? (terminalRefs setup.program)
            next.application.config.store).elim 0 (fun source => utility source owner)))) := by
    apply bind_congr_on_support
    intro initial supportedInitial
    rw [← PMF.bind_pure_comp]
    apply bind_congr_on_support
    intro next reached
    rw [clean initial supportedInitial next reached, PMF.pure_map]
    rfl
  rw [settled]
  have law := source_prescribed_terminal_joint_law setup keepsReveals leaks horizon scheduler
    delay bound contract timely profile
  have joint := congrArg (fun distribution => distribution.map (fun pair =>
    (pair.1, pair.2, fun owner => pair.2.elim 0 (fun source => utility source owner)))) law
  simpa only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.elim_some, native,
    players, compiled, app, runtime] using joint

end

end Vegas
