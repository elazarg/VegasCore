/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Game.SourceServiceConformance

/-! # Actual retained states before protected inclusion

The next scheduler instruction determines a complete phase roster. Uniform
retained responses witness every legal environment history and recover its
real typed phase boundary. The result applies independently of the chosen
source strategy and of the history's equilibrium probability.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem rosterBlock_includeLatest
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player)
    (block event : (graph setup).EventId) (owner : Player) (index : Nat)
    (found : (rosterBlock setup rosters block)[index]? = some (.includeLatest event owner)) :
    block = event ∧ (graph setup).actor? event = some owner ∧
      index = (rosters event).length := by
  change ((rosters block).map ServiceInstruction.player ++
    (match (graph setup).actor? block with
    | none => [.sample block]
    | some actor => [.includeLatest block actor]) ++
      List.replicate (block.val + 1) .tick ++ [.expire block])[index]? = _ at found
  simp only [List.append_assoc] at found
  by_cases inside : index < (rosters block).length
  · rw [List.getElem?_append_left (by simpa only [List.length_map] using inside),
      List.getElem?_map] at found
    obtain ⟨_, _, impossible⟩ := Option.map_eq_some_iff.mp found
    cases impossible
  · rw [List.getElem?_append_right (by simp only [List.length_map]; omega)] at found
    simp only [List.length_map] at found
    cases owned : (graph setup).actor? block with
    | none =>
        have member := List.mem_of_getElem? found
        simp only [owned, List.mem_append, List.mem_singleton, List.mem_replicate] at member
        rcases member with impossible | impossible | impossible <;> simp_all
    | some actor =>
        simp only [owned, List.singleton_append] at found
        cases offset : index - (rosters block).length with
        | zero =>
            rw [offset, List.getElem?_cons_zero] at found
            obtain ⟨rfl, rfl⟩ := ServiceInstruction.includeLatest.inj (Option.some.inj found)
            exact ⟨rfl, owned, by omega⟩
        | succ rest =>
            rw [offset, List.getElem?_cons_succ] at found
            have member := List.mem_of_getElem? found
            simp only [List.mem_append, List.mem_replicate, List.mem_singleton] at member
            rcases member with ⟨_, impossible⟩ | impossible <;> cases impossible

/-- The actual protected-inclusion command uniquely determines the preceding
complete source phases and the full activation roster. -/
theorem roster_inclusion_prefix
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player)
    (index : Nat) (event : (graph setup).EventId) (owner : Player)
    (found : (rosterPlan setup rosters)[index]? = some (.includeLatest event owner)) :
    (graph setup).actor? event = some owner ∧
      index = (rosterPlanPrefix setup rosters event.val).length + (rosters event).length ∧
      (rosterPlan setup rosters).take index =
        rosterPlanPrefix setup rosters event.val ++
          (rosters event).map ServiceInstruction.player := by
  obtain ⟨rank, block, offset, selected, located, position⟩ := flatMap_position
    (List.finRange (graph setup).order.eventCount) (rosterBlock setup rosters) index
      (.includeLatest event owner) found
  obtain ⟨blockEq, owned, offsetEq⟩ := rosterBlock_includeLatest setup rosters block event owner
    offset located
  subst block
  have bound := (List.getElem?_eq_some_iff.mp selected).1
  rw [List.getElem?_eq_getElem bound, List.getElem_finRange] at selected
  have rankEq : rank = event.val := congrArg Fin.val (Option.some.inj selected)
  have indexEq : index = (rosterPlanPrefix setup rosters event.val).length +
      (rosters event).length := by
    change index = (rosterPlanPrefix setup rosters rank).length + offset at position
    rw [rankEq, offsetEq] at position
    exact position
  refine ⟨owned, indexEq, ?_⟩
  obtain ⟨after, split⟩ := rosterPlan_split setup rosters event
  rw [indexEq, split, List.append_assoc, List.take_append,
    List.take_of_length_le (by omega), show
      (rosterPlanPrefix setup rosters event.val).length + (rosters event).length -
        (rosterPlanPrefix setup rosters event.val).length = (rosters event).length by omega]
  rw [rosterBlock_of_owner setup rosters event owner owned]
  simp only [List.append_assoc]
  exact congrArg _ (List.take_left' (List.length_map _))

private theorem environment_openable_origin
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (execution next : (application setup leaks).Execution)
    (command : (application setup leaks).Command) (candidate : Handle (graph setup))
    (raw : Raw L)
    (reached : next ∈ (execution.environmentStep (application setup leaks) command).support)
    (opened : next.application.candidates.lookup candidate = .openable raw) :
    execution.application.candidates.lookup candidate = .openable raw := by
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact opened
  | activate who =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨sample, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact opened
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending at opened
      cases found : execution.network.lookup id with
      | none => simpa only [found] using opened
      | some message =>
          rw [found] at opened
          change (((application setup leaks).handle execution.application
            message).getD execution.application).candidates.lookup
              candidate = .openable raw at opened
          cases reactiveAccepted : (application setup leaks).handle execution.application
              message with
          | none => simpa only [reactiveAccepted, Option.getD_none] using opened
          | some state =>
              simp only [reactiveAccepted, Option.getD_some] at opened
              have accepted := reactiveHandle_call reactiveAccepted
              cases packet : message.payload.call with
              | commitment event selected =>
                  rw [packet] at accepted
                  rw [(handle_commitment_tables (runtime setup) _ state message.id event
                    selected accepted).1] at opened
                  exact (CommitmentCandidates.lookup_freeze_openable_iff ..).mp opened
              | opening event handle value | withhold event =>
                  have tables := handle_resolution_tables (runtime setup) _ state _
                    (by intros; simp [packet]) accepted
                  simpa only [tables.2] using opened
              | malformed value => simp only [packet, handle] at accepted; contradiction
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      simpa only [(environmentStep_tables (runtime setup) _ state command changed).2] using opened

variable [Fintype Player]

/-- Every legal retained environment history whose next command is protected
inclusion has the actual completed source boundary and full roster witness.
The current phase is ready and timely; all ordinary runtime invariants hold. -/
theorem sourceService_inclusion_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (idle : control.actor = none)
    (event : (graph setup).EventId) (owner : Player)
    (selected : (rosterPlan setup rosters)[control.execution.environmentRecall.length]? =
      some (.includeLatest event owner)) :
    (graph setup).actor? event = some owner ∧
    ∃ initial ∈ setup.initialLaw.support, ∃ (Γ : SourceCtx Player L)
      (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
      (boundary : (application setup leaks).Execution),
      ServiceBoundary setup leaks rosters initial source refs event.val boundary ∧
      control.execution ∈ ((runtime setup).runInteractionPlan leaks
        (sourceServiceMenu setup leaks bounds rosters).uniformResponses network
        ((rosters event).map ServiceInstruction.player) boundary).support ∧
      control.execution.application.config = boundary.application.config ∧
      control.execution.application.publicView = boundary.application.publicView ∧
      SourceCheckpoint setup source refs event.val control.execution.application.config ∧
      control.execution.application.config.cut.Ready event ∧
      control.execution.application.WithinDeadline (runtime setup) event ∧
      EventGraphRuntime.State.Invariant (graph := graph setup)
        (setup.eventInputs initial) control.execution.application ∧
      control.execution.application.BindingInvariant ∧
      control.execution.InputRecall (application setup leaks) ∧
      control.execution.SerialRecall (application setup leaks) ∧
      control.execution.network.SerialsBeforeNext ∧
      control.execution.network.Satisfies (fun message => (runtime setup).permittedServiceEnvelope
        control.execution.application.publicView control.execution.network.ledger message = true) :=
    by
  let menu := sourceServiceMenu setup leaks bounds rosters
  have lawful : ∀ who past view response,
      response ∈ (menu.uniformResponses who past view).support →
        response ∈ menu.actions who past view :=
    fun who past view response => (menu.uniformResponses_support who past view response).mp
  obtain ⟨owned, _, planPrefix⟩ := roster_inclusion_prefix setup rosters _ event owner selected
  have supported := menu.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) trace
  have account := supported.1
  have reached := supported.2
  rw [idle] at reached
  change control.execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
    (rosterScheduler setup leaks rosters network) menu.uniformResponses
      control.execution.environmentRecall.length).support at reached
  have within : control.execution.environmentRecall.length ≤ (rosterPlan setup rosters).length :=
    by omega
  rw [roster_roundsFrom setup leaks rosters network menu.uniformResponses _ within] at reached
  have factored : control.execution ∈
      (((initialLaw setup).bind fun state =>
        (runtime setup).runInteractionPlan leaks menu.uniformResponses network
          (rosterPlanPrefix setup rosters event.val)
          (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
        (fun before => (runtime setup).runInteractionPlan leaks menu.uniformResponses network
          ((rosters event).map ServiceInstruction.player) before)).support := by
    have equal :
        ((initialLaw setup).bind fun state =>
          (runtime setup).runInteractionPlan leaks menu.uniformResponses network
            (rosterPlanPrefix setup rosters event.val)
            (ReactiveApplication.Execution.initial (application setup leaks) state)).bind
          (fun before => (runtime setup).runInteractionPlan leaks menu.uniformResponses network
            ((rosters event).map ServiceInstruction.player) before) =
        (initialLaw setup).bind fun state =>
          (runtime setup).runInteractionPlan leaks menu.uniformResponses network
            ((rosterPlan setup rosters).take control.execution.environmentRecall.length)
            (ReactiveApplication.Execution.initial (application setup leaks) state) := by
      rw [PMF.bind_bind]
      apply bind_congr_on_support _
      intro state _
      rw [planPrefix]
      exact ((runtime setup).runInteractionPlan_append leaks menu.uniformResponses network
        (rosterPlanPrefix setup rosters event.val)
        ((rosters event).map ServiceInstruction.player)
        (ReactiveApplication.Execution.initial (application setup leaks) state)).symm
    rw [equal]
    exact reached
  obtain ⟨prior, before, reachedWindow⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ factored)
  obtain ⟨initial, initialSupport, _, _, _, Γ, names, remaining, remainingProfile, source,
      refs, embedding, refsBefore, _, _, _, _, _, _, _, _, checkpoint⟩ :=
    initialized_sourceService_prefix_support setup leaks bounds values capacity rosters
      opportunities menu.uniformResponses
      (fun who past view response member =>
        (menu.uniformResponses_support who past view response).mp member)
      network (failureProfile setup.program) event.val event.isLt.le prior before
  have beforeTraffic := initialized_sourceService_prefix_conformance bounds values capacity
    opportunities menu.uniformResponses lawful network event.val event.isLt.le prior before
  have boundaryTraffic := beforeTraffic
  obtain ⟨config, publicEq⟩ := (runtime setup).player_window_application leaks menu.uniformResponses
    network (rosters event) prior control.execution reachedWindow
  obtain ⟨validState, validBinding, recalled, serialRecall, serials⟩ := checkpoint.run_core
    menu.uniformResponses network ((rosters event).map ServiceInstruction.player)
      control.execution reachedWindow
  refine ⟨owned, initial, initialSupport, Γ, source, refs, prior, checkpoint,
    reachedWindow, config, publicEq, config.symm ▸ checkpoint.toSourceCheckpoint,
    ?_, ?_, validState, validBinding, recalled, serialRecall, serials, ?_⟩
  · rw [config]
    exact checkpoint.ready event rfl
  · have timely := checkpoint.timely event rfl (by rw [owned]; rfl)
    have clock : control.execution.application.clock = prior.application.clock :=
      congrArg PublicView.clock publicEq
    have activated : control.execution.application.activatedAt = prior.application.activatedAt :=
      congrArg PublicView.activatedAt publicEq
    unfold EventGraphRuntime.State.WithinDeadline at timely ⊢
    rw [activated, clock]
    exact timely
  · cases node : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
        have actor := congrArg EventGraph.EventCode.actor codeEq
        rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actor
        change (graph setup).actor? event = none at actor
        rw [owned] at actor
        cases actor
    | bind actor payload outputEq codeEq =>
        have ownership : (graph setup).actor? event = some actor := by
          have actual := congrArg EventGraph.EventCode.actor codeEq
          rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actual
          exact actual
        exact (checkpoint.binding_prefix_conformance bounds menu.uniformResponses lawful network
          event rfl actor payload outputEq codeEq node ownership boundaryTraffic
          (rosters event) control.execution reachedWindow).1
    | resolve actor payload binding checks outputEq codeEq =>
        have ownership : (graph setup).actor? event = some actor := by
          have actual := congrArg EventGraph.EventCode.actor codeEq
          rw [EventGraph.EventCode.actor_cast outputEq ((graph setup).nodes event)] at actual
          exact actual
        exact (bounds.compiled_resolution_window_conformance (runtime setup) leaks
          menu.uniformResponses
          (fun who past view response supported =>
            sourceServiceMenu_in_compiled setup leaks bounds rosters who past view
              (lawful who past view response supported)) network (rosters event)
          actor event payload binding checks outputEq codeEq node prior control.execution
          checkpoint.binding checkpoint.recall
          (soleReady_of_ready setup prior.application (checkpoint.ready event rfl))
          (checkpoint.ready event rfl)
          (checkpoint.timely event rfl (by rw [ownership]; rfl))
          (fun _ => checkpoint.accounted actor)
          ((runtime setup).service_published_conformance leaks prior checkpoint.published)
          boundaryTraffic reachedWindow).1

/-- Before every actual protected binding inclusion, the current canonical
candidate already contains an admitted typed value. This includes arbitrary
earlier submission times and silent rosters. -/
theorem sourceService_inclusion_binding_candidate
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (control : (application setup leaks).Control)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (idle : control.actor = none)
    (event : (graph setup).EventId) (owner : Player)
    (selected : (rosterPlan setup rosters)[control.execution.environmentRecall.length]? =
      some (.includeLatest event owner))
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq) :
    ∃ value ∈ bounds.typedValues payload,
      control.execution.application.candidates.lookup
        (owner, .prepared (control.execution.application.publicView.bindingCount owner)) =
          .openable ⟨payload, value⟩ := by
  let app := application setup leaks
  let menu := sourceServiceMenu setup leaks bounds rosters
  obtain ⟨owned, initial, _, Γ, source, refs, boundary, checkpoint, reached,
      _, publicEq, _⟩ := sourceService_inclusion_boundary setup leaks bounds values capacity
    rosters opportunities network control trace idle event owner selected
  let serial := boundary.application.publicView.bindingCount owner
  obtain ⟨slot, fresh, unused, vacant⟩ := checkpoint.binding_resources event rfl owner
  obtain ⟨final, included⟩ := ((runtime setup).interactionStep leaks menu.uniformResponses network
    (.includeLatest event owner) control.execution).support_nonempty
  have whole : final ∈ ((runtime setup).runInteractionPlan leaks menu.uniformResponses network
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner])
        boundary).support := by
    rw [(runtime setup).runInteractionPlan_append]
    rw [PMF.support_bind]
    apply Set.mem_iUnion₂.mpr ⟨control.execution, reached, ?_⟩
    simpa only [runInteractionPlan, PMF.bind_pure] using included
  obtain ⟨before, immediate, value, admitted, beforeApp, _, _, _, beforeSerials,
      immediateSupport, finalApp, _⟩ := sourceService_binding_roster_support setup leaks bounds
    rosters values menu.uniformResponses
      (fun who past view response => (menu.uniformResponses_support who past view response).mp)
      network owner event payload outputEq codeEq node owned serial
      (checkpoint.binding_capacity bounds capacity event rfl owner) (rosters event)
      boundary final (checkpoint.ready event rfl) slot fresh checkpoint.published
      checkpoint.serials (checkpoint.unsent owner event (Nat.le_refl _))
      (opportunities event owner (binding_actor setup event owner payload outputEq))
      (by rw [checkpoint.response_offset event rfl owner]) whole
  have beforeFresh : before.application.candidates.lookup (owner, .prepared serial) = .fresh := by
    rw [beforeApp]
    exact fresh
  have state := (runtime setup).reactiveBinding_reserved_state leaks before owner event payload
    outputEq codeEq node (.success value) serial
    (by rw [beforeApp]; exact checkpoint.ready event rfl)
    (by rw [beforeApp]; exact checkpoint.timely event rfl (by rw [owned]; rfl))
    beforeFresh (by rw [beforeApp]; exact vacant) (by rw [beforeApp]; exact unused)
    beforeSerials menu.uniformResponses network immediate immediateSupport
  have finalOpen : final.application.candidates.lookup (owner, .prepared serial) =
      .openable ⟨payload, value⟩ := by
    rw [finalApp, state.2.2,
      (runtime setup).reactiveBinding_candidate_lookup leaks before owner event payload
        (.success value) serial beforeFresh, ite_eq_left rfl]
    simp only [State.candidateOfValue, ite_true]
  have currentOpen := environment_openable_origin setup leaks control.execution final
    ((runtime setup).reactiveLatest leaks event owner (control.execution.observeEnvironment app))
    (owner, .prepared serial) ⟨payload, value⟩
    (by
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at included
      have noActor : ((runtime setup).reactiveLatest leaks event owner
          (control.execution.observeEnvironment app)).actor? app = none := by
        unfold reactiveLatest
        split <;> rfl
      change final ∈ (app.dispatch menu.uniformResponses _ control.execution).support at included
      unfold ReactiveApplication.dispatch at included
      rw [noActor] at included
      change final ∈ ((control.execution.environmentStep app _).bind PMF.pure).support
        at included
      simpa only [PMF.bind_pure] using included)
    finalOpen
  refine ⟨value, admitted, ?_⟩
  simpa only [serial, congrArg (fun view : PublicView (graph setup) => view.bindingCount owner)
    publicEq] using currentOpen

end Vegas
