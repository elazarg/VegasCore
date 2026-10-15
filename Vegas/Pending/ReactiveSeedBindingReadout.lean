/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveSeedCompletion
import Vegas.Pending.ReactiveBinding
import Vegas.Pending.ReactiveEventStability
import Vegas.Pending.EventValueSwap

/-! # Physical binding readout at event-local resolution commands -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- Actual acceptance reads the immutable candidate's binding result into the
selected graph output, including failed and wrongly typed candidates. -/
theorem handle_commitment_config_result
    (state next : State graph) (id : MessageId Player)
    (event : graph.EventId) (candidate : Handle graph) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (accepted : handle runtime state ⟨id, .commitment event candidate⟩ = some next) :
    ∃ ready : state.config.cut.Ready event,
      next.config = state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) (state.bindingResult candidate payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (state.bindingResult candidate payload)) := by
  obtain ⟨ready, timely, actualOwner, actualPayload, actualOutput, actualCode,
      actualNode, sender, owns, vacant, unused⟩ :=
    handle_commitment_conditions runtime state next id event candidate accepted
  have sameOwner := (EventField.binding.inj (outputEq.symm.trans actualOutput)).1
  rw [handle_commitment_eq runtime state id event candidate owner payload outputEq codeEq node
    ready timely (sender.trans sameOwner.symm) (owns.trans sameOwner.symm) vacant unused]
      at accepted
  cases Option.some.inj accepted
  exact ⟨ready, rfl⟩

omit [DecidableEq Player] in
/-- A real first binding completion caused by its expiry writes exactly
failure; stuttering not-ready, unactivated and early commands are excluded
by the actual completion facts. -/
theorem environmentStep_expire_binding_result
    (state next : State graph) (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (unfinished : event ∉ state.config.cut.completed)
    (completed : event ∈ next.config.cut.completed)
    (reached : next ∈ (environmentStep runtime state (.expire event)).support) :
    ∃ ready : state.config.cut.Ready event,
      next.config = state.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  have noStutter : next ≠ state := by
    intro same
    subst next
    exact unfinished completed
  have ready : state.config.cut.Ready event := by
    by_contra notReady
    rw [runtime.environmentStep_expire_of_not_ready state event notReady] at reached
    exact noStutter ((PMF.mem_support_pure_iff _ _).mp reached)
  cases activated : state.activatedAt event with
  | none =>
      rw [runtime.environmentStep_expire_of_not_activated state event ready activated] at reached
      exact False.elim (noStutter ((PMF.mem_support_pure_iff _ _).mp reached))
  | some entered =>
      have due : runtime.deadline event ≤ state.clock - entered := by
        by_contra early
        rw [runtime.environmentStep_expire_of_not_due state event ready entered activated early]
          at reached
        exact noStutter ((PMF.mem_support_pure_iff _ _).mp reached)
      rw [runtime.environmentStep_expire_bind_eq state event ready entered activated due owner
        payload outputEq codeEq node] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨ready, rfl⟩

/-- The physical result of resolving one binding, retaining the actual
accepted envelope and immutable handle when the command includes it. -/
def BindingResolutionReadout
    (execution next : (app).Execution) (event : graph.EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (command : (app).Command) : Prop :=
    (command = .application (.expire event) ∧
      ∃ ready : execution.application.config.cut.Ready event,
        next.application.config = execution.application.config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)))
          (cast (congrArg EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)))) ∨
    ∃ (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
      (candidate : Handle graph) (ready : execution.application.config.cut.Ready event),
      command = .include id ∧ execution.network.lookup id = some message ∧
      message.payload.call = .commitment event candidate ∧
      message.sender = owner ∧
      (app).handle execution.application message = some next.application ∧
      next.application.accepted (.inr event) = some candidate ∧
      next.application.config = execution.application.config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (execution.application.bindingResult candidate payload))
        (cast (congrArg EventField.Value outputEq.symm)
          (execution.application.bindingResult candidate payload))

/-- The actual resolving command determines the physical binding readout:
expiry records failure, whereas an accepted commitment reads its named
immutable candidate. Arbitrary intermediate player policies are retained. -/
theorem resolvingSeedCommand_binding_readout
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (command : (app).Command)
    (resolving : runtime.ResolvingSeedCommand leaks event execution command)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    runtime.BindingResolutionReadout leaks execution next event owner payload
        outputEq command := by
  cases command with
  | wait => cases resolving.1
  | activate who => cases resolving.1
  | application application =>
      cases application with
      | advanceClock => cases resolving.1
      | executeSample addressed => cases resolving.1
      | expire addressed =>
          have same : addressed = event := resolving.1
          subst addressed
          have native : next.application ∈
              (environmentStep runtime execution.application (.expire event)).support := by
            change next ∈ ((execution.environmentStep app (.application (.expire event))).bind
              PMF.pure).support at reached
            rw [PMF.bind_pure] at reached
            obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ reached
            obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ moved
            exact changed
          exact Or.inl ⟨rfl, runtime.environmentStep_expire_binding_result execution.application
            next.application event owner payload outputEq codeEq node unfinished completed native⟩
  | «include» id =>
      change next ∈ ((execution.environmentStep app (.include id)).bind PMF.pure).support
        at reached
      rw [PMF.bind_pure] at reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff] at reached
      subst next
      change event ∈ (execution.includePending app id).application.config.cut.completed at completed
      cases found : execution.network.lookup id with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found] at completed
          exact False.elim (unfinished completed)
      | some message =>
          cases accepted : (app).handle execution.application message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, accepted, Option.getD_none] at completed
              exact False.elim (unfinished completed)
          | some result =>
              have resultEq : (execution.includePending app id).application = result := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, accepted, Option.getD_some]
              rw [resultEq] at completed
              have rawAccepted := reactiveHandle_call accepted
              obtain ⟨addressed, named, ready, action, moved⟩ := handle_config_mem_step runtime
                execution.application result ⟨message.id, message.payload.call⟩ rawAccepted
              have addressEq : addressed = event := by
                have complete := completed
                rw [execution.application.config.step_cut addressed ready action result.config
                  moved, EventOrder.Cut.mem_complete] at complete
                rcases complete with same | earlier
                · exact same.symm
                · exact False.elim (unfinished earlier)
              subst addressed
              cases call : message.payload.call with
              | malformed raw => rw [call] at named; cases named
              | opening addressed candidate raw =>
                  rw [call] at named
                  cases Option.some.inj named
                  simp [handle, call, node] at rawAccepted
              | commitment addressed candidate =>
                  rw [call] at named
                  cases Option.some.inj named
                  have rawBinding : handle runtime execution.application
                      ⟨message.id, .commitment event candidate⟩ = some result := by
                    simpa only [call] using rawAccepted
                  obtain ⟨ready, resultConfig⟩ := runtime.handle_commitment_config_result
                    execution.application result message.id event candidate owner payload outputEq
                      codeEq node rawBinding
                  have association := (handle_commitment_tables runtime execution.application
                    result message.id event candidate rawBinding).2.1
                  have installed : result.accepted (.inr event) = some candidate := by
                    rw [association, Function.update_self]
                  obtain ⟨_, _, actualOwner, actualPayload, actualOutput, _, _, sender,
                      _, _, _⟩ := handle_commitment_conditions runtime execution.application
                        result message.id event candidate rawBinding
                  have ownerEq := (EventField.binding.inj (outputEq.symm.trans actualOutput)).1
                  refine Or.inr ⟨id, message, candidate, ready, rfl, found, call,
                    sender.trans ownerEq.symm, ?_, ?_, ?_⟩
                  · change (app).handle execution.application message =
                      some (execution.includePending app id).application
                    rw [resultEq]
                    exact accepted
                  · change (execution.includePending app id).application.accepted (.inr event) = _
                    rw [resultEq]
                    exact installed
                  · change (execution.includePending app id).application.config = _
                    rw [resultEq]
                    exact resultConfig

/-- The result selected by a resolving command: accepted binding inclusion
uses the submitted typed result; expiry uses failure. -/
def bindingResolutionResult (command : (app).Command) {payload : L.Ty}
    (result : PublicationResult (L.Val payload)) : PublicationResult (L.Val payload) :=
  match command with
  | .include _ => result
  | _ => .failure


end Vegas.EventGraphRuntime

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction EventGraph GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

private theorem reply_resolution_service
    (seed : Seed) (query : CurrentSeedQuery graph) (command : (app).Command)
    (answer : controller.reply seed query = .resolution command) :
    controller.service seed query.input = some command := by
  have select : (match controller.service seed query.input with
      | some selected => LocalSeedReply.resolution selected
      | none => LocalSeedReply.exhausted) = .resolution command →
      controller.service seed query.input = some command := by
    intro selected
    cases serviceEq : controller.service seed query.input with
    | none => simp only [serviceEq, reduceCtorEq] at selected
    | some actual =>
        simp only [serviceEq, LocalSeedReply.resolution.injEq] at selected
        exact congrArg some selected
  unfold reply at answer
  by_cases head : (controller.calendar seed)[query.activationIndex]? = some query.input.elapsed
  · rw [ite_eq_left head] at answer
    by_cases preferred : controller.serviceFirst seed query.input = true
    · rw [ite_eq_left preferred] at answer
      cases serviceEq : controller.service seed query.input with
      | none => simp only [serviceEq, reduceCtorEq] at answer
      | some actual =>
          simp only [serviceEq, LocalSeedReply.resolution.injEq] at answer
          exact congrArg some answer
    · rw [ite_eq_right preferred] at answer
      cases answer
  · rw [ite_eq_right head] at answer
    exact select answer

/-- A newly recorded resolving answer is the command actually issued by the
scheduler, at its current physical event input. -/
theorem step_resolution_of_log
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (memory : LocalSeedMemory runtime leaks Seed RestSeed)
    (execution : (app).Execution) (query : CurrentSeedQuery graph) (command : (app).Command)
    (genuine : controller.domain execution)
    (logged : (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).2.log = memory.log ++ [⟨query, .resolution command⟩]) :
    (controller.step remainder memory execution.environmentRecall
      (execution.observeEnvironment app)).1 = command ∧
      runtime.ResolvingSeedCommand leaks event execution command ∧
      runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app) =
        query.input := by
  classical
  generalize selectedEq : controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app) = selected at logged ⊢
  dsimp only [step] at selectedEq
  split_ifs at selectedEq with ready closed polled
  · rw [← selectedEq] at logged
    have lengths := congrArg List.length logged
    simp only [List.length_append, List.length_singleton] at lengths
    omega
  · rw [← selectedEq] at logged ⊢
    let currentQuery : CurrentSeedQuery graph :=
      ⟨runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app),
        memory.activationIndex⟩
    change (finishReply owner memory _ currentQuery
      (controller.reply memory.localSeed currentQuery)).2.log = _ at logged
    cases answer : controller.reply memory.localSeed currentQuery with
    | activation =>
        simp only [answer, finishReply] at logged
        have entries := (List.singleton_inj.mp (List.append_cancel_left logged))
        have impossible := congrArg LocalSeedEntry.reply entries
        cases impossible
    | exhausted =>
        simp only [answer, finishReply] at logged
        have entries := (List.singleton_inj.mp (List.append_cancel_left logged))
        have impossible := congrArg LocalSeedEntry.reply entries
        cases impossible
    | resolution actual =>
        simp only [answer, finishReply] at logged
        have entries := (List.singleton_inj.mp (List.append_cancel_left logged))
        have queryEq := congrArg LocalSeedEntry.query entries
        have commandEq := congrArg LocalSeedEntry.reply entries
        have actualEq : actual = command := LocalSeedReply.resolution.inj commandEq
        subst actual
        have inputEq : runtime.environmentSeedInput leaks owner event
            (execution.observeEnvironment app) = query.input := congrArg CurrentSeedQuery.input
              queryEq
        refine ⟨?_, ?_, inputEq⟩
        · rfl
        · exact controller.resolves memory.localSeed currentQuery execution command genuine rfl
            ready (reply_resolution_service controller memory.localSeed currentQuery command answer)
  all_goals
    rw [← selectedEq] at logged
    have lengths := congrArg List.length logged
    simp only [List.length_append, List.length_singleton] at lengths
    omega

/-- A genuine first-completing original-seed replay yields its exact physical
binding readout. The reconstructed resolution log is connected to the issued
command and actual accepted envelope, without a success-law premise. -/
theorem replay_resolution_binding_readout
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (initialMemory : LocalSeedMemory runtime leaks Seed RestSeed)
    (players : Player → (app).Policy) (execution next : (app).Execution)
    (payload : L.Ty) (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (query : CurrentSeedQuery graph) (command : (app).Command)
    (genuine : controller.domain execution)
    (unfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder (controller.replay remainder initialMemory
        execution.environmentRecall) execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support)
    (logged : (controller.replay remainder initialMemory next.environmentRecall).log =
      (controller.replay remainder initialMemory execution.environmentRecall).log ++
        [⟨query, .resolution command⟩]) :
    runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app) =
      query.input ∧
      runtime.BindingResolutionReadout leaks execution next event owner payload
        outputEq command := by
  have replayEq : controller.replay remainder initialMemory next.environmentRecall =
      (controller.step remainder (controller.replay remainder initialMemory
        execution.environmentRecall) execution.environmentRecall
          (execution.observeEnvironment app)).2 := by
    rw [(app).dispatch_environmentRecall players _ execution next reached]
    exact controller.replay_snoc remainder initialMemory execution.environmentRecall _
  rw [replayEq] at logged
  obtain ⟨issued, resolving, inputEq⟩ := controller.step_resolution_of_log remainder
    (controller.replay remainder initialMemory execution.environmentRecall) execution query command
      genuine logged
  refine ⟨inputEq, ?_⟩
  apply runtime.resolvingSeedCommand_binding_readout leaks players execution next event owner
    payload outputEq codeEq node command resolving unfinished completed
  simpa only [issued] using reached

end Vegas.EventGraphRuntime.LocalSeedController

end
