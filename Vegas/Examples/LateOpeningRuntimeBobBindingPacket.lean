/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeBobSuccessSettlement
import Vegas.Examples.LateOpeningRuntimeRetryAudit
import Interaction.ReactiveTrafficContinuation

/-! # Actual accepted first binding envelopes

A successful first binding identifies its actual authenticated Bob-zero
envelope. Full audit freedom at one supported terminal continuation certifies
that envelope's public commitment body. Private response aliases are retained.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeBobBindingPacket

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeReadout
  LateOpeningRuntimeBobBindingService LateOpeningRuntimeBobAudit
open LateOpeningRuntimeBobRawBinding
  (serviced responsePhysical serviced_physical serviced_trace continuation_split
    known_same_information)

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def responseMessage (execution : app.Execution) (material : app.Submission) :
    Message Player app.Payload :=
  ⟨(bob, 0), app.packet (app.submit execution.application bob material) bob
    (execution.network.known bob) material⟩

private theorem binding_absent (physical : app.State)
    (ready : physical.config.cut.Ready bobBindEvent) :
    physical.config.store (.inr bobBindEvent) = none := by
  cases stored : physical.config.store (.inr bobBindEvent) with
  | none => rfl
  | some result =>
      have present : (physical.config.outputs bobBindEvent).isSome := by
        change (physical.config.store (.inr bobBindEvent)).isSome = true
        rw [stored]
        rfl
      exact (ready.1 ((physical.config.output_available bobBindEvent).mp present)).elim

/-- At a ready first binding, every accepted call commits that binding,
independently of its identifier and the earlier raw traffic. -/
theorem binding_call_of_handler (physical next : app.State)
    (ready : physical.config.cut.Ready bobBindEvent) (message : Message Player app.Payload)
    (handled : app.handle physical message = some next) :
    ∃ candidate, message.payload.call = .commitment bobBindEvent candidate := by
  have checked := reactiveApplication_handle_eq_some LateOpeningRuntimeService.runtime leaks
    physical next message handled
  have aliceNotReady : ¬ physical.config.cut.Ready aliceEvent := by
    intro attempted
    exact attempted.1 (ready.2 (by decide : aliceEvent ∈
      nativeGraph.order.predecessors bobBindEvent))
  have answerNotReady : ¬ physical.config.cut.Ready bobRevealEvent := by
    intro attempted
    exact ready.1 (attempted.2 (by decide : bobBindEvent ∈
      nativeGraph.order.predecessors bobRevealEvent))
  have raw := checked.2
  cases call : message.payload.call with
  | malformed rawData => simp [EventGraphRuntime.handle, call] at raw
  | commitment event candidate =>
      rw [call] at raw
      change Fin 3 at event
      fin_cases event
      · change LateOpeningRuntimeService.runtime.handle physical
          ⟨message.id, .commitment aliceEvent candidate⟩ = some next at raw
        have absent : ¬ physical.config.cut.Ready (0 : Fin 3) := aliceNotReady
        simp [EventGraphRuntime.handle, absent] at raw
      · exact ⟨candidate, rfl⟩
      · change LateOpeningRuntimeService.runtime.handle physical
          ⟨message.id, .commitment bobRevealEvent candidate⟩ = some next at raw
        simp [EventGraphRuntime.handle, answerNotReady] at raw
  | opening event candidate data =>
      rw [call] at raw
      change Fin 3 at event
      fin_cases event
      · change LateOpeningRuntimeService.runtime.handle physical
          ⟨message.id, .opening aliceEvent candidate data⟩ = some next at raw
        have absent : ¬ physical.config.cut.Ready (0 : Fin 3) := aliceNotReady
        simp [EventGraphRuntime.handle, absent] at raw
      · change LateOpeningRuntimeService.runtime.handle physical
          ⟨message.id, .opening bobBindEvent candidate data⟩ = some next at raw
        have node : nodeView nativeGraph (1 : Fin 3) =
            .bind bob (.range 0 5) rfl rfl := rfl
        simp [EventGraphRuntime.handle, node] at raw
      · change LateOpeningRuntimeService.runtime.handle physical
          ⟨message.id, .opening bobRevealEvent candidate data⟩ = some next at raw
        simp [EventGraphRuntime.handle, answerNotReady] at raw

theorem accepted_response (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (response : app.Action) (answer : Answer)
    (selected : (serviced execution response).application.config.store (.inr bobBindEvent) =
      some (.success answer)) :
    ∃ material : app.Submission,
      response = ⟨some material⟩ ∧
      (∃ candidate, (responseMessage execution material).payload.call =
        .commitment bobBindEvent candidate) ∧
      (responseMessage execution material).payload.tokenValid = true ∧
      ((bob, 0), true) ∈ (serviced execution response).receipts ∧
      (serviced execution response).network.inputs = execution.network.inputs ++
        [responseMessage execution material] := by
  have absent := binding_absent execution.application ready
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      have impossible : execution.application.config.store (.inr bobBindEvent) =
          some (.success answer) := selected
      rw [absent] at impossible
      cases impossible
  | some material =>
      let submitted := execution.respond app bob ⟨some material⟩
      have configSame := (LateOpeningRuntimeService.runtime.reactive_respond_application leaks
        execution bob ⟨some material⟩).1
      have submittedReady : submitted.application.config.cut.Ready bobBindEvent := by
        rw [configSame]
        exact ready
      have accepted : ∃ next,
          app.handle submitted.application (responseMessage execution material) = some next := by
        cases handled : app.handle submitted.application (responseMessage execution material) with
        | some next => exact ⟨next, rfl⟩
        | none =>
            rw [serviced_physical weight nonnegative execution trace quiet] at selected
            change ((app.handle submitted.application (responseMessage execution material)).getD
              submitted.application).config.store (.inr bobBindEvent) = _ at selected
            rw [handled] at selected
            change submitted.application.config.store (.inr bobBindEvent) = _ at selected
            rw [configSame, absent] at selected
            cases selected
      obtain ⟨next, handled⟩ := accepted
      have checked := reactiveApplication_handle_eq_some LateOpeningRuntimeService.runtime leaks
        submitted.application next (responseMessage execution material) handled
      have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
        weight nonnegative) initial LateOpeningRuntimeService.horizon trace
      have zero := (silent_resources weight nonnegative ⟨14, some bob, execution⟩ trace quiet).1
      have found : submitted.network.lookup (bob, 0) =
          some (responseMessage execution material) := by
        change (execution.network.submit bob
          (app.packet (app.submit execution.application bob material) bob
            (execution.network.known bob) material)).2.lookup (bob, 0) = _
        rw [← zero, serials.lookup_submit]
        rw [zero]
        rfl
      have receipt : ((bob, 0), true) ∈ (serviced execution ⟨some material⟩).receipts := by
        change ((bob, 0), true) ∈ (submitted.includePending app (bob, 0)).receipts
        unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        rw [found]
        change ((bob, 0), true) ∈ submitted.receipts ++
          [((bob, 0),
            (app.handle submitted.application (responseMessage execution material)).isSome)]
        rw [handled]
        simp
      have inputs : (serviced execution ⟨some material⟩).network.inputs =
          execution.network.inputs ++ [responseMessage execution material] := by
        change (submitted.includePending app (bob, 0)).network.inputs = _
        rw [app.includePending_network]
        unfold MessageNetwork.includePending
        rw [found]
        change execution.network.inputs ++ [⟨(bob, execution.network.nextSerial bob),
          app.packet (app.submit execution.application bob material) bob
            (execution.network.known bob) material⟩] = _
        rw [zero]
        rfl
      exact ⟨material, rfl, binding_call_of_handler submitted.application next submittedReady
        (responseMessage execution material) handled, checked.1, receipt, inputs⟩

private theorem permitted_of_zero_charge (control : app.Control)
    (traffic : app.TrafficRecord) (present : traffic ∈ app.executionTraffic control.execution)
    (owner : traffic.envelope.sender = bob)
    (clear : TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some control) bob = 0) :
    (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits
      traffic.envelope = true := by
  by_contra forbidden
  have denied : (LateOpeningRuntimeService.runtime.settledRecord leaks control.execution).permits
      traffic.envelope = false := Bool.eq_false_iff.mpr forbidden
  have charged : 1 ≤ TerminalAudit.charge
      (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (some control) bob :=
    LateOpeningRuntimeService.runtime.serviceAudit_charge_from_record leaks
    (fun record traffic => ((record, traffic.envelope) : SettledEvidence setup .sequential))
    (fun evidence => evidence.2.sender) (fun evidence => evidence.1.permits evidence.2)
    (fun actual => PMF.pure actual) bob 1 (by
      intro actual evidence member _ _
      rw [PMF.toOuterMeasure_pure_apply,
        ite_eq_left (show actual ∈ {observed | evidence ∈ observed} from member)]
      norm_num) control traffic present owner denied
  rw [clear] at charged
  norm_num at charged

theorem responseMessage_same_information (first second : app.Execution)
    (firstRecall : first.InputRecall app) (secondRecall : second.InputRecall app)
    (sameRecall : first.recall bob = second.recall bob)
    (sameView : first.observe app bob = second.observe app bob) (material : app.Submission) :
    responseMessage first material = responseMessage second material := by
  have physicalView : first.application.playerView bob = second.application.playerView bob :=
    congrArg ReactiveApplication.PlayerView.application sameView
  have known := known_same_information first second firstRecall secondRecall sameRecall sameView
  have packets := LateOpeningRuntimeService.runtime.packet_playerView_congr leaks
    first.application second.application bob (first.network.known bob) material physicalView
  unfold responseMessage
  rw [← known]
  exact congrArg (fun packet => (⟨(bob, 0), packet⟩ : Message Player app.Payload)) packets

theorem canonical_packet_clean (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (material : app.Submission) (answer : Answer)
    (selected : (serviced execution ⟨some material⟩).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (packet : responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage) :
    CleanBindings (serviced execution ⟨some material⟩) := by
  obtain ⟨other, responseEq, call, token, receipt, inputs⟩ := accepted_response weight nonnegative
    execution trace quiet ready ⟨some material⟩ answer selected
  have same : material = other := Option.some.inj
    (congrArg ReactiveApplication.Action.transmission responseEq)
  subst other
  have serials := app.serialsBeforeNext_history (LateOpeningRuntimeService.scheduler
    weight nonnegative) initial LateOpeningRuntimeService.horizon trace
  have zero := (silent_resources weight nonnegative ⟨14, some bob, execution⟩ trace quiet).1
  intro message present owner
  rw [inputs, List.mem_append, List.mem_singleton] at present
  rcases present with old | rfl
  · have earlier := serials.inputs message old
    change message.id.2 < execution.network.nextSerial message.id.1 at earlier
    change message.id.1 = bob at owner
    rw [owner, zero] at earlier
    exact (Nat.not_lt_zero _ earlier).elim
  · exact ⟨some ⟨bobBindEvent⟩, congrArg Message.payload packet, receipt⟩

/-- One clean actual terminal certifies the current public envelope. This
statement does not identify the private submission's representation. -/
theorem packet_canonical_of_terminal_clear (execution : app.Execution)
    (trace : (app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, execution⟩))
    (quiet : SilentRecall execution) (ready : execution.application.config.cut.Ready bobBindEvent)
    (response : app.Action) (answer : Answer)
    (selected : (serviced execution response).application.config.store (.inr bobBindEvent) =
      some (.success answer))
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
      players 14 (execution.respond app bob response)).support)
    (clear : TerminalAudit.charge (LateOpeningRuntimeService.runtime.serviceAuditObservation leaks)
      (serviceSourceAudit setup .sequential deadline leaks (fun actual => PMF.pure actual))
        (app.finished final) bob = 0) :
    ∃ material : app.Submission,
      response = ⟨some material⟩ ∧
      responseMessage execution material = LateOpeningRuntimeBobSuffix.bindingMessage := by
  obtain ⟨material, responseEq, ⟨candidate, call⟩, token, receipt, inputs⟩ := accepted_response
    weight nonnegative execution trace quiet ready response answer selected
  subst response
  obtain ⟨servicedTrace⟩ := serviced_trace weight nonnegative execution trace quiet ⟨some material⟩
  have splitReach := reached
  rw [continuation_split weight nonnegative execution trace quiet] at splitReach
  have messagePresent : responseMessage execution material ∈
      (serviced execution ⟨some material⟩).network.inputs := by
    rw [inputs]
    simp
  have recorded := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) servicedTrace
  change (app.executionTraffic (serviced execution ⟨some material⟩)).map
    ReactiveApplication.TrafficRecord.envelope =
      (serviced execution ⟨some material⟩).network.inputs at recorded
  rw [← recorded, List.mem_map] at messagePresent
  obtain ⟨traffic, trafficPresent, envelopeEq⟩ := messagePresent
  have finalPresent := (app.executionTraffic_runRounds (LateOpeningRuntimeService.scheduler
    weight nonnegative) players 13 _ final splitReach).subset trafficPresent
  have permitted := permitted_of_zero_charge ⟨0, none, final⟩ traffic finalPresent
    (by rw [envelopeEq]; rfl) clear
  rw [envelopeEq] at permitted
  obtain ⟨finalTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 13 _ final servicedTrace
      splitReach
  let record := LateOpeningRuntimeService.runtime.settledRecord leaks final
  have permission := (record.permits_eq_true_iff (responseMessage execution material)).mp permitted
  simp only [SettledRecord.Permits, call, Payload.event?] at permission
  have settled : record.Accepts (bob, 0) ∧
      record.SettledContent (responseMessage execution material) := by
    rcases permission with unfinished | accepted
    · have completed := LateOpeningRuntimeService.completes weight nonnegative
        ⟨0, none, final⟩ finalTrace ⟨rfl, rfl⟩
      have done : bobBindEvent ∈ final.application.config.cut.completed := by
        rw [completed]
        exact Finset.mem_univ _
      exact (unfinished ((final.application.config.history_exact bobBindEvent).mpr done)).elim
    · exact accepted
  have content := settled.2
  rw [SettledRecord.SettledContent, call] at content
  have canonical : (responseMessage execution material).payload.evidence = none ∧
      candidate = (bob, .prepared 0) := by
    change (responseMessage execution material).payload.evidence = none ∧
      candidate = (bob, .prepared (record.view.bindingCountBefore bob bobBindEvent)) at content
    rwa [binding_count_before record.view] at content
  obtain ⟨event, named, validToken⟩ :=
    (WitnessedPacket.tokenValid_iff (responseMessage execution material).payload).mp token
  have eventEq : event = bobBindEvent := by
    simpa only [call, Payload.event?, Option.some.injEq] using named.symm
  subst event
  have payload : (responseMessage execution material).payload =
      LateOpeningRuntimeBobSuffix.bindingMessage.payload := by
    calc
      _ = (⟨(responseMessage execution material).payload.call,
          (responseMessage execution material).payload.evidence,
          (responseMessage execution material).payload.token⟩ : WitnessedPacket nativeGraph) := rfl
      _ = _ := by rw [call, canonical.1, canonical.2, validToken]; rfl
  refine ⟨material, rfl, ?_⟩
  exact congrArg (fun packet => (⟨(bob, 0), packet⟩ : Message Player app.Payload)) payload

end Vegas.Examples.LateOpeningRuntimeBobBindingPacket
