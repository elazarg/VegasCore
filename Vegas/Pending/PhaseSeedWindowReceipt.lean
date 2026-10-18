/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountedRequestResolution
import Vegas.Pending.PhaseSeedServiceTick
import Vegas.Pending.PhaseSeedHorizon
import Vegas.Pending.PhaseCountUniqueness
import Interaction.ReactiveRoundBoundary
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveMonitoring

/-! # Original true service ticks force exact physical acceptance -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An original service tick forces this earlier authorized envelope to be accepted
along every supported completing continuation, with its exact raw graph witness. -/
theorem service_tick_eventually_included (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨count, none, execution⟩))
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (serviceTick : Nat)
    (notPast : execution.application.current.native.clock ≤ entered + serviceTick)
    (inTime : serviceTick < runtime.deadline coordinate.1.event)
    (unclosed : (entered + serviceTick, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (sent : Nat) (message : Message Player (CommitAttemptPacket graph))
    (recorded : (sent, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (service : sent + bound coordinate.1.event < runtime.deadline coordinate.1.event ∨
      (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1) serviceTick) = true) :
    (message.id, true) ∈ next.receipts ∧
    ∃ (used tail : Nat) (prior after : (app).Execution) (native : State graph)
      (ready : prior.application.current.native.config.cut.Ready coordinate.1.event)
      (action : graph.Action coordinate.1.event),
      used + 1 + tail = count ∧
      prior ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players used
          execution).support ∧
      (.include message.id : (app).Command) ∈
        (((controller runtime leaks delay bound priority).family seeds)
          prior.environmentRecall (prior.observeEnvironment app)).support ∧
      after ∈ (prior.environmentStep app (.include message.id)).support ∧
      next ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players tail after).support ∧
      (app).handle prior.application message = some after.application ∧
      EventGraphRuntime.handle runtime prior.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.config ∈ (prior.application.current.native.config.step
        coordinate.1.event ready action).support ∧
      after.application = ({prior.application with
        current := prior.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  obtain ⟨finalTrace⟩ := menu.trace_runRounds initial horizon scheduler players covered 0 count
    execution next (by simpa only [Nat.zero_add] using trace) continued
  have finalRaw := menu.toRawTrace initial horizon scheduler finalTrace
  have completed := terminal_history_complete runtime leaks delay bound priority seeds plan
    ordered maximal inputs horizon enough ⟨0, none, next⟩ finalRaw ⟨rfl, rfl⟩
  have finalLost : ¬ next.application.SeedRequest owner coordinate.1 := by
    intro request
    obtain ⟨phase, installed, _member⟩ := request.2.1
    rw [completed.1] at installed
    cases installed
  obtain ⟨used, tail, prior, middle, resumed, command, length, priorSupported, priorRequest,
      chosen, moved, lost, response, future⟩ :=
    (app).runRounds_environment_boundary scheduler players
      (fun current => current.application.SeedRequest owner coordinate.1)
      (fun current actor action request =>
        respond_request runtime leaks current actor action owner coordinate.1 request)
      count execution next requested continued finalLost
  have usedLe : used ≤ count := by omega
  obtain ⟨priorTrace⟩ := menu.trace_runRounds initial horizon scheduler players covered
    (count - used) used execution prior (by
      simpa only [Nat.sub_add_cancel usedLe] using trace) priorSupported
  obtain ⟨_clockLower, clockUpper, stamp⟩ := service_tick_bounds_request_time runtime leaks
    delay bound priority seeds bounds plan ordered maximal inputs horizon (count - used) players
      used execution prior priorTrace valid phases wordRecall clean priorSupported owner coordinate
      requested priorRequest entered activated started serviceTick notPast inTime unclosed sent
      message recorded service
  have timely : prior.application.current.native.WithinDeadline runtime coordinate.1.event := by
    simp only [State.WithinDeadline, stamp]
    omega
  have invariant := ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks input) players
  have currentValid := invariant.runRounds scheduler used execution prior valid priorSupported
  have raw := menu.toRawTrace initial horizon scheduler priorTrace
  have priorClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) priorTrace
  have priorWords := PhaseSeedScheduler.runRounds_wordRecall runtime leaks scheduler players used
    execution prior wordRecall priorSupported
  have retainedWord := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks scheduler
    players used execution prior wordRecall priorSupported owner coordinate.1
  have authentic := PhaseSeedScheduler.localInput_emission_authentic runtime leaks prior
    coordinate.1 owner priorWords priorClean.1.1
    sent message (retainedWord.subset recorded)
  obtain ⟨commandEq, found, actualHandle, recordedReceipt, native, ready, action,
      accepted, stepped, normalized⟩ := PhaseCount.timely_request_loss_accepts runtime leaks
    plan ordered inputs horizon scheduler ⟨count - used, none, prior⟩ raw owner coordinate.1
      (fun packet member _sender =>
        (PhaseCount.permits_eq_true_iff _ _).mp (priorClean.2 packet member))
      priorRequest timely message authentic.1 authentic.2.1 authentic.2.2.1 authentic.2.2.2
      middle command moved lost
  rw [commandEq] at chosen moved response
  have resumedEq : resumed = middle := (PMF.mem_support_pure_iff _ _).mp response
  subst resumed
  have finalReceipt := ((app).receipt_policyInvariant players (message.id, true)).runRounds
    scheduler tail middle next recordedReceipt future
  exact ⟨finalReceipt, used, tail, prior, middle, native, ready, action, length, priorSupported,
    chosen, moved, future, actualHandle, accepted, stepped, normalized⟩

/-- Every candidate in the original seed window attains actual acceptance of
the envelope emitted at the current callback tick, despite arbitrary later legal
choices and history-adaptive priority. No physical-success predicate is assumed. -/
theorem window_eventually_included (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨count, none, execution⟩))
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (PhaseCount.onePacketMenu runtime leaks bounds).actions who past view)
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (entered : Nat)
    (activated : execution.application.current.native.activatedAt coordinate.1.event = some entered)
    (started : entered ≤ execution.application.current.native.clock)
    (unclosed : (execution.application.current.native.clock, coordinate) ∉
      replayClosed runtime leaks priority seeds.1 execution.environmentRecall)
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : (execution.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (window : InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
      (execution.application.current.native.clock - entered)) :
    (message.id, true) ∈ next.receipts ∧
    ∃ (used tail : Nat) (prior after : (app).Execution) (native : State graph)
      (ready : prior.application.current.native.config.cut.Ready coordinate.1.event)
      (action : graph.Action coordinate.1.event),
      used + 1 + tail = count ∧
      prior ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players used
          execution).support ∧
      (.include message.id : (app).Command) ∈
        (((controller runtime leaks delay bound priority).family seeds)
          prior.environmentRecall (prior.observeEnvironment app)).support ∧
      after ∈ (prior.environmentStep app (.include message.id)).support ∧
      next ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players tail after).support ∧
      (app).handle prior.application message = some after.application ∧
      EventGraphRuntime.handle runtime prior.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.config ∈ (prior.application.current.native.config.step
        coordinate.1.event ready action).support ∧
      after.application = ({prior.application with
        current := prior.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
  classical
  have sum : entered + (execution.application.current.native.clock - entered) =
      execution.application.current.native.clock := by omega
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon
    ((controller runtime leaks delay bound priority).family seeds) trace
  obtain ⟨_accountedInput, accounting, _exhausted⟩ := history_calendar_state runtime leaks
    delay bound priority seeds plan ordered maximal inputs horizon raw
      ⟨count, none, execution⟩ rfl
  have includeAt (tick : Nat)
      (notPast : execution.application.current.native.clock ≤ entered + tick)
      (inTime : tick < runtime.deadline coordinate.1.event)
      (service : execution.application.current.native.clock - entered + bound coordinate.1.event <
          runtime.deadline coordinate.1.event ∨
        (seeds.2 coordinate).2 (Fin.ofNat (clockLimit runtime delay + 1) tick) = true) :
      (message.id, true) ∈ next.receipts ∧
    ∃ (used tail : Nat) (prior after : (app).Execution) (native : State graph)
      (ready : prior.application.current.native.config.cut.Ready coordinate.1.event)
      (action : graph.Action coordinate.1.event),
      used + 1 + tail = count ∧
      prior ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players used
          execution).support ∧
      (.include message.id : (app).Command) ∈
        (((controller runtime leaks delay bound priority).family seeds)
          prior.environmentRecall (prior.observeEnvironment app)).support ∧
      after ∈ (prior.environmentStep app (.include message.id)).support ∧
      next ∈ ((app).runRounds
        ((controller runtime leaks delay bound priority).family seeds) players tail after).support ∧
      (app).handle prior.application message = some after.application ∧
      EventGraphRuntime.handle runtime prior.application.current.native
        ⟨message.id, message.payload.packet.call⟩ = some native ∧
      native.config ∈ (prior.application.current.native.config.step
        coordinate.1.event ready action).support ∧
      after.application = ({prior.application with
        current := prior.application.current.inclusionResult message.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
    exact service_tick_eventually_included runtime leaks delay bound priority seeds bounds plan
      ordered maximal inputs horizon enough players count execution next trace covered valid phases
        wordRecall clean continued owner coordinate requested entered activated started tick notPast
        inTime (future_tick_unclosed runtime leaks delay priority seeds accounting.safe coordinate
          unclosed (entered + tick) notPast)
        (execution.application.current.native.clock - entered) message recorded service
  rcases window with protection | ⟨tick, afterEmission, inTime, coin⟩
  · exact includeAt (execution.application.current.native.clock - entered) (by omega) (by omega)
      (Or.inl protection)
  · exact includeAt tick (by omega) inTime (Or.inr coin)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
