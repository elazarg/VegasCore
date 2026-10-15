/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedProtectedResolution
import Vegas.Pending.PhaseSeedHorizon
import Vegas.Pending.PhaseCountUniqueness
import Interaction.ReactiveRoundBoundary
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveMonitoring

/-! # Every actual completion path includes the original protected envelope -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Genuine bounded calendar completion forces the original protected envelope
to be accepted along the same supported continuation. The actual raw graph
completion is kept even if phase normalization immediately retires its namespace. -/
theorem protected_eventually_included (delay bound : graph.EventId → Nat)
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
    (protection : execution.application.current.native.clock - entered +
      bound coordinate.1.event < runtime.deadline coordinate.1.event) :
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
  obtain ⟨identifier, packet, native, ready, action, commandEq, found, sender, named, accepted,
      stepped, normalized⟩ := protected_first_resolution_includes runtime leaks delay bound priority
    seeds bounds plan ordered maximal inputs horizon (count - used) players used execution prior
      priorTrace valid phases wordRecall clean priorSupported owner coordinate requested
      priorRequest entered activated started unclosed message recorded protection middle command
      moved lost
  have actualHandle : (app).handle prior.application packet = some middle.application := by
    have applicationEq : middle.application =
        ((app).handle prior.application packet).getD prior.application := by
      have included := moved
      rw [commandEq] at included
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
        PMF.mem_support_pure_iff _ _] at included
      cases included
      simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending, found]
    cases handled : (app).handle prior.application packet with
    | none =>
        rw [handled, Option.getD_none] at applicationEq
        exact (lost (applicationEq.symm ▸ priorRequest)).elim
    | some target =>
        rw [handled, Option.getD_some] at applicationEq
        exact congrArg some applicationEq.symm
  have packetCurrent : packet.payload.attempt = prior.application.attempt := by
    by_contra different
    have rejected := prior.application.handle_retired runtime packet different
    change prior.application.handle runtime packet = some middle.application at actualHandle
    rw [rejected] at actualHandle
    cases actualHandle
  have raw := menu.toRawTrace initial horizon scheduler priorTrace
  have priorClean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    initial horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) priorTrace
  have priorWords := PhaseSeedScheduler.runRounds_wordRecall runtime leaks scheduler players used
    execution prior wordRecall priorSupported
  have retainedWord := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks scheduler
    players used execution prior wordRecall priorSupported owner coordinate.1
  have authentic := PhaseSeedScheduler.localInput_emission_authentic runtime leaks prior
    coordinate.1 owner priorWords priorClean.1.1
    (execution.application.current.native.clock - entered) message (retainedWord.subset recorded)
  have envelopes := (app).retained_envelopes_mem_inputs prior
    ((app).history_provenance initial horizon scheduler raw)
    ((app).history_inputRecall initial horizon scheduler raw)
  have packetInput := envelopes.lookup identifier packet found
  have sameEvent : PhaseCount.event? message.payload = PhaseCount.event? packet.payload := by
    simp only [PhaseCount.event?, authentic.2.2.2, named, Option.map_some, authentic.2.2.1,
      packetCurrent, priorRequest.1]
  have same := PhaseCount.Permits.eq_of_same_event
    ((PhaseCount.permits_eq_true_iff _ _).mp (priorClean.2 message authentic.1))
    ((PhaseCount.permits_eq_true_iff _ _).mp (priorClean.2 packet packetInput))
    authentic.1 packetInput
    (fun left leftInput right rightInput same =>
      (app).input_identifier_injective_history initial horizon scheduler
        ⟨count - used, none, prior⟩ raw left right leftInput rightInput same)
    (authentic.2.1.trans sender.symm) sameEvent
  subst packet
  have identifierEq : message.id = identifier := by
    simpa only [decide_eq_true_eq] using List.find?_some found
  rw [← identifierEq] at commandEq found
  rw [commandEq] at chosen moved response
  have resumedEq : resumed = middle := (PMF.mem_support_pure_iff _ _).mp response
  subst resumed
  have recordedReceipt : (message.id, true) ∈ middle.receipts := by
    have included := moved
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
      PMF.mem_support_pure_iff _ _] at included
    have receipts := congrArg ReactiveApplication.Execution.receipts included
    rw [receipts]
    simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
      found, actualHandle, Option.isSome_some, List.mem_append, List.mem_singleton, or_true]
  have finalReceipt := ((app).receipt_policyInvariant players (message.id, true)).runRounds
    scheduler tail middle next recordedReceipt future
  exact ⟨finalReceipt, used, tail, prior, middle, native, ready, action, length, priorSupported,
    chosen, moved, future, actualHandle, accepted, stepped, normalized⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
