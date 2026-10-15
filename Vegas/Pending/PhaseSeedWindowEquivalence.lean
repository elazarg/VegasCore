/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedWindowReceipt
import Vegas.Pending.PhaseSeedWindowNecessary
import Interaction.ReactiveReceiptBoundary

/-! # Original coin windows characterize actual accepting receipts -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem fallback_ne_include (view : (app).EnvironmentView) (id : MessageId Player) :
    fallback runtime leaks view ≠ .include id := by
  cases phaseEq : view.application.phase with
  | none => simp [fallback, phaseEq]
  | some current =>
      rcases current with ⟨kind, low, high⟩
      cases kind <;> simp [fallback, phaseEq]
      split <;> simp

theorem inclusionWindow_of_receipt (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat)
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
    (message : Message Player (CommitAttemptPacket graph))
    (recorded : (execution.application.current.native.clock - entered, message) ∈
      (PhaseSeedScheduler.localInput runtime leaks coordinate.1 owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions)
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event)
    (receipted : (message.id, true) ∈ next.receipts) :
    InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
      (execution.application.current.native.clock - entered) := by
  classical
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let scheduler := (controller runtime leaks delay bound priority).family seeds
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have authentic := PhaseSeedScheduler.localInput_emission_authentic runtime leaks execution
    coordinate.1 owner wordRecall clean.1.1
      (execution.application.current.native.clock - entered) message recorded
  have within : execution.application.current.native.WithinDeadline runtime coordinate.1.event := by
    simpa only [State.WithinDeadline, activated] using timely
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, coordinate.1.event⟩ := by
    simpa only [authentic.2.1, authentic.2.2.1] using requested
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan ordered maximal inputs
    horizon scheduler ⟨count, none, execution⟩ trace message authentic.1 coordinate.1.event
      authentic.2.2.2
      packetRequest within
  have unreceipted := (app).pending_identifier_not_receipted initial horizon scheduler
    ⟨count, none, execution⟩ raw message pending true
  obtain ⟨used, tail, prior, middle, length, path, _unreceipted, included, _moved,
      _accepted, _future⟩ := (app).runRounds_accepting_receipt_boundary scheduler players count
        execution next message.id unreceipted continued receipted
  have usedLe : used ≤ count := by omega
  obtain ⟨priorTrace⟩ := menu.trace_runRounds initial horizon scheduler players covered
    (count - used) used execution prior (by
      simpa only [Nat.sub_add_cancel usedLe] using trace) path
  have priorRaw := menu.toRawTrace initial horizon scheduler priorTrace
  have priorValid := (ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks input) players).runRounds scheduler used
      execution prior valid path
  cases selected : selectedAt runtime leaks priority seeds.1 prior with
  | none =>
      have chosen := (PMF.mem_support_pure_iff _ _).mp included
      change (.include message.id : (app).Command) =
        (controller runtime leaks delay bound priority).choose seeds
          prior.environmentRecall (prior.observeEnvironment app) at chosen
      have requestNone : (controller runtime leaks delay bound priority).request seeds.1
          prior.environmentRecall (prior.observeEnvironment app) = none := by
        change (selectedAt runtime leaks priority seeds.1 prior).bind _ = none
        rw [selected]
        rfl
      rw [ReactiveApplication.AddressedScheduler.choose, requestNone] at chosen
      exact (fallback_ne_include runtime leaks (prior.observeEnvironment app) message.id
        chosen.symm).elim
  | some selectedCoordinate =>
      obtain ⟨acting, priorRequest⟩ := selected_request runtime leaks priority seeds.1 prior
        priorValid selectedCoordinate selected
      have chosen := (PMF.mem_support_pure_iff _ _).mp included
      have replyEq : reply runtime leaks delay bound selectedCoordinate
          (seeds.2 selectedCoordinate)
          (queryAt runtime leaks prior selectedCoordinate acting) = .include message.id := by
        rw [choose_eq_reply runtime leaks delay bound priority seeds prior selectedCoordinate
          selected acting priorRequest.2.2.2.1] at chosen
        exact chosen.symm
      obtain ⟨packet, packetInput, _sender, attempt, named, _pending, found, _deadline⟩ :=
        reply_inclusion_packet_of_trace runtime leaks delay bound bounds plan ordered maximal
          inputs horizon scheduler (count - used) prior priorTrace selectedCoordinate acting
            priorRequest (seeds.2 selectedCoordinate) message.id replyEq
      have retainedWord := PhaseSeedScheduler.runRounds_emissions_prefix runtime leaks scheduler
        players used execution prior wordRecall path owner coordinate.1
      have priorWords := PhaseSeedScheduler.runRounds_wordRecall runtime leaks scheduler players
        used execution prior wordRecall path
      have original := PhaseSeedScheduler.localInput_emission_authentic runtime leaks prior
        coordinate.1 owner priorWords
        ((app).history_inputRecall initial horizon scheduler priorRaw)
        (execution.application.current.native.clock - entered) message
        (retainedWord.subset recorded)
      have identifierEq : packet.id = message.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have packetEq : packet = message := (app).input_identifier_injective_history
        initial horizon scheduler ⟨count - used, none, prior⟩ priorRaw packet message
          packetInput original.1 identifierEq
      subst packet
      have attemptEq : selectedCoordinate.1.attempt = coordinate.1.attempt :=
        attempt.symm.trans original.2.2.1
      have eventEq : selectedCoordinate.1.event = coordinate.1.event :=
        Option.some.inj (named.symm.trans original.2.2.2)
      have coordinateEq : selectedCoordinate = coordinate := by
        apply Subtype.ext
        exact congrArg₂ CommitAttemptEvent.mk attemptEq eventEq
      subst selectedCoordinate
      exact (future_inclusion_window runtime leaks delay bound priority seeds bounds initial horizon
        players covered (count - used) used execution prior (by
          simpa only [Nat.sub_add_cancel usedLe] using trace)
        valid phases wordRecall path owner coordinate requested entered activated started timely
        message recorded selected message.id included).2

theorem receipt_iff_inclusionWindow (delay bound : graph.EventId → Nat)
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
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event) :
    (message.id, true) ∈ next.receipts ↔
      InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
        (execution.application.current.native.clock - entered) := by
  constructor
  · exact inclusionWindow_of_receipt runtime leaks delay bound priority seeds bounds plan ordered
      maximal inputs horizon players count execution next trace covered valid phases wordRecall
      clean
      continued owner coordinate requested entered activated started message recorded timely
  · intro window
    exact (window_eventually_included runtime leaks delay bound priority seeds bounds plan ordered
      maximal inputs horizon enough players count execution next trace covered valid phases
      wordRecall
      clean continued owner coordinate requested entered activated started unclosed message recorded
      window).1

open Classical in
theorem receipt_runRounds_law (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (players : Player → (app).Policy) (count : Nat) (execution : (app).Execution)
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
    (timely : execution.application.current.native.clock - entered <
      runtime.deadline coordinate.1.event) :
    (((app).runRounds ((controller runtime leaks delay bound priority).family seeds) players count
      execution).map fun final => decide ((message.id, true) ∈ final.receipts)) =
        PMF.pure (decide (InclusionWindow runtime delay bound coordinate (seeds.2 coordinate)
          (execution.application.current.native.clock - entered))) := by
  classical
  apply pmf_eq_pure_of_support_subset_singleton
  intro outcome supported
  obtain ⟨final, reached, rfl⟩ := PMF.support_map .. ▸ supported
  have same := receipt_iff_inclusionWindow runtime leaks delay bound priority seeds bounds plan
    ordered maximal inputs horizon enough players count execution final trace covered valid phases
    wordRecall clean reached owner coordinate requested entered activated started unclosed message
    recorded timely
  exact Set.mem_singleton_iff.mpr
    (decide_eq_decide.mpr same)

end Vegas.EventGraphRuntime.PhaseSeedCalendar
