/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedProtectedClock
import Vegas.Pending.PhaseReadyResolution

/-! # Protected packets physically resolve by inclusion -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Expiry before this ready event's deadline stutters before normalization,
which preserves its genuine request. No scheduler fairness premise is used. -/
theorem expiry_request_before_deadline (runtime : EventGraphRuntime graph)
    (state next : PhaseRuntimeState graph) (owner : Player)
    (coordinate : CommitAttemptEvent graph) (requested : state.SeedRequest owner coordinate)
    (timely : state.current.native.WithinDeadline runtime coordinate.event)
    (reached : next ∈ (state.environment runtime (.expire coordinate.event)).support) :
    next.SeedRequest owner coordinate := by
  classical
  cases activated : state.current.native.activatedAt coordinate.event with
  | none =>
      simp only [State.WithinDeadline, activated] at timely
  | some entered =>
      have notDue : ¬ runtime.deadline coordinate.event ≤ state.current.native.clock - entered :=
        Nat.not_le_of_lt (by simpa only [State.WithinDeadline, activated] using timely)
      have raw := environmentStep_expire_of_not_due runtime state.current.native coordinate.event
        requested.2.2.1 entered activated notDue
      unfold PhaseRuntimeState.environment at reached
      split at reached
      · rw [raw, PMF.pure_map, PMF.mem_support_pure_iff _ _] at reached
        have unchanged : state.current.environmentResult (.expire coordinate.event)
            state.current.native = state.current := by
          simp only [RecoveryState.environmentResult, requested.2.2.1.1, and_false, ite_false]
        simp only [unchanged] at reached
        cases reached
        exact requested.normalize.2
      · cases (PMF.mem_support_pure_iff _ _).mp reached
        exact requested

end PhaseRuntimeState

namespace PhaseSeedCalendar

variable {RestSeed : Type} [Fintype Player]
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- An actual selected activation and its atomic response leave this physical
address open at the same clock. Thus protected service starts from a derived
calendar condition, rather than assuming that the new envelope wins priority. -/
theorem callback_tick_unclosed
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) {inputs : graph.Inputs} (before active : (app).Execution)
    (valid : before.application.Invariant inputs) (owner : Player) (action : (app).Action)
    (coordinate : PhaseSeedAddress graph)
    (selected : selectedAt runtime leaks priority rest before = some coordinate)
    (activated : active ∈ (before.environmentStep app (.activate owner)).support) :
    ((active.respond app owner action).application.current.native.clock, coordinate) ∉
      replayClosed runtime leaks priority rest
        (active.respond app owner action).environmentRecall := by
  have initialOpen := request_unclosed runtime leaks
    (replayClosed runtime leaks priority rest before.environmentRecall)
    (before.observeEnvironment app)
    (priority rest before.environmentRecall (before.observeEnvironment app)) coordinate selected
  change (before.application.current.native.clock, coordinate) ∉
    replayClosed runtime leaks priority rest before.environmentRecall at initialOpen
  have activeValid := (phaseApplication_invariant runtime leaks inputs).environmentStep
    before active (.activate owner) valid activated
  have clock := (respond_clock runtime leaks active activeValid owner action).trans
    (environmentStep_clock runtime leaks before active (.activate owner) valid activated)
  have recorded := (app).environmentStep_environmentRecall before active (.activate owner) activated
  rw [clock]
  change (before.application.current.native.clock, coordinate) ∉ _
  rw [(app).respond_environmentRecall, recorded, replayClosed_snoc]
  simpa only [closeAfter, ReactiveApplication.Command.actor?, Option.isNone_some,
    Bool.false_eq_true, ite_false] using initialOpen

/-- The first physical loss of a protected request is an accepting own-packet
inclusion. It cannot be expiry or collateral phase rollback. -/
theorem protected_first_resolution_includes (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat)
    (players : Player → (app).Policy) (count : Nat) (execution next : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace
        (some ⟨remaining, none, next⟩))
    {input : graph.Inputs} (valid : execution.application.Invariant input)
    (phases : execution.application.Ordered)
    (wordRecall : PhaseSeedScheduler.WordRecall runtime leaks execution)
    (clean : PhaseCount.CountClean runtime leaks execution)
    (continued : next ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
        execution).support)
    (owner : Player) (coordinate : PhaseSeedAddress graph)
    (requested : execution.application.SeedRequest owner coordinate.1)
    (survives : next.application.SeedRequest owner coordinate.1)
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
      bound coordinate.1.event < runtime.deadline coordinate.1.event)
    (after : (app).Execution) (command : (app).Command)
    (moved : after ∈ (next.environmentStep app command).support)
    (lost : ¬ after.application.SeedRequest owner coordinate.1) :
    ∃ (identifier : MessageId Player) (packet : Message Player (CommitAttemptPacket graph))
      (native : State graph)
      (ready : next.application.current.native.config.cut.Ready coordinate.1.event)
      (action : graph.Action coordinate.1.event),
      command = .include identifier ∧ next.network.lookup identifier = some packet ∧
      packet.sender = owner ∧ packet.payload.packet.call.event? graph = some coordinate.1.event ∧
      EventGraphRuntime.handle runtime next.application.current.native
        ⟨packet.id, packet.payload.packet.call⟩ = some native ∧
      native.config ∈ (next.application.current.native.config.step
        coordinate.1.event ready action).support ∧
      after.application = ({next.application with
        current := next.application.current.inclusionResult packet.payload.packet.call native } :
          PhaseRuntimeState graph).normalize := by
  obtain ⟨sameClock, stamp⟩ := protected_request_time runtime leaks delay bound priority seeds
    bounds plan ordered maximal inputs horizon remaining players count execution next trace valid
      phases wordRecall clean continued owner coordinate requested survives entered activated
      started
      unclosed message recorded protection
  have timely : next.application.current.native.WithinDeadline runtime coordinate.1.event := by
    simp only [State.WithinDeadline, stamp, sameClock]
    omega
  have invariant := ReactiveApplication.Invariant.policyInvariant app
    (phaseApplication_invariant runtime leaks input) players
  have nextValid := invariant.runRounds
    ((controller runtime leaks delay bound priority).family seeds) count execution next valid
      continued
  rcases environment_request_or_own_resolution runtime leaks ordered next after nextValid
      owner coordinate.1 survives command moved with retained | expiry | included
  · exact (lost retained).elim
  · have expirySupported := moved
    rw [expiry] at expirySupported
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expirySupported
    obtain ⟨state, stateMoved, rfl⟩ := PMF.support_map .. ▸ expirySupported
    exact (lost (PhaseRuntimeState.expiry_request_before_deadline runtime next.application state
      owner coordinate.1 survives timely stateMoved)).elim
  · exact included

end PhaseSeedCalendar
end Vegas.EventGraphRuntime
