/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedAdvanceCharge
import Vegas.Pending.PhaseSeedClockEffects

/-! # Finite clock accounting along genuine seeded executions -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

structure ClockAccounting
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (inputs : graph.Inputs) (origin : Nat)
    (execution : (app).Execution) : Prop where
  safe : TickSafe runtime leaks delay priority seeds inputs execution
  budget : execution.application.SeedBudget
  frontier : execution.application.Frontier
  live : execution.application.Live
  maximal : execution.application.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample
  quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event
  book : ∃ charges : List (ClockCharge runtime),
    execution.application.current.native.clock = origin + charges.length ∧
    (charges.map ClockCharge.ticket).Nodup ∧
    ∀ charge ∈ charges,
      charge.tick < execution.application.current.native.clock ∧
      ClosedCoordinateBound runtime charge.tick charge.entered charge.coordinate.1
        execution.application

theorem initial_clockAccounting
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} (state : PhaseRuntimeState graph)
    (valid : state.Invariant inputs) (budget : state.SeedBudget) (frontier : state.Frontier)
    (live : state.Live) (maximal : state.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (quiescent : ∀ event, ¬ state.current.AutomaticReady event) :
    ClockAccounting runtime leaks delay priority seeds inputs state.current.native.clock
      (ReactiveApplication.Execution.initial app state) := by
  refine ⟨initial_tickSafe runtime leaks delay priority seeds state valid frontier.adjacent,
    budget, frontier, live, maximal, quiescent, [], ?_, List.nodup_nil, ?_⟩
  · rfl
  · simp

/-- Proof-only tickets count genuine physical clock advances. They neither
change scheduler memory nor inspect hidden private inputs or seed values. -/
theorem clockAccounting_invariant
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (ordered : graph.RevealRelaxedOrdered)
    (inputs : graph.Inputs) (origin : Nat) :
    (app).ServiceInvariant ((controller runtime leaks delay bound priority).family seeds)
      (ClockAccounting runtime leaks delay priority seeds inputs origin) where
  respond execution who action before := by
    have geometry := (phaseApplication_quiescent runtime leaks ordered).respond execution who
      action ⟨before.frontier, before.maximal, before.quiescent⟩
    have living := (phaseApplication_live runtime leaks).respond execution who action
      ⟨before.frontier, before.live⟩
    refine ⟨(tickSafe_invariant runtime leaks delay bound priority seeds inputs).respond
      execution who action before.safe,
      (phaseApplication_seedBudget runtime leaks).respond execution who action before.budget,
      geometry.1, living.2, geometry.2.1, geometry.2.2, ?_⟩
    obtain ⟨charges, clock, unique, retained⟩ := before.book
    have clockEq := respond_clock runtime leaks execution before.safe.invariant who action
    refine ⟨charges, clockEq.trans clock, unique, ?_⟩
    intro charge member
    obtain ⟨earlier, closed⟩ := retained charge member
    refine ⟨?_, ClosedCoordinateBound.respond runtime leaks execution who action
      before.safe.invariant before.safe.ordered closed⟩
    rwa [clockEq]
  environment execution next command before chosen reached := by
    have geometry := (phaseApplication_quiescent runtime leaks ordered).environmentStep
      execution next command ⟨before.frontier, before.maximal, before.quiescent⟩ reached
    have living := (phaseApplication_live runtime leaks).environmentStep execution next command
      ⟨before.frontier, before.live⟩ reached
    refine ⟨(tickSafe_invariant runtime leaks delay bound priority seeds inputs).environment
      execution next command before.safe chosen reached,
      (phaseApplication_seedBudget runtime leaks).environmentStep execution next command
        before.budget reached, geometry.1, living.2, geometry.2.1, geometry.2.2, ?_⟩
    obtain ⟨charges, clock, unique, retained⟩ := before.book
    have clockEq := environmentStep_clock runtime leaks execution next command
      before.safe.invariant reached
    have clockLe := (phaseApplication_clock_monotone runtime leaks).environmentStep
      execution next command reached
    have transport : ∀ charge ∈ charges,
        charge.tick < next.application.current.native.clock ∧
        ClosedCoordinateBound runtime charge.tick charge.entered charge.coordinate.1
          next.application := by
      intro charge member
      obtain ⟨earlier, closed⟩ := retained charge member
      exact ⟨earlier.trans_le clockLe, ClosedCoordinateBound.environmentStep runtime leaks
        execution next command before.safe.invariant before.safe.ordered reached closed⟩
    by_cases advance : command = .application .advanceClock
    · have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
      have actualAdvance : (controller runtime leaks delay bound priority).choose seeds
          execution.environmentRecall (execution.observeEnvironment app) =
            .application .advanceClock := chosenEq.symm.trans advance
      obtain ⟨fresh, owner, current, request, activated, _, closed⟩ :=
        advance_charge runtime leaks delay bound priority seeds execution before.safe before.budget
          before.frontier before.live before.quiescent actualAdvance
      have freshTicket : fresh.ticket ∉ charges.map ClockCharge.ticket := by
        intro member
        obtain ⟨old, member, same⟩ := List.mem_map.mp member
        obtain ⟨earlier, oldClosed⟩ := retained old member
        exact ClockCharge.ticket_ne_of_ready_clock runtime old fresh execution.application oldClosed
          current request.1 request.2.2.1 activated earlier same
      have oneTick : next.application.current.native.clock =
          execution.application.current.native.clock + 1 := by
        simpa only [advance, commandTicks, EnvironmentCommand.clockTicks] using clockEq
      refine ⟨charges ++ [fresh], ?_, ?_, ?_⟩
      · simp only [List.length_append, List.length_singleton]
        omega
      · simpa only [List.map_append, List.map_singleton, List.concat_eq_append] using
          List.Nodup.concat freshTicket unique
      · intro charge member
        rcases List.mem_append.mp member with previous | added
        · exact transport charge previous
        · have same : charge = fresh := List.mem_singleton.mp added
          subst charge
          refine ⟨?_, ClosedCoordinateBound.environmentStep runtime leaks execution next command
            before.safe.invariant before.safe.ordered reached closed⟩
          omega
    · have noTick : commandTicks runtime leaks command = 0 := by
        cases command with
        | application native =>
            cases native with
            | advanceClock => exact (advance rfl).elim
            | executeSample event => rfl
            | expire event => rfl
        | wait => rfl
        | activate owner => rfl
        | «include» identifier => rfl
      refine ⟨charges, ?_, unique, transport⟩
      simpa only [noTick, Nat.add_zero, clock] using clockEq

/-- The actual physical clock is bounded by the finite original coordinate
space and deadlines, including every phase reset and unrestricted response. -/
theorem ClockAccounting.clock_le
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} {origin : Nat}
    {execution : (app).Execution}
    (accounting : ClockAccounting runtime leaks delay priority seeds inputs origin execution) :
    execution.application.current.native.clock ≤ origin + Fintype.card (ClockTicket runtime) := by
  obtain ⟨charges, clock, unique, _⟩ := accounting.book
  have bounded := ClockCharge.length_le_tickets runtime charges unique
  omega

end Vegas.EventGraphRuntime.PhaseSeedCalendar
