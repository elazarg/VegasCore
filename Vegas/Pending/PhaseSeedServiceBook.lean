/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedQueryMarks
import Vegas.Pending.PhaseSeedClockBound
import Vegas.Pending.PhaseSampleProgress
import Interaction.ReactiveServiceRounds

/-! # Finite actual calendar rounds through every phase retry -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] [DecidableEq Player] in
theorem nonempty_of_namespace_progress (before after : PhaseRuntimeState graph)
    (progress : before.attempt.phase ≤ after.attempt.phase) (nonempty : after.phases ≠ []) :
    before.phases ≠ [] := by
  intro empty
  have prior : before.attempt.phase = graph.order.eventCount := by
    simp only [PhaseRuntimeState.attempt, empty, List.head?_nil, Option.map_none, Option.getD_none]
  cases phases : after.phases with
  | nil => exact nonempty phases
  | cons phase remaining =>
      have later : after.attempt.phase = phase.low := by
        simp only [PhaseRuntimeState.attempt, phases, List.head?_cons,
          Option.map_some, Option.getD_some]
      have lower := phase.nonempty
      have upper := phase.bounded
      omega

omit [Fintype Player] in
private theorem command_of_actor (command : (app).Command) (owner : Player)
    (actor : command.actor? app = some owner) : command = .activate owner := by
  cases command with
  | activate actual =>
      have same : actual = owner := Option.some.inj actor
      exact congrArg ReactiveApplication.Command.activate same
  | wait => cases actor
  | «include» identifier => cases actor
  | application native => cases actor

private theorem advance_mark_fresh
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution)
    (old : ServiceMark graph)
    (valid : old.Valid runtime leaks priority rest execution) :
    old.ticket ≠ (ServiceMark.advanced execution.application.current.native.clock).ticket := by
  cases old with
  | queried activation tick coordinate => simp [ServiceMark.ticket]
  | sampled attempt => simp [ServiceMark.ticket]
  | advanced tick =>
      intro same
      have tickEq : tick = execution.application.current.native.clock :=
        Sum.inl.inj (Sum.inr.inj same)
      exact Nat.ne_of_lt valid tickEq

private theorem sample_mark_fresh
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution)
    (old : ServiceMark graph)
    (valid : old.Valid runtime leaks priority rest execution) :
    old.ticket ≠ (ServiceMark.sampled execution.application.attempt).ticket := by
  cases old with
  | queried activation tick coordinate => simp [ServiceMark.ticket]
  | advanced tick => simp [ServiceMark.ticket]
  | sampled attempt =>
      intro same
      exact valid.2.2.2.2 (Sum.inr.inj (Sum.inr.inj same))

/-- Every genuine nonterminal environment command consumes either an unread
query receipt, a fresh clock tick, or the current singleton sample namespace. -/
theorem environment_mark
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} (execution next : (app).Execution)
    (accounting : ClockAccounting runtime leaks delay priority seeds inputs 0 execution)
    (command : (app).Command)
    (chosen : command = (controller runtime leaks delay bound priority).choose seeds
      execution.environmentRecall (execution.observeEnvironment app))
    (reached : next ∈ (execution.environmentStep app command).support)
    (nonempty : execution.application.phases ≠ []) :
    ∃ mark : ServiceMark graph, mark.Valid runtime leaks priority seeds.1 next ∧
      ∀ old : ServiceMark graph, old.Valid runtime leaks priority seeds.1 execution →
        old.ticket ≠ mark.ticket := by
  cases selected : selectedAt runtime leaks priority seeds.1 execution with
  | some coordinate =>
      cases actor : command.actor? app with
      | some owner =>
          have same := command_of_actor runtime leaks command owner actor
          rw [same] at chosen reached
          exact ⟨.queried true execution.application.current.native.clock coordinate,
            activation_mark_valid runtime leaks delay bound priority seeds execution next
              accounting.safe.invariant accounting.safe.ordered coordinate selected owner chosen
              reached,
            fun old valid => activation_mark_fresh runtime leaks delay bound priority seeds
              execution accounting.safe.invariant coordinate selected owner chosen old valid⟩
      | none =>
          exact ⟨.queried false execution.application.current.native.clock coordinate,
            closure_mark_valid runtime leaks priority seeds.1 execution next coordinate selected
              command (by rw [actor]; rfl) reached,
            fun old valid => closure_mark_fresh runtime leaks priority seeds.1 execution coordinate
              selected old valid⟩
  | none =>
      have fallbackEq : command = fallback runtime leaks (execution.observeEnvironment app) := by
        rw [chosen]
        have selectedEq := selected
        unfold selectedAt at selectedEq
        simp only [ReactiveApplication.AddressedScheduler.choose, controller, selectedEq,
          Option.bind_none]
      cases phases : execution.application.phases with
      | nil => exact (nonempty phases).elim
      | cons phase remaining =>
          have head : execution.application.phases.head? = some phase := by
            simp only [phases, List.head?_cons]
          cases kind : phase.kind with
          | commitment | reveal =>
              have same : command = .application .advanceClock := by
                simpa only [fallback, ReactiveApplication.Execution.observeEnvironment,
                  phaseApplication, PhaseRuntimeState.publicView, head, Option.map_some, kind]
                  using fallbackEq
              rw [same] at reached
              have clock := environmentStep_clock runtime leaks execution next
                (.application .advanceClock) accounting.safe.invariant reached
              refine ⟨.advanced execution.application.current.native.clock, ?_,
                fun old valid =>
                  advance_mark_fresh runtime leaks priority seeds.1 execution old valid⟩
              change execution.application.current.native.clock <
                next.application.current.native.clock
              simp only [commandTicks, EnvironmentCommand.clockTicks] at clock
              omega
          | sample =>
              obtain ⟨event, rank, ready, chance⟩ :=
                execution.application.sample_ready_of_live accounting.frontier accounting.live
                  accounting.quiescent phase head kind
              have lowBound : phase.low < graph.order.eventCount :=
                phase.nonempty.trans_le phase.bounded
              have same : command = .application (.executeSample event) := by
                have eventEq : (⟨phase.low, lowBound⟩ : graph.EventId) = event := Fin.ext rank.symm
                simpa only [fallback, ReactiveApplication.Execution.observeEnvironment,
                  phaseApplication, PhaseRuntimeState.publicView, head, Option.map_some, kind,
                  dite_eq_left lowBound, eventEq] using fallbackEq
              rw [same] at reached
              have strict : execution.application.attempt.phase <
                  next.application.attempt.phase := by
                have sampleSupported := reached
                simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp]
                  at sampleSupported
                obtain ⟨state, moved, rfl⟩ := PMF.support_map .. ▸ sampleSupported
                exact execution.application.sample_advances_phase runtime state accounting.frontier
                  phase head kind event rank ready chance moved
              have namespaceProgress :=
                (phaseApplication_namespace_progress runtime leaks).environmentStep execution next
                  (.application (.executeSample event)) reached accounting.safe.ordered
              refine ⟨.sampled execution.application.attempt, ?_,
                fun old valid =>
                  sample_mark_fresh runtime leaks priority seeds.1 execution old valid⟩
              refine ⟨PhaseRuntimeState.phaseLow_le_count _,
                accounting.budget.generation_le_card, namespaceProgress.1, namespaceProgress.2, ?_⟩
              intro equal
              have := congrArg CommitAttemptId.phase equal
              omega

structure ServiceBook
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (inputs : graph.Inputs) (execution : (app).Execution) : Prop where
  accounting : ClockAccounting runtime leaks delay priority seeds inputs 0 execution
  receipts : ∃ marks : List (ServiceMark graph), (marks.map ServiceMark.ticket).Nodup ∧
    (∀ mark ∈ marks, mark.Valid runtime leaks priority seeds.1 execution) ∧
    (execution.application.phases ≠ [] → marks.length = execution.environmentRecall.length)

/-- Receipt counting follows existing actual transitions and responses. At a
still-running phase, every environment entry has a distinct finite ticket. -/
theorem serviceBook_invariant
    (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) :
    (app).ServiceInvariant ((controller runtime leaks delay bound priority).family seeds)
      (ServiceBook runtime leaks delay priority seeds inputs) where
  respond execution who action before := by
    have afterAccounting := (clockAccounting_invariant runtime leaks delay bound priority seeds
      ordered inputs 0).respond execution who action before.accounting
    refine ⟨afterAccounting, ?_⟩
    obtain ⟨marks, unique, valid, counted⟩ := before.receipts
    refine ⟨marks, unique, ?_, ?_⟩
    · intro mark member
      exact ServiceMark.valid_respond runtime leaks priority seeds.1 mark execution who action
        before.accounting.safe.invariant before.accounting.safe.ordered (valid mark member)
    · intro unfinished
      rw [(app).respond_environmentRecall]
      apply counted
      exact nonempty_of_namespace_progress _ _
        ((phaseApplication_namespace_progress runtime leaks).respond execution who action
          before.accounting.safe.ordered).2 unfinished
  environment execution next command before chosen reached := by
    have afterAccounting := (clockAccounting_invariant runtime leaks delay bound priority seeds
      ordered inputs 0).environment execution next command before.accounting chosen reached
    refine ⟨afterAccounting, ?_⟩
    obtain ⟨marks, unique, valid, counted⟩ := before.receipts
    have transport : ∀ mark ∈ marks, mark.Valid runtime leaks priority seeds.1 next := by
      intro mark member
      exact ServiceMark.valid_environment runtime leaks priority seeds.1 mark execution next command
        before.accounting.safe.invariant before.accounting.safe.ordered reached (valid mark member)
    by_cases unfinished : execution.application.phases ≠ []
    · obtain ⟨fresh, freshValid, freshTicket⟩ := environment_mark runtime leaks delay bound priority
        seeds execution next before.accounting command ((PMF.mem_support_pure_iff _ _).mp chosen)
          reached unfinished
      have unused : fresh.ticket ∉ marks.map ServiceMark.ticket := by
        intro member
        obtain ⟨old, oldMember, same⟩ := List.mem_map.mp member
        exact freshTicket old (valid old oldMember) same
      refine ⟨marks ++ [fresh], ?_, ?_, ?_⟩
      · simpa only [List.map_append, List.map_singleton, List.concat_eq_append] using
          List.Nodup.concat unused unique
      · intro mark member
        rcases List.mem_append.mp member with prior | added
        · exact transport mark prior
        · exact (List.mem_singleton.mp added) ▸ freshValid
      · intro _
        rw [(app).environmentStep_environmentRecall execution next command reached]
        simp only [List.length_append, List.length_singleton, counted unfinished]
    · refine ⟨marks, unique, transport, ?_⟩
      intro afterUnfinished
      exact (unfinished (nonempty_of_namespace_progress _ _
        ((phaseApplication_namespace_progress runtime leaks).environmentStep execution next command
          reached before.accounting.safe.ordered).2 afterUnfinished)).elim

/-- A genuine unfinished state admits at most finitely many actual rounds,
regardless of arbitrary callback responses and rollback outcomes. -/
theorem ServiceBook.rounds_le
    (delay : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    {inputs : graph.Inputs} {execution : (app).Execution}
    (book : ServiceBook runtime leaks delay priority seeds inputs execution)
    (unfinished : execution.application.phases ≠ []) :
    execution.environmentRecall.length ≤ (ServiceMark.tickets runtime).card := by
  obtain ⟨marks, unique, valid, counted⟩ := book.receipts
  rw [← counted unfinished]
  exact ServiceMark.length_le_tickets runtime leaks priority book.accounting marks unique valid

end Vegas.EventGraphRuntime.PhaseSeedCalendar
