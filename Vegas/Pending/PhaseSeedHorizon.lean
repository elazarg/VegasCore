/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedServiceBook
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveStopping

/-! # A concrete finite horizon completes every all-phase seeded execution -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

variable (delay bound : graph.EventId → Nat)
  (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
  (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))

def serviceHorizon : Nat := (ServiceMark.tickets runtime).card + 1

theorem initial_plan_serviceBook (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : graph.Inputs) :
    ServiceBook runtime leaks delay priority seeds inputs
      (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan inputs)) := by
  refine ⟨initial_plan_clockAccounting runtime leaks delay priority seeds plan ordered maximal
    inputs,
    [], List.nodup_nil, ?_, ?_⟩
  · simp
  · intro _
    rfl

/-- The derived horizon works for every original seed vector, every private
initial input and unrestricted player policies, through all automatic retries. -/
theorem runRounds_complete (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (players : Player → (app).Policy) (inputs : graph.Inputs) (count : Nat)
    (enough : serviceHorizon runtime ≤ count) (final : (app).Execution)
    (reached : final ∈ ((app).runRounds
      ((controller runtime leaks delay bound priority).family seeds) players count
      (ReactiveApplication.Execution.initial app
        (PhaseRuntimeState.initial plan inputs))).support) :
    final.application.phases = [] ∧ final.application.current.native.config.cut.completed =
      Finset.univ := by
  have book :=
    (serviceBook_invariant runtime leaks delay bound priority seeds ordered inputs).runRounds
    players count _ final
    (initial_plan_serviceBook runtime leaks delay priority seeds plan ordered maximal inputs)
    reached
  have complete : final.application.phases = [] := by
    by_contra unfinished
    have bounded := ServiceBook.rounds_le runtime leaks delay priority seeds book unfinished
    have length := (app).runRounds_environmentRecall_length
      ((controller runtime leaks delay bound priority).family seeds) players count _ final reached
    change final.environmentRecall.length = 0 + count at length
    unfold serviceHorizon at enough
    omega
  exact ⟨complete, book.accounting.frontier.terminal complete⟩

/-- Completion holds at every genuine legal terminal protocol history, rather
than only under a chosen player profile or an assumed eventual service law. -/
theorem terminal_history_complete (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (current : (app).Control)
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace (some current))
    (terminal : (app).terminal (some current)) :
    current.execution.application.phases = [] ∧
      current.execution.application.current.native.config.cut.completed = Finset.univ := by
  let predicate := fun execution : (app).Execution =>
    ∃ inputs, ServiceBook runtime leaks delay priority seeds inputs execution
  have invariant : (app).ServiceInvariant
      ((controller runtime leaks delay bound priority).family seeds) predicate := by
    constructor
    · intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (serviceBook_invariant runtime leaks delay bound priority seeds ordered
        inputs).respond execution who action valid⟩
    · intro execution next command valid chosen reached
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (serviceBook_invariant runtime leaks delay bound priority seeds ordered
        inputs).environment execution next command valid chosen reached⟩
  have supported := invariant.history (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
    (fun initial member => by
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨inputs, initial_plan_serviceBook runtime leaks delay priority seeds plan ordered
        maximal inputs⟩) trace
  obtain ⟨inputs, book⟩ := supported
  have complete : current.execution.application.phases = [] := by
    by_contra unfinished
    have bounded := ServiceBook.rounds_le runtime leaks delay priority seeds book unfinished
    have accounted := (app).raw_trace_horizon (inputLaw.map (PhaseRuntimeState.initial plan))
      horizon
      ((controller runtime leaks delay bound priority).family seeds) trace
    have zero := terminal.1
    unfold serviceHorizon at enough
    omega
  exact ⟨complete, book.accounting.frontier.terminal complete⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
