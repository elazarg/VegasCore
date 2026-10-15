/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedHorizon
import Interaction.ReactiveServiceMixture

/-! # Original-prior behavioralized calendars complete actual legal histories -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The actual mixed scheduler, rather than a chosen fixed-seed run, completes
every legal terminal history under the same original independent seed prior. -/
theorem mixture_terminal_history_complete (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (Nat × CommitAttemptId) → Nat × CommitAttemptId → Nat)
    (laws : PhaseSeedAddress graph → PMF (Seed runtime delay)) (restLaw : PMF RestSeed)
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat) (enough : serviceHorizon runtime ≤ horizon)
    (current : (app).Control)
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).implementation laws restLaw).scheduler).Trace
        (some current))
    (terminal : (app).terminal (some current)) :
    current.execution.application.phases = [] ∧
      current.execution.application.current.native.config.cut.completed = Finset.univ := by
  let driver := controller runtime leaks delay bound priority
  let initialSeeds := ReactiveApplication.AddressedScheduler.prior laws restLaw
  let predicate := fun seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay) =>
    fun execution : (app).Execution =>
      ∃ inputs, ServiceBook runtime leaks delay priority seeds inputs execution
  have invariant (seeds) : (app).ServiceInvariant (driver.family seeds) (predicate seeds) := by
    constructor
    · intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (serviceBook_invariant runtime leaks delay bound priority seeds ordered
        inputs).respond execution who action valid⟩
    · intro execution next command valid chosen reached
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (serviceBook_invariant runtime leaks delay bound priority seeds ordered
        inputs).environment execution next command valid chosen reached⟩
  have jointInvariant := ReactiveApplication.ServiceInvariant.schedulerMixture app initialSeeds
    driver.family predicate invariant
  have supported := jointInvariant.history (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
    (fun initial member => by
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
      intro seeds _
      exact ⟨inputs, initial_plan_serviceBook runtime leaks delay priority seeds plan ordered
        maximal inputs⟩) trace
  obtain ⟨seeds, seedSupport⟩ := PMF.support_nonempty
    (((driver.implementation laws restLaw).posterior current.execution.environmentRecall))
  obtain ⟨inputs, book⟩ := supported seeds seedSupport
  have complete : current.execution.application.phases = [] := by
    by_contra unfinished
    have bounded := ServiceBook.rounds_le runtime leaks delay priority seeds book unfinished
    have accounted := (app).raw_trace_horizon (inputLaw.map (PhaseRuntimeState.initial plan))
      horizon (driver.implementation laws restLaw).scheduler trace
    have zero := terminal.1
    unfold serviceHorizon at enough
    omega
  exact ⟨complete, book.accounting.frontier.terminal complete⟩

end Vegas.EventGraphRuntime.PhaseSeedCalendar
