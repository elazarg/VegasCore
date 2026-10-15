/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedClockAccounting

/-! # Uniform physical clock bounds at every actual calendar history -/

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

/-- The normalized initial attempt starts with an empty ticket book even when
excluded automatic cells already complete entire descriptors. -/
theorem initial_plan_clockAccounting (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample) (inputs : graph.Inputs) :
    ClockAccounting runtime leaks delay priority seeds inputs 0
      (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan inputs)) := by
  have geometry := phaseApplication_initial_quiescent plan ordered maximal inputs
  have clock : (PhaseRuntimeState.initial plan inputs).current.native.clock = 0 :=
    (PhaseRuntimeState.settle_physical _ _ _ _ _).2.2
  simpa only [clock] using initial_clockAccounting runtime leaks delay priority seeds
    (PhaseRuntimeState.initial plan inputs) (PhaseRuntimeState.initial_invariant plan inputs).1
    (PhaseRuntimeState.initial_seedBudget plan inputs) geometry.1
    (PhaseRuntimeState.initial_live plan inputs) geometry.2.1 geometry.2.2

/-- The bound applies to all legal histories, including off-path responses and
arbitrary private input laws. Original seed values remain immutable parameters. -/
theorem history_clock_le (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat)
    {state : (app).ProtocolState}
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace state)
    (current : (app).Control) (stateEq : state = some current) :
    current.execution.application.current.native.clock ≤ Fintype.card (ClockTicket runtime) := by
  let predicate := fun execution : (app).Execution =>
    ∃ inputs, ClockAccounting runtime leaks delay priority seeds inputs 0 execution
  have invariant : (app).ServiceInvariant
      ((controller runtime leaks delay bound priority).family seeds) predicate := by
    constructor
    · intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (clockAccounting_invariant runtime leaks delay bound priority seeds ordered
        inputs 0).respond execution who action valid⟩
    · intro execution next command valid chosen reached
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (clockAccounting_invariant runtime leaks delay bound priority seeds ordered
        inputs 0).environment execution next command valid chosen reached⟩
  have supported := invariant.history (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
    (fun initial member => by
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨inputs, initial_plan_clockAccounting runtime leaks delay priority seeds plan ordered
        maximal inputs⟩) trace
  rw [stateEq] at supported
  obtain ⟨inputs, accounting⟩ := supported
  simpa only [Nat.zero_add] using
    ClockAccounting.clock_le runtime leaks delay priority seeds accounting

end Vegas.EventGraphRuntime.PhaseSeedCalendar
