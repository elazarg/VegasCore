/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseRequestOrigin
import Vegas.Pending.PhaseSeedClosedQueries
import Vegas.Pending.PhaseSeedClockBound

/-! # Every earlier ready tick has an actual nonactivation query -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseSeedCalendar

open EventGraph Interaction GameTheory.Math.Probability

variable {Player RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every tick since a surviving coordinate became ready has already been
drained before the current tick. This retains its original activation anchor. -/
def TickExhaustion
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (execution : (app).Execution) : Prop :=
  ∀ (coordinate : PhaseSeedAddress graph) (owner : Player),
    execution.application.SeedRequest owner coordinate.1 → ∀ entered,
      execution.application.current.native.activatedAt coordinate.1.event = some entered →
        ∀ tick, entered ≤ tick → tick < execution.application.current.native.clock →
          (tick, coordinate) ∈ replayClosed runtime leaks priority rest execution.environmentRecall

/-- Tick exhaustion is preserved by genuine unrestricted player responses and
all supported commands of the history-adaptive tick-draining calendar. -/
theorem tickExhaustion_invariant (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) (origin : Nat) :
    (app).ServiceInvariant ((controller runtime leaks delay bound priority).family seeds)
      (fun execution => ClockAccounting runtime leaks delay priority seeds inputs origin execution ∧
        TickExhaustion runtime leaks priority seeds.1 execution) where
  respond execution who action before := by
    refine ⟨(clockAccounting_invariant runtime leaks delay bound priority seeds ordered inputs
      origin).respond execution who action before.1, ?_⟩
    intro coordinate owner request entered activated tick lower earlier
    have clockEq := respond_clock runtime leaks execution before.1.safe.invariant who action
    have priorTick : tick < execution.application.current.native.clock := by
      rwa [clockEq] at earlier
    obtain ⟨priorRequest, priorStamp⟩ | fresh := PhaseSeedScheduler.respond_request_origin
      runtime leaks execution who action ordered before.1.safe.invariant before.1.frontier
      before.1.live before.1.maximal before.1.quiescent owner coordinate.1 entered request activated
    · exact before.2 coordinate owner priorRequest entered priorStamp tick lower priorTick
    · omega
  environment execution next command before chosen reached := by
    refine ⟨(clockAccounting_invariant runtime leaks delay bound priority seeds ordered inputs
      origin).environment execution next command before.1 chosen reached, ?_⟩
    have retain : replayClosed runtime leaks priority seeds.1 execution.environmentRecall ⊆
        replayClosed runtime leaks priority seeds.1 next.environmentRecall := by
      rw [(app).environmentStep_environmentRecall execution next command reached]
      exact replayClosed_append_mono runtime leaks priority seeds.1 _ _
    intro coordinate owner request entered activated tick lower earlier
    have clockEq := environmentStep_clock runtime leaks execution next command
      before.1.safe.invariant reached
    by_cases oldTick : tick < execution.application.current.native.clock
    · obtain ⟨priorRequest, priorStamp⟩ | fresh := PhaseSeedScheduler.environmentStep_request_origin
        runtime leaks execution next command ordered before.1.safe.invariant before.1.frontier
        before.1.live before.1.maximal before.1.quiescent reached owner coordinate.1 entered
        request activated
      · exact retain (before.2 coordinate owner priorRequest entered priorStamp tick lower oldTick)
      · omega
    · have advancing : command = .application .advanceClock := by
        by_contra notAdvance
        have noTick : commandTicks runtime leaks command = 0 := by
          cases command with
          | wait => rfl
          | activate owner => rfl
          | «include» identifier => rfl
          | application native =>
              cases native with
              | advanceClock => exact (notAdvance rfl).elim
              | executeSample event => rfl
              | expire event => rfl
        rw [noTick, Nat.add_zero] at clockEq
        omega
      have exactTick : tick = execution.application.current.native.clock := by
        simp only [advancing, commandTicks, EnvironmentCommand.clockTicks] at clockEq
        omega
      have advanced := reached
      rw [advancing] at advanced
      obtain ⟨priorRequest, _⟩ | fresh := PhaseSeedScheduler.advanceClock_request_origin runtime
        leaks execution next ordered before.1.safe.invariant before.1.frontier before.1.live
        before.1.maximal before.1.quiescent advanced owner coordinate.1 entered request activated
      · have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
        have closed := clockAdvance_request_closed runtime leaks delay bound priority seeds
          execution before.1.safe.invariant before.1.budget priorRequest
          (chosenEq.symm.trans advancing)
        have addressEq : priorRequest.coordinate before.1.budget = coordinate := Subtype.ext rfl
        rw [addressEq, ← exactTick] at closed
        exact retain closed
      · omega

/-- The normalized initial physical clock is zero, so no earlier tick is due. -/
theorem initial_plan_tickExhaustion
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (rest : RestSeed) (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    TickExhaustion runtime leaks priority rest
      (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan inputs)) := by
  intro coordinate owner request entered activated tick lower earlier
  have clock : (PhaseRuntimeState.initial plan inputs).current.native.clock = 0 :=
    (PhaseRuntimeState.settle_physical _ _ _ _ _).2.2
  change tick < (PhaseRuntimeState.initial plan inputs).current.native.clock at earlier
  omega

/-- The earlier-tick query coverage holds at every actual legal history, with
arbitrary private inputs, arbitrary player choices and the original fixed seeds. -/
theorem history_calendar_state (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat) {state : (app).ProtocolState}
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace state)
    (current : (app).Control) (stateEq : state = some current) :
    ∃ inputs, ClockAccounting runtime leaks delay priority seeds inputs 0 current.execution ∧
      TickExhaustion runtime leaks priority seeds.1 current.execution := by
  let predicate := fun execution : (app).Execution =>
    ∃ inputs, ClockAccounting runtime leaks delay priority seeds inputs 0 execution ∧
      TickExhaustion runtime leaks priority seeds.1 execution
  have invariant : (app).ServiceInvariant
      ((controller runtime leaks delay bound priority).family seeds) predicate := by
    constructor
    · intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (tickExhaustion_invariant runtime leaks delay bound priority seeds ordered
        inputs 0).respond execution who action valid⟩
    · intro execution next command valid chosen reached
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (tickExhaustion_invariant runtime leaks delay bound priority seeds ordered
        inputs 0).environment execution next command valid chosen reached⟩
  have supported := invariant.history (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
    (fun initial member => by
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
      exact ⟨inputs, initial_plan_clockAccounting runtime leaks delay priority seeds plan ordered
        maximal inputs, initial_plan_tickExhaustion runtime leaks priority seeds.1 plan inputs⟩)
    trace
  rw [stateEq] at supported
  exact supported

/-- Every genuine calendar history has queried all earlier ready ticks. -/
theorem history_tickExhaustion (delay bound : graph.EventId → Nat)
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (seeds : RestSeed × (PhaseSeedAddress graph → Seed runtime delay))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat) {state : (app).ProtocolState}
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks delay bound priority).family seeds)).Trace state)
    (current : (app).Control) (stateEq : state = some current) :
    TickExhaustion runtime leaks priority seeds.1 current.execution := by
  obtain ⟨_inputs, _accounting, exhausted⟩ := history_calendar_state runtime leaks delay bound
    priority seeds plan ordered maximal inputLaw horizon trace current stateEq
  exact exhausted

end Vegas.EventGraphRuntime.PhaseSeedCalendar
