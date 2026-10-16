/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceTiming
import Vegas.Pending.PhaseSeedTickExhaustion

/-! # Actual coverage of every earlier ready tick for local service rules -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability
open PhaseSeedCalendar (TickExhaustion replayClosed replayClosed_append_mono)

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

private structure ReadyContext (inputs : graph.Inputs) (execution : (app).Execution) : Prop where
  invariant : execution.application.Invariant inputs
  budget : execution.application.SeedBudget
  frontier : execution.application.Frontier
  live : execution.application.Live
  maximal : execution.application.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample
  quiescent : ∀ event, ¬ execution.application.current.AutomaticReady event

omit [Fintype Player] in
private theorem readyContext_invariant (scheduler : (app).Scheduler)
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) :
    (app).ServiceInvariant scheduler (ReadyContext (runtime := runtime) (leaks := leaks) inputs)
      where
  respond execution who action before := by
    have geometry := (phaseApplication_quiescent runtime leaks ordered).respond execution who
      action ⟨before.frontier, before.maximal, before.quiescent⟩
    have living := (phaseApplication_live runtime leaks).respond execution who action
      ⟨before.frontier, before.live⟩
    exact ⟨(phaseApplication_invariant runtime leaks inputs).respond execution who action
      before.invariant,
      (phaseApplication_seedBudget runtime leaks).respond execution who action before.budget,
      geometry.1, living.2, geometry.2.1, geometry.2.2⟩
  environment execution next command before _ reached := by
    have geometry := (phaseApplication_quiescent runtime leaks ordered).environmentStep execution
      next command ⟨before.frontier, before.maximal, before.quiescent⟩ reached
    have living := (phaseApplication_live runtime leaks).environmentStep execution next command
      ⟨before.frontier, before.live⟩ reached
    exact ⟨(phaseApplication_invariant runtime leaks inputs).environmentStep execution next command
      before.invariant reached,
      (phaseApplication_seedBudget runtime leaks).environmentStep execution next command
        before.budget reached, geometry.1, living.2, geometry.2.1, geometry.2.2⟩

/-- Tick exhaustion is preserved by genuine unrestricted player responses and
all supported commands of an arbitrary history-adaptive local service rule. -/
private theorem tickExhaustion_invariant (priority : RestSeed → List (app).EnvironmentEntry →
  (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (ordered : graph.RevealRelaxedOrdered) (inputs : graph.Inputs) :
    (app).ServiceInvariant ((controller runtime leaks priority decideLocal).family seeds)
      (fun execution => ReadyContext (runtime := runtime) (leaks := leaks) inputs execution ∧
        TickExhaustion runtime leaks priority seeds.1 execution) where
  respond execution who action before := by
    refine ⟨(readyContext_invariant runtime leaks
      ((controller runtime leaks priority decideLocal).family seeds) ordered inputs).respond
        execution who action
      before.1, ?_⟩
    intro coordinate owner request entered activated tick lower earlier
    have clockEq := PhaseSeedCalendar.respond_clock runtime leaks execution before.1.invariant who
      action
    have priorTick : tick < execution.application.current.native.clock := by
      rwa [clockEq] at earlier
    obtain ⟨priorRequest, priorStamp⟩ | fresh := PhaseSeedScheduler.respond_request_origin
      runtime leaks execution who action ordered before.1.invariant before.1.frontier
      before.1.live before.1.maximal before.1.quiescent owner coordinate.1 entered request activated
    · exact before.2 coordinate owner priorRequest entered priorStamp tick lower priorTick
    · omega
  environment execution next command before chosen reached := by
    refine ⟨(readyContext_invariant runtime leaks
      ((controller runtime leaks priority decideLocal).family seeds) ordered inputs).environment
        execution next
      command
      before.1 chosen reached, ?_⟩
    have retain : replayClosed runtime leaks priority seeds.1 execution.environmentRecall ⊆
        replayClosed runtime leaks priority seeds.1 next.environmentRecall := by
      rw [(app).environmentStep_environmentRecall execution next command reached]
      exact replayClosed_append_mono runtime leaks priority seeds.1 _ _
    intro coordinate owner request entered activated tick lower earlier
    have clockEq := PhaseSeedCalendar.environmentStep_clock runtime leaks execution next command
      before.1.invariant reached
    by_cases oldTick : tick < execution.application.current.native.clock
    · obtain ⟨priorRequest, priorStamp⟩ | fresh := PhaseSeedScheduler.environmentStep_request_origin
        runtime leaks execution next command ordered before.1.invariant before.1.frontier
        before.1.live before.1.maximal before.1.quiescent reached owner coordinate.1 entered
        request activated
      · exact retain (before.2 coordinate owner priorRequest entered priorStamp tick lower oldTick)
      · omega
    · have advancing : command = .application .advanceClock := by
        by_contra notAdvance
        have noTick : PhaseSeedCalendar.commandTicks runtime leaks command = 0 := by
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
        simp only [advancing, PhaseSeedCalendar.commandTicks,
          EnvironmentCommand.clockTicks] at clockEq
        omega
      have advanced := reached
      rw [advancing] at advanced
      obtain ⟨priorRequest, _⟩ | fresh := PhaseSeedScheduler.advanceClock_request_origin runtime
        leaks execution next ordered before.1.invariant before.1.frontier before.1.live
        before.1.maximal before.1.quiescent advanced owner coordinate.1 entered request activated
      · have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
        have closed := clockAdvance_request_closed runtime leaks priority decideLocal seeds
          execution before.1.invariant before.1.budget priorRequest
          (chosenEq.symm.trans advancing)
        have addressEq : priorRequest.coordinate before.1.budget = coordinate := Subtype.ext rfl
        rw [addressEq, ← exactTick] at closed
        exact retain closed
      · omega


/-- Every actual history of the phased local driver has queried every earlier
ready tick of every surviving coordinate. No first-delay law, activation bound,
positive probability or completion assumption is used. -/
theorem history_tickExhaustion
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (plan : RuntimePhasePlan graph) (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputLaw : PMF graph.Inputs) (horizon : Nat) {state : (app).ProtocolState}
    (trace : ((app).protocol (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family seeds)).Trace state)
    (current : (app).Control) (stateEq : state = some current) :
    TickExhaustion runtime leaks priority seeds.1 current.execution := by
  let predicate := fun execution : (app).Execution => ∃ inputs,
    ReadyContext (runtime := runtime) (leaks := leaks) inputs execution ∧
      TickExhaustion runtime leaks priority seeds.1 execution
  have invariant : (app).ServiceInvariant
      ((controller runtime leaks priority decideLocal).family seeds) predicate := by
    constructor
    · intro execution who action valid
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (tickExhaustion_invariant runtime leaks priority decideLocal seeds ordered
        inputs).respond execution who action valid⟩
    · intro execution next command valid chosen reached
      obtain ⟨inputs, valid⟩ := valid
      exact ⟨inputs, (tickExhaustion_invariant runtime leaks priority decideLocal seeds ordered
        inputs).environment execution next command valid chosen reached⟩
  have supported := invariant.history (inputLaw.map (PhaseRuntimeState.initial plan)) horizon
    (fun initial member => by
      obtain ⟨inputs, _, rfl⟩ := PMF.support_map .. ▸ member
      have geometry := phaseApplication_initial_quiescent plan ordered maximal inputs
      exact ⟨inputs,
        ⟨(PhaseRuntimeState.initial_invariant plan inputs).1,
          PhaseRuntimeState.initial_seedBudget plan inputs, geometry.1,
          PhaseRuntimeState.initial_live plan inputs, geometry.2.1, geometry.2.2⟩,
        PhaseSeedCalendar.initial_plan_tickExhaustion runtime leaks priority seeds.1 plan inputs⟩)
    trace
  rw [stateEq] at supported
  exact supported.choose_spec.2

end Vegas.EventGraphRuntime.PhaseServiceScheduler
