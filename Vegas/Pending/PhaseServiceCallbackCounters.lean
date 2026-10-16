/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceCountedQueries
import Vegas.Pending.PhaseSeedUnsentFiber

/-! # The complete exhausted-clock count at genuine phased callbacks -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A genuine active callback has exactly one earlier WAIT per elapsed tick;
its own activation adds no exhaustion record. The count is a function of the
owner's actual input, including repeated current-clock activations. -/
theorem active_wait_count
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (owner : Player)
    (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, some owner, execution⟩))
    (coordinate : PhaseSeedAddress graph)
    (request : execution.application.SeedRequest owner coordinate.1) :
    (waitClocks runtime leaks priority decideLocal seeds.1 coordinate
      execution.environmentRecall).length =
      (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner)).elapsed := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let scheduler := (controller runtime leaks priority decideLocal).family seeds
  let idle := execution.respond app owner ⟨none⟩
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨input, valid, _geometry⟩ :=
    currentTokenPrerequisites_history runtime leaks plan inputs horizon scheduler raw
  obtain ⟨before, _word, chosen, moved, inputEq⟩ :=
    PhaseSeedScheduler.active_informationInput_of_trace runtime leaks menu initial horizon scheduler
      remaining owner execution trace coordinate.1
  have applicationEq : execution.application = before.application := by
    obtain ⟨updated, observed, rfl⟩ := PMF.support_map .. ▸ moved
    obtain ⟨selected, _selected, rfl⟩ := PMF.support_map .. ▸ observed
    rfl
  have beforeValid : before.application.Invariant input := by
    rw [← applicationEq]
    exact valid
  have beforeRequest : before.application.SeedRequest owner coordinate.1 := by
    rw [← applicationEq]
    exact request
  have chosenEq := (PMF.mem_support_pure_iff _ _).mp chosen
  have requested := callback_request runtime leaks priority decideLocal seeds before beforeValid
    ordered coordinate owner beforeRequest chosenEq.symm
  have recalled := (app).environmentStep_environmentRecall before execution (.activate owner) moved
  obtain ⟨idleTrace⟩ := menu.trace_respond initial horizon scheduler remaining execution owner
    ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner
      (execution.recall owner) (execution.observe app owner))
  have idleRecall : idle.environmentRecall = before.environmentRecall ++
      [⟨before.observeEnvironment app, .activate owner⟩] := by
    rw [(app).respond_environmentRecall]
    exact recalled
  have count := recorded_query_wait_count runtime leaks priority decideLocal timed seeds bounds plan
    ordered maximal inputs horizon remaining idle idleTrace coordinate owner request.2.2.2.1
      before.environmentRecall ⟨before.observeEnvironment app, .activate owner⟩ [] idleRecall
        (queryAt runtime leaks before coordinate owner) requested
  have noExtra : waitClocks runtime leaks priority decideLocal seeds.1 coordinate
      idle.environmentRecall = waitClocks runtime leaks priority decideLocal seeds.1 coordinate
        before.environmentRecall := by
    unfold waitClocks
    rw [idleRecall, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_append,
      List.filterMap_append]
    simp only [List.nil_append, ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom,
      requested, ite_true, List.filterMap_cons, reduceCtorEq, ite_false, List.filterMap_nil,
      List.append_nil]
  rw [← noExtra, (app).respond_environmentRecall] at count
  have elapsed : (queryAt runtime leaks before coordinate owner).elapsed =
      (PhaseSeedScheduler.informationInput runtime leaks coordinate.1 owner
        (execution.recall owner) (execution.observe app owner)).elapsed :=
    congrArg (fun value => value.elapsed) inputEq
  exact count.trans elapsed

end Vegas.EventGraphRuntime.PhaseServiceScheduler
