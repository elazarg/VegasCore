/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryEntries

/-! # Surviving local transcripts contain only owner activations and waits -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every original queried command of a still requested physical coordinate
is its owner's activation or an actual WAIT. Resolutions cannot survive. -/
theorem queried_activate_or_wait
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (timed : DeadlineExpiry runtime decideLocal)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF graph.Inputs) (horizon remaining : Nat) (execution : (app).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon
      ((controller runtime leaks priority decideLocal).family seeds)).Trace
        (some ⟨remaining, none, execution⟩))
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (item : PhaseSeedOperationalInput graph × (app).Command)
    (member : item ∈ (controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      seeds.1 coordinate [] execution.environmentRecall) :
    item.2 = .activate owner ∨ item.2 = .wait := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let driver := controller runtime leaks priority decideLocal
  let scheduler := driver.family seeds
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have raw := menu.toRawTrace initial horizon scheduler trace
  have commands := ((app).deterministic_transcript_invariant driver.choose seeds).history
    initial horizon (by intro state supported; trivial) raw
  have replies := (driver.command_rectangle_transcript seeds.1 seeds.2 []
    execution.environmentRecall).mp commands
  have replyEq : reply runtime leaks decideLocal coordinate (seeds.2 coordinate) item.1 =
      item.2 := replies.2 coordinate item member
  have idleCase (idle : (item.2.actor? app).isNone = true) : item.2 = .wait := by
    obtain ⟨before, entry, after, recorded, queried, command⟩ :=
      (ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_mem_iff driver seeds.1
        coordinate [] execution.environmentRecall item).mp member
    simp only [List.nil_append] at queried
    have selectedQuery : (PhaseSeedCalendar.selectOpen runtime leaks
        (PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1 before) entry.beforeView
        (priority seeds.1 before entry.beforeView)).bind
          (fun selected => (graph.actor? selected.1.event).map fun acting =>
            (selected, PhaseSeedInput.operational selected.1.attempt
              (PhaseSeedScheduler.localInput runtime leaks selected.1 acting before
                entry.beforeView))) = some (coordinate, item.1) := queried
    obtain ⟨selected, selectedEq, queryEq⟩ := Option.bind_eq_some_iff.mp selectedQuery
    obtain ⟨acting, _actor, pair⟩ := Option.map_eq_some_iff.mp queryEq
    have sameCoordinate : selected = coordinate := congrArg Prod.fst pair
    have actualSelected : PhaseSeedCalendar.selectOpen runtime leaks
        (PhaseSeedCalendar.replayClosed runtime leaks priority seeds.1 before) entry.beforeView
        (priority seeds.1 before entry.beforeView) = some coordinate := by
      simpa only [sameCoordinate] using selectedEq
    have entryIdle : (entry.command.actor? app).isNone = true := by rwa [command]
    have waited := (recorded_wait_of_request runtime leaks priority decideLocal timed seeds
      bounds plan ordered maximal inputs horizon remaining execution trace coordinate owner
        request before entry after recorded actualSelected entryIdle).1
    exact command.symm.trans waited
  cases commandEq : item.2 with
  | activate acting =>
      rw [commandEq] at replyEq
      have same := activation_owner runtime leaks decideLocal coordinate (seeds.2 coordinate)
        item.1 acting owner request.2.2.2.1 replyEq
      exact Or.inl (congrArg ReactiveApplication.Command.activate same)
  | wait => exact Or.inr rfl
  | «include» identifier =>
      exact Or.inr (commandEq.symm.trans (idleCase (by rw [commandEq]; rfl)))
  | application native =>
      exact Or.inr (commandEq.symm.trans (idleCase (by rw [commandEq]; rfl)))

end Vegas.EventGraphRuntime.PhaseServiceScheduler
