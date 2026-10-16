/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceRecordedQuery
import Interaction.ReactiveAddressedTranscriptEntries

/-! # Actual occurrence, activation index and clock of every phased query -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every pair in the actual transcript identifies a real original query with
its exact preceding activation word and surviving readiness anchor. -/
theorem queried_entry
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (seeds : RestSeed × (PhaseSeedAddress graph → LocalSeed))
    (ordered : graph.RevealRelaxedOrdered) (plan : RuntimePhasePlan graph)
    (input : graph.Inputs) (players : Player → (app).Policy) (count : Nat)
    (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds
      ((controller runtime leaks priority decideLocal).family seeds) players count
        (ReactiveApplication.Execution.initial app (PhaseRuntimeState.initial plan input))).support)
    (coordinate : PhaseSeedAddress graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate.1)
    (item : PhaseSeedOperationalInput graph × (app).Command)
    (member : item ∈ (controller runtime leaks priority decideLocal).coordinateTranscriptFrom
      seeds.1 coordinate [] execution.environmentRecall) :
    ∃ before entry after, execution.environmentRecall = before ++ entry :: after ∧
      (controller runtime leaks priority decideLocal).request seeds.1 before entry.beforeView =
        some (coordinate, item.1) ∧ entry.command = item.2 ∧
      item.1.activationClocks = activationTranscript runtime leaks priority decideLocal seeds.1
        coordinate owner before ∧
      entry.beforeView.application.native.activatedAt coordinate.1.event =
        execution.application.current.native.activatedAt coordinate.1.event ∧
      item.1.elapsed ≤ (queryAt runtime leaks execution coordinate owner).elapsed := by
  obtain ⟨before, entry, after, recorded, queried, command⟩ :=
    (ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_mem_iff
      (controller runtime leaks priority decideLocal) seeds.1 coordinate []
        execution.environmentRecall item).mp member
  simp only [List.nil_append] at queried
  have clocks := recorded_query_activationClocks runtime leaks priority decideLocal seeds
    ordered plan input players count execution reached coordinate owner request.2.2.2.1
      before entry after recorded item.1 queried
  obtain ⟨stamp, elapsed⟩ := recorded_query_timing runtime leaks priority decideLocal seeds
    plan input players count execution reached coordinate owner request before entry after
      recorded item.1 queried
  exact ⟨before, entry, after, recorded, queried, command, clocks, stamp, elapsed⟩

end Vegas.EventGraphRuntime.PhaseServiceScheduler
