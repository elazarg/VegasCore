/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseServiceContract
import Interaction.ReactiveServiceRounds

/-! # Native service success derived from the runtime completion contract -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => phaseApplication runtime leaks
local notation "Seeds" => RestSeed × (PhaseSeedAddress graph → LocalSeed)
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds

omit [Fintype Player] in
theorem runRounds_namespace_progress
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (before after : (app).Execution) (ordered : before.application.Ordered)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    before.application.attempt.generation ≤ after.application.attempt.generation ∧
      before.application.attempt.phase ≤ after.application.attempt.phase := by
  let predicate := fun current : (app).Execution => current.application.Ordered ∧
    before.application.attempt.generation ≤ current.application.attempt.generation ∧
    before.application.attempt.phase ≤ current.application.attempt.phase
  have invariant : (app).ServiceInvariant scheduler predicate := by
    constructor
    · intro current who action valid
      have progress := (phaseApplication_namespace_progress runtime leaks).respond
        current who action valid.1
      exact ⟨(phaseApplication_seedOrder runtime leaks).respond current who action valid.1,
        valid.2.1.trans progress.1, valid.2.2.trans progress.2⟩
    · intro current next command valid _selected moved
      have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
        current next command moved valid.1
      exact ⟨(phaseApplication_seedOrder runtime leaks).environmentStep current next command
        valid.1 moved, valid.2.1.trans progress.1, valid.2.2.trans progress.2⟩
  exact (invariant.runRounds players count before after ⟨ordered, le_rfl, le_rfl⟩ reached).2

/-- Every original coordinate resolves when its genuine continuation consumes
the remaining runtime budget. Resolution follows from completion and namespace
monotonicity, including retirement by retry or exhausted restoration. -/
theorem CompletesPlay.resolved_runRounds
    (scheduler : (app).Scheduler)
    (complete : CompletesPlay runtime leaks initial horizon scheduler)
    (players : Player → (app).Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ (menu).actions who past view)
    (count : Nat) (before after : (app).Execution)
    (trace : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨count, none, before⟩))
    (coordinate : CommitAttemptEvent graph)
    (current : coordinate.attempt = before.application.attempt)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    coordinate.Resolved after.application := by
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have ordered : before.application.Ordered :=
    (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler (by
      intro state supported
      obtain ⟨input, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.initial_ordered plan input) raw
  obtain ⟨last⟩ := (menu).trace_runRounds initial horizon scheduler players covered 0 count
    before after (by simpa only [Nat.zero_add] using trace) reached
  have completed := complete ⟨0, none, after⟩
    ((menu).toRawTrace initial horizon scheduler last) ⟨rfl, rfl⟩
  apply CommitAttemptEvent.Resolved.of_step coordinate before.application after.application current
    (runRounds_namespace_progress runtime leaks scheduler players count before after ordered
      reached)
  right
  rw [completed]
  exact Finset.mem_univ _

end Vegas.EventGraphRuntime.PhaseService
