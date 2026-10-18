/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReservedEpochRequestProgress
import Vegas.Pending.PhaseRetryCompletion

/-! # Unchanged semantic work fixes the installed phase and completed cut -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def FlatSnapshot (before after : PhaseRuntimeState graph) : Prop :=
  before.attempt = after.attempt ∧ after.phases = before.phases ∧
    after.current.native.config.cut.completed = before.current.native.config.cut.completed

omit [DecidableEq Player] in
private theorem snapshot_of_facts (before after : PhaseRuntimeState graph)
    (progress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (budget : after.SeedBudget)
    (completed : before.attempt = after.attempt →
      before.current.native.config.cut.completed ⊆ after.current.native.config.cut.completed)
    (phases : before.attempt = after.attempt → after.phases = before.phases)
    (flat : workRemaining after = workRemaining before) : FlatSnapshot before after := by
  have same := namespace_eq_of_flat before after progress budget flat
  refine ⟨same, phases same, ?_⟩
  have included := completed same
  symm
  apply Finset.eq_of_subset_of_card_le included
  · have leftBound : before.current.native.config.cut.completed.card ≤ graph.order.eventCount := by
      simpa using Finset.card_le_card (Finset.subset_univ
        before.current.native.config.cut.completed)
    have rightBound : after.current.native.config.cut.completed.card ≤ graph.order.eventCount := by
      simpa using Finset.card_le_card (Finset.subset_univ
        after.current.native.config.cut.completed)
    unfold workRemaining at flat
    rw [same] at flat
    unfold EventGraph.Config.remaining at flat
    omega

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

theorem flat_snapshot_relation : (app).StepRelation (fun before after =>
    ∀ inputs, WorkValid inputs before → workRemaining after = workRemaining before →
      FlatSnapshot before after) where
  refl _ _ _ _ := ⟨rfl, rfl, rfl⟩
  submit state actor material inputs valid flat := by
    apply snapshot_of_facts state _
      ((phaseApplication_namespace_progress runtime leaks).submit state actor material valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).submit state actor material valid.2.2)
      (fun _ => (state.submit_progress actor material valid.1.active).completed)
      (fun _ => rfl) flat
  handle state message next accepted inputs valid flat := by
    apply snapshot_of_facts state next
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).handle state message next valid.2.2 accepted)
      (fun same => (state.handle_progress_of_same_namespace runtime next message valid.1
        valid.2.1 accepted same).completed)
      ((phaseApplication_sameAttempt_phases runtime leaks).handle state message next accepted
        valid.2.1) flat
  environment state command next reached inputs valid flat := by
    apply snapshot_of_facts state next
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).environment state command next valid.2.2 reached)
      (fun same => (state.environment_progress_of_same_namespace runtime next command valid.1
        valid.2.1 reached same).completed)
      ((phaseApplication_sameAttempt_phases runtime leaks).environment state command next reached
        valid.2.1) flat

def SnapshotWatch (inputs : graph.Inputs) (origin : PhaseRuntimeState graph)
    (execution : (app).Execution) : Prop :=
  WorkValid inputs execution.application ∧
    workRemaining execution.application ≤ workRemaining origin ∧
      (workRemaining execution.application = workRemaining origin →
        FlatSnapshot origin execution.application)

theorem snapshot_watch_invariant (scheduler : (app).Scheduler) (inputs : graph.Inputs)
    (origin : PhaseRuntimeState graph) :
    (app).ServiceInvariant scheduler (SnapshotWatch runtime leaks inputs origin) where
  respond execution owner action watched := by
    obtain ⟨valid, bounded, witness⟩ := watched
    have nextValid := (work_valid_invariant runtime leaks inputs).respond
      execution owner action valid
    have decreases := (work_step_relation runtime leaks).respond execution owner action inputs valid
    refine ⟨nextValid, decreases.trans bounded, ?_⟩
    intro flat
    have beforeFlat : workRemaining execution.application = workRemaining origin := by omega
    have stepFlat : workRemaining (execution.respond app owner action).application =
        workRemaining execution.application := by omega
    obtain ⟨same, phases, completed⟩ := witness beforeFlat
    obtain ⟨nextSame, nextPhases, nextCompleted⟩ := (flat_snapshot_relation runtime leaks).respond
      execution owner action inputs valid stepFlat
    exact ⟨same.trans nextSame, nextPhases.trans phases, nextCompleted.trans completed⟩
  environment execution next command watched _ reached := by
    obtain ⟨valid, bounded, witness⟩ := watched
    have nextValid := (work_valid_invariant runtime leaks inputs).environmentStep
      execution next command valid reached
    have decreases := (work_step_relation runtime leaks).environmentStep
      execution next command reached inputs valid
    refine ⟨nextValid, decreases.trans bounded, ?_⟩
    intro flat
    have beforeFlat : workRemaining execution.application = workRemaining origin := by omega
    have stepFlat : workRemaining next.application = workRemaining execution.application := by omega
    obtain ⟨same, phases, completed⟩ := witness beforeFlat
    obtain ⟨nextSame, nextPhases, nextCompleted⟩ :=
      (flat_snapshot_relation runtime leaks).environmentStep execution next command reached
        inputs valid stepFlat
    exact ⟨same.trans nextSame, nextPhases.trans phases, nextCompleted.trans completed⟩

theorem runRounds_flat_snapshot (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (inputs : graph.Inputs) (before after : (app).Execution)
    (valid : WorkValid inputs before.application)
    (reached : after ∈ ((app).runRounds scheduler players count before).support)
    (flat : workRemaining after.application = workRemaining before.application) :
    FlatSnapshot before.application after.application := by
  have watched := (snapshot_watch_invariant runtime leaks scheduler inputs
    before.application).runRounds players count before after
      ⟨valid, le_rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ reached
  exact watched.2.2 flat

end Vegas.EventGraphRuntime.ReservedEpoch
