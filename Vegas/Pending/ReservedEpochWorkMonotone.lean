/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReservedEpochProgress
import Interaction.ReactiveServiceRounds

/-! # Remaining semantic work never increases under raw execution -/

noncomputable section

namespace Vegas.EventGraphRuntime.ReservedEpoch

open EventGraph Interaction

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
theorem work_le_of_same_namespace (before after : PhaseRuntimeState graph)
    (same : before.attempt = after.attempt)
    (completed : before.current.native.config.cut.completed ⊆
      after.current.native.config.cut.completed) : workRemaining after ≤ workRemaining before := by
  have remaining := Nat.sub_le_sub_left (Finset.card_le_card completed) graph.order.eventCount
  unfold workRemaining
  rw [same]
  exact Nat.add_le_add_left remaining _

omit [DecidableEq Player] in
private theorem work_le_of_step_facts (before after : PhaseRuntimeState graph)
    (namespaceProgress : before.attempt.generation ≤ after.attempt.generation ∧
      before.attempt.phase ≤ after.attempt.phase)
    (budget : after.SeedBudget)
    (completed : before.attempt = after.attempt →
      before.current.native.config.cut.completed ⊆ after.current.native.config.cut.completed) :
    workRemaining after ≤ workRemaining before := by
  by_cases same : before.attempt = after.attempt
  · exact work_le_of_same_namespace before after same (completed same)
  · exact (work_decreases_of_namespace before after namespaceProgress.2 namespaceProgress.1
      (PhaseRuntimeState.phaseLow_le_count after.phases) budget.generation_le_card same).le

def WorkValid (inputs : graph.Inputs) (state : PhaseRuntimeState graph) : Prop :=
  state.Invariant inputs ∧ state.Ordered ∧ state.SeedBudget

variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
theorem work_valid_invariant (inputs : graph.Inputs) : (app).Invariant (WorkValid inputs) where
  submit state owner material valid :=
    ⟨(phaseApplication_invariant runtime leaks inputs).submit state owner material valid.1,
      (phaseApplication_seedOrder runtime leaks).submit state owner material valid.2.1,
      (phaseApplication_seedBudget runtime leaks).submit state owner material valid.2.2⟩
  handle state message next valid accepted :=
    ⟨(phaseApplication_invariant runtime leaks inputs).handle state message next valid.1 accepted,
      (phaseApplication_seedOrder runtime leaks).handle state message next valid.2.1 accepted,
      (phaseApplication_seedBudget runtime leaks).handle state message next valid.2.2 accepted⟩
  environment state command next valid reached :=
    ⟨(phaseApplication_invariant runtime leaks inputs).environment state command next
        valid.1 reached,
      (phaseApplication_seedOrder runtime leaks).environment state command next valid.2.1 reached,
      (phaseApplication_seedBudget runtime leaks).environment state command next valid.2.2 reached⟩

/-- Arbitrary signed submissions, rejected packets, physical expiry, automatic
drain and checkpoint rollback all respect the same finite work measure. -/
theorem work_step_relation : (app).StepRelation (fun before after =>
    ∀ inputs, WorkValid inputs before → workRemaining after ≤ workRemaining before) where
  refl _ _ _ := le_rfl
  submit state owner material inputs valid := by
    apply work_le_of_step_facts state _
      ((phaseApplication_namespace_progress runtime leaks).submit state owner material valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).submit state owner material valid.2.2)
    intro _same
    exact (state.submit_progress owner material valid.1.active).completed
  handle state message next accepted inputs valid := by
    apply work_le_of_step_facts state next
      ((phaseApplication_namespace_progress runtime leaks).handle state message next accepted
        valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).handle state message next valid.2.2 accepted)
    intro same
    exact (state.handle_progress_of_same_namespace runtime next message valid.1 valid.2.1
      accepted same).completed
  environment state command next reached inputs valid := by
    apply work_le_of_step_facts state next
      ((phaseApplication_namespace_progress runtime leaks).environment state command next reached
        valid.2.1)
      ((phaseApplication_seedBudget runtime leaks).environment state command next valid.2.2 reached)
    intro same
    exact (state.environment_progress_of_same_namespace runtime next command valid.1 valid.2.1
      reached same).completed

theorem work_bounded_invariant (scheduler : (app).Scheduler) (inputs : graph.Inputs)
    (bound : Nat) : (app).ServiceInvariant scheduler (fun execution =>
      WorkValid inputs execution.application ∧ workRemaining execution.application ≤ bound) where
  respond execution owner response valid :=
    ⟨(work_valid_invariant runtime leaks inputs).respond execution owner response valid.1,
      ((work_step_relation runtime leaks).respond execution owner response inputs valid.1).trans
        valid.2⟩
  environment execution next command valid _ reached :=
    ⟨(work_valid_invariant runtime leaks inputs).environmentStep execution next command
        valid.1 reached,
      ((work_step_relation runtime leaks).environmentStep execution next command reached inputs
        valid.1).trans valid.2⟩

theorem runRounds_work_le (scheduler : (app).Scheduler) (players : Player → (app).Policy)
    (count : Nat) (inputs : graph.Inputs) (before after : (app).Execution)
    (valid : WorkValid inputs before.application)
    (reached : after ∈ ((app).runRounds scheduler players count before).support) :
    workRemaining after.application ≤ workRemaining before.application := by
  have retained := (work_bounded_invariant runtime leaks scheduler inputs
    (workRemaining before.application)).runRounds players count before after ⟨valid, le_rfl⟩ reached
  exact retained.2

end Vegas.EventGraphRuntime.ReservedEpoch
