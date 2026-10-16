/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNamespace

/-! # Strict chronology of physically retired attempt namespaces -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction

/-- Physical retry generations order attempts before their static phase addresses. -/
def CommitAttemptId.Precedes (before after : CommitAttemptId) : Prop :=
  before.generation < after.generation ∨
    before.generation = after.generation ∧ before.phase < after.phase

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- The actual archive is strictly chronological and ends before the live namespace. -/
def RetiredOrdered (state : PhaseRuntimeState graph) : Prop :=
  state.retired.Pairwise (fun before after => before.attempt.Precedes after.attempt) ∧
    ∀ record ∈ state.retired, record.attempt.Precedes state.attempt

omit [DecidableEq Player] in
private theorem phaseLow_tail_lt (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph))
    (ordered : (phase :: remaining).IsChain fun before after => before.high = after.low) :
    phase.low < phaseLow remaining := by
  cases remaining with
  | nil => exact phase.nonempty.trans_le phase.bounded
  | cons next rest =>
      exact phase.nonempty.trans_eq (List.isChain_cons_cons.mp ordered).1

/-- Normalization appends only the old current namespace, then strictly advances it. -/
theorem settle_retiredOrdered (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (ordered : phases.IsChain fun before after => before.high = after.low)
    (chronology : RetiredOrdered (⟨phases, generation, entry, current, retired⟩ :
      PhaseRuntimeState graph)) :
    RetiredOrdered (settle phases generation entry current retired) := by
  induction phases generalizing generation entry current retired with
  | nil => exact chronology
  | cons phase remaining ih =>
      have tailLater := phaseLow_tail_lt phase remaining ordered
      have oldBefore : ∀ record ∈ retired,
          record.attempt.Precedes ⟨phase.low, generation⟩ := chronology.2
      have oldTail : ∀ record ∈ retired,
          record.attempt.Precedes ⟨phaseLow remaining, generation⟩ := by
        intro record member
        have earlier := oldBefore record member
        simp only [CommitAttemptId.Precedes] at earlier ⊢
        omega
      have extended : (retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩] :
            List (RetiredCommitAttempt graph)).Pairwise
          (fun (before after : RetiredCommitAttempt graph) =>
            before.attempt.Precedes after.attempt) := by
        rw [List.pairwise_append]
        refine ⟨chronology.1, by simp, ?_⟩
        intro before member after last
        obtain rfl := List.mem_singleton.mp last
        exact oldBefore before member
      have archiveTail : ∀ record ∈ retired ++
          [⟨⟨phase.low, generation⟩, (phase.drain current).native⟩],
          record.attempt.Precedes ⟨phaseLow remaining, generation⟩ := by
        intro record member
        rcases List.mem_append.mp member with old | new
        · exact oldTail record old
        · obtain rfl := List.mem_singleton.mp new
          exact Or.inr ⟨rfl, tailLater⟩
      simp only [settle]
      split
      · split
        · split
          · refine ⟨extended, ?_⟩
            intro record member
            rcases List.mem_append.mp member with old | new
            · have earlier := oldBefore record old
              simp only [CommitAttemptId.Precedes] at earlier ⊢
              change record.attempt.generation < generation + 1 ∨
                record.attempt.generation = generation + 1 ∧ record.attempt.phase < phase.low
              omega
            · obtain rfl := List.mem_singleton.mp new
              exact Or.inl (Nat.lt_succ_self generation)
          · exact ih _ _ _ _ ordered.tail ⟨extended, archiveTail⟩
        · exact ih _ _ _ _ ordered.tail ⟨chronology.1, oldTail⟩
      · exact chronology

/-- Arbitrary native commands retain strict archive chronology. -/
theorem retiredOrdered_invariant (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state => state.Ordered ∧ state.RetiredOrdered)
    where
  submit _ _ _ valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact ⟨settle_ordered _ _ _ _ _ valid.1, settle_retiredOrdered _ _ _ _ _ valid.1 valid.2⟩
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact ⟨settle_ordered _ _ _ _ _ valid.1, settle_retiredOrdered _ _ _ _ _ valid.1 valid.2⟩
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Every initialized raw history has strictly ordered retired attempts, all before current. -/
theorem retiredOrdered_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (initial plan)) horizon scheduler).Trace (some control)) :
    control.execution.application.RetiredOrdered := by
  have invariant := retiredOrdered_invariant runtime leaks
  have result := invariant.history _ horizon scheduler (fun state supported => ?_) trace
  · exact result.2
  · obtain ⟨input, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    exact ⟨initial_ordered plan input, settle_retiredOrdered _ _ _ _ _ plan.adjacent
      ⟨List.Pairwise.nil, fun _ impossible => by cases impossible⟩⟩

end PhaseRuntimeState
end Vegas.EventGraphRuntime
