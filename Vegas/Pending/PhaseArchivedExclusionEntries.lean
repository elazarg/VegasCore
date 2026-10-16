/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSavedExclusionReadback

/-! # Public readback of exclusions at retired attempt entries -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

namespace State

/-- A retained exact lower prefix determines all later public failures below
that prefix, even when later events complete in a different order. -/
theorem PublicFailureExtension.failureOwnersBefore_eq {before after : State graph}
    (extension : before.PublicFailureExtension after) (low : Nat)
    (atLow : before.config.cut.IsPrefix low) :
    after.failureOwnersBefore low = before.failureOwners := by
  classical
  ext owner
  simp only [failureOwnersBefore, failureOwners, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨event, earlier, acting, failed⟩
    exact ⟨event, acting, (extension.failures event ((atLow.2 event).mpr earlier)).mp failed⟩
  · rintro ⟨event, acting, failed⟩
    exact ⟨event, (atLow.2 event).mp failed.completed, acting,
      (extension.failures event failed.completed).mpr failed⟩

end State

namespace PhaseRuntimeState

/-- Entry exclusions read in archive order. Only preceding archived failures
and failures below the archived attempt's saved boundary enter each result. -/
def archivedExclusionEntriesFrom (inherited : Finset Player) :
    List (RetiredCommitAttempt graph) → List (CommitAttemptId × Finset Player)
  | [] => []
  | record :: rest =>
    (record.attempt, inherited ∪ record.state.failureOwnersBefore record.attempt.phase) ::
      archivedExclusionEntriesFrom (inherited ∪ record.state.failureOwners) rest

/-- The public exclusion readout of every retired attempt's entry. -/
def archivedExclusionEntries (retired : List (RetiredCommitAttempt graph)) :
    List (CommitAttemptId × Finset Player) := archivedExclusionEntriesFrom ∅ retired

theorem archivedExclusionEntriesFrom_length (inherited : Finset Player)
    (retired : List (RetiredCommitAttempt graph)) :
    (archivedExclusionEntriesFrom inherited retired).length = retired.length := by
  induction retired generalizing inherited with
  | nil => rfl
  | cons record rest ih => exact congrArg Nat.succ (ih _)

theorem archivedExclusionEntriesFrom_append (inherited : Finset Player)
    (first second : List (RetiredCommitAttempt graph)) :
    archivedExclusionEntriesFrom inherited (first ++ second) =
      archivedExclusionEntriesFrom inherited first ++
        archivedExclusionEntriesFrom (inherited ∪ archivedFailureOwners first) second := by
  induction first generalizing inherited with
  | nil => simp only [List.nil_append, archivedExclusionEntriesFrom, archivedFailureOwners,
      List.foldr_nil, Finset.union_empty]
  | cons record rest ih =>
    simp only [List.cons_append, archivedExclusionEntriesFrom, archivedFailureOwners,
      List.foldr_cons]
    rw [ih]
    simp only [Finset.union_assoc]
    rfl

/-- The readout at an index uses exactly the earlier archives, excluding
failures introduced by this or any later attempt above its saved boundary. -/
theorem archivedExclusionEntriesFrom_getElem (inherited : Finset Player)
    (retired : List (RetiredCommitAttempt graph)) (index : Nat) (bound : index < retired.length) :
    (archivedExclusionEntriesFrom inherited retired)[index]'(by
      rw [archivedExclusionEntriesFrom_length]; exact bound) =
      (retired[index].attempt, (inherited ∪ archivedFailureOwners (retired.take index)) ∪
        retired[index].state.failureOwnersBefore retired[index].attempt.phase) := by
  induction retired generalizing inherited index with
  | nil => simp only [List.length_nil, Nat.not_lt_zero] at bound
  | cons record rest ih =>
    cases index with
    | zero => simp only [archivedExclusionEntriesFrom, List.getElem_cons_zero, List.take_zero,
        archivedFailureOwners, List.foldr_nil, Finset.union_empty]
    | succ index =>
      have smaller : index < rest.length := Nat.lt_of_succ_lt_succ bound
      simpa only [archivedExclusionEntriesFrom, List.getElem_cons_succ, List.take_succ_cons,
        archivedFailureOwners, List.foldr_cons, Finset.union_assoc] using
        ih (inherited ∪ record.state.failureOwners) index smaller

/-- Hidden archived values cannot affect the chronological entry-exclusion
readout: every ingredient is determined by public failure verdicts. -/
theorem archivedExclusionEntriesFrom_eq_of_publicViews_eq (inherited : Finset Player)
    (first second : List (RetiredCommitAttempt graph))
    (same : first.map (fun record => (record.attempt, record.state.publicView)) =
      second.map (fun record => (record.attempt, record.state.publicView))) :
    archivedExclusionEntriesFrom inherited first =
      archivedExclusionEntriesFrom inherited second := by
  induction first generalizing inherited second with
  | nil =>
    cases second with
    | nil => rfl
    | cons record rest => cases same
  | cons record rest ih =>
    cases second with
    | nil => simp only [List.map_cons, List.map_nil, List.cons_ne_nil] at same
    | cons other more =>
      have pairs := List.cons.inj same
      have attemptEq := congrArg Prod.fst pairs.1
      have publicEq := congrArg Prod.snd pairs.1
      change record.attempt = other.attempt at attemptEq
      change record.state.publicView = other.state.publicView at publicEq
      have failures : record.state.failureOwners = other.state.failureOwners := by
        have singleton := archivedFailureOwners_eq_of_publicViews_eq [record] [other]
          (congrArg (fun pair => [pair]) pairs.1)
        simpa only [archivedFailureOwners, List.foldr_cons, List.foldr_nil,
          Finset.union_empty] using singleton
      simp only [archivedExclusionEntriesFrom]
      rw [attemptEq, State.failureOwnersBefore_congr publicEq, failures, ih _ more pairs.2]

/-- Appending an actual drained attempt records exactly its saved entry's
exclusions. The archive is not treated as a fresh hypothetical raw history. -/
theorem archivedExclusionEntries_append_drain {state : PhaseRuntimeState graph}
    (archives : state.ArchivedExclusions) (checkpoint : state.PublicFailureCheckpoint)
    (frontier : state.Frontier) (phase : RuntimePhase graph)
    (remaining : List (RuntimePhase graph)) (installed : state.phases = phase :: remaining) :
    archivedExclusionEntries
        (state.retired ++ [⟨state.attempt, (phase.drain state.current).native⟩]) =
      archivedExclusionEntries state.retired ++ [(state.attempt, state.entry.excluded)] := by
  have saved := frontier.positioned
  rw [installed] at saved
  have low : state.attempt.phase = phase.low := by
    simp only [attempt, installed, List.head?_cons, Option.map_some, Option.getD_some]
  have failures := State.PublicFailureExtension.failureOwnersBefore_eq
    (checkpoint.trans (phase.drain_publicFailureExtension state.current)) phase.low saved.1
  unfold archivedExclusionEntries
  rw [archivedExclusionEntriesFrom_append]
  simp only [Finset.empty_union, archivedExclusionEntriesFrom, low, failures]
  rw [archives.saved_eq]

end PhaseRuntimeState

/-- The public readout after retiring the current attempt recovers the saved
exclusions on every genuine initialized raw execution. -/
theorem phase_archivedExclusionEntries_append_drain (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (phase : RuntimePhase graph) (remaining : List (RuntimePhase graph))
    (installed : control.execution.application.phases = phase :: remaining) :
    PhaseRuntimeState.archivedExclusionEntries
        (control.execution.application.retired ++
          [⟨control.execution.application.attempt,
            (phase.drain control.execution.application.current).native⟩]) =
      PhaseRuntimeState.archivedExclusionEntries control.execution.application.retired ++
        [(control.execution.application.attempt, control.execution.application.entry.excluded)] :=
  PhaseRuntimeState.archivedExclusionEntries_append_drain
    (phaseArchivedExclusions_history runtime leaks plan inputs horizon scheduler trace)
    (phasePublicFailureCheckpoint_history runtime leaks plan inputs horizon scheduler trace)
    (phaseExclusionRecord_history runtime leaks plan inputs horizon scheduler trace).frontier
    phase remaining installed

end Vegas.EventGraphRuntime
