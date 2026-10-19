/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNamespace
import Interaction.ReactiveInvariant

/-! # The permanent exclusion saved at an actual namespace installation -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Starting settlement with the same permanent exclusion on both sides keeps
that equality through automatic advances. No clear-state condition is used. -/
theorem settle_entry_excluded_of_same (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (same : entry.excluded = current.excluded) :
    (settle phases generation entry current retired).entry.excluded =
      (settle phases generation entry current retired).current.excluded := by
  induction phases generalizing entry current retired with
  | nil => exact same
  | cons phase remaining ih =>
      have noFailure : ¬ (phase.kind = .commitment ∧
          (((phase.drain current).excluded \ entry.excluded) ∩ phase.owners).Nonempty) := by
        simp only [RuntimePhase.drain_excluded, same, Finset.sdiff_self,
          Finset.empty_inter, Finset.not_nonempty_empty, and_false, not_false_eq_true]
      simp only [settle, noFailure, ↓reduceIte]
      split
      · exact ih _ _ _ rfl
      · exact same.trans (phase.drain_excluded current).symm

/-- A changed normalized namespace either installs a retry checkpoint or
consumes the old head. Both operations save the actual permanent exclusion. -/
theorem normalize_entry_excluded_of_changed (state : PhaseRuntimeState graph)
    (changed : state.normalize.attempt ≠ state.attempt) :
    state.normalize.entry.excluded = state.normalize.current.excluded := by
  cases installed : state.phases with
  | nil =>
      apply False.elim
      apply changed
      simp only [normalize, installed, settle, attempt]
  | cons phase remaining =>
      by_cases finished : phase.Finished (phase.drain state.current)
      · by_cases failed : phase.kind = .commitment ∧
            (((phase.drain state.current).excluded \ state.entry.excluded) ∩
              phase.owners).Nonempty
        · by_cases survivors : (phase.owners \ (phase.drain state.current).excluded).Nonempty
          · simp only [normalize, installed, settle, finished, failed, survivors, ↓reduceIte]
            exact (phase.drain_excluded _).symm
          · simp only [normalize, installed, settle, finished, failed, survivors, ↓reduceIte]
            exact settle_entry_excluded_of_same _ _ _ _ _ rfl
        · simp only [normalize, installed, settle, finished, failed, ↓reduceIte]
          exact settle_entry_excluded_of_same _ _ _ _ _ rfl
      · apply False.elim
        apply changed
        simp only [normalize, installed, settle, finished, ↓reduceIte, attempt]

/-- The real initial application saves the same exclusion even if it skips
automatically completed phases before exposing its first descriptor. -/
theorem initial_entry_excluded (plan : RuntimePhasePlan graph) (inputs : graph.Inputs) :
    (initial plan inputs).entry.excluded = (initial plan inputs).current.excluded :=
  settle_entry_excluded_of_same _ _ _ _ _ rfl

end PhaseRuntimeState

/-- Native handling and environment effects save permanent exclusion whenever
they install another namespace. Private preparation never changes namespace. -/
theorem phaseApplication_namespaceInstallation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).StepRelation (fun before after =>
      before.attempt ≠ after.attempt → after.entry.excluded = after.current.excluded) where
  refl _ different := (different rfl).elim
  submit _ _ _ different := (different rfl).elim
  handle state message next accepted different := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      exact PhaseRuntimeState.normalize_entry_excluded_of_changed _ (Ne.symm different)
    · cases accepted
  environment state command next reached different := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      exact PhaseRuntimeState.normalize_entry_excluded_of_changed _ (Ne.symm different)
    · cases (PMF.mem_support_pure_iff ..).mp reached
      exact (different rfl).elim

end Vegas.EventGraphRuntime
