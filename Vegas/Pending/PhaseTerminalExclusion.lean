/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseApplication

/-! # Terminal exclusion agrees with the saved physical checkpoint -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- Finishing the last installed phase saves its actual permanent exclusion.
Subsequent terminal normalization retains that same saved set. -/
theorem settle_terminal_excluded (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (prior : phases = [] → entry.excluded = current.excluded) :
    (settle phases generation entry current retired).phases = [] →
      (settle phases generation entry current retired).entry.excluded =
        (settle phases generation entry current retired).current.excluded := by
  induction phases generalizing generation entry current retired with
  | nil => exact prior
  | cons phase remaining ih =>
      simp only [settle]
      split
      · split
        · split
          · intro impossible
            cases impossible
          · exact ih _ _ _ _ (fun _ => rfl)
        · exact ih _ _ _ _ (fun _ => rfl)
      · intro impossible
        cases impossible

end PhaseRuntimeState

/-- Actual operations cannot change exclusion after the final phase has been
saved, while every new terminal phase closure records its current exclusion. -/
theorem phaseApplication_terminalExclusion (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state => state.phases = [] →
      state.entry.excluded = state.current.excluded) where
  submit _ _ _ valid := valid
  handle state message next _valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · rename_i authorized
      obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      apply PhaseRuntimeState.settle_terminal_excluded
      intro empty
      change state.phases = [] at empty
      have allowed := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp authorized).1).2
      simp only [PhaseRuntimeState.allows, empty, List.head?_nil, Bool.false_eq_true] at allowed
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rename_i allowed
      rw [PMF.support_map] at reached
      obtain ⟨native, _supported, rfl⟩ := reached
      apply PhaseRuntimeState.settle_terminal_excluded
      intro empty
      change state.phases = [] at empty
      cases command with
      | advanceClock => exact valid empty
      | executeSample event | expire event =>
          simp only [PhaseRuntimeState.commandAllowed, empty, List.head?_nil,
            Option.any_none, Bool.false_eq_true] at allowed
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- At every actual initialized terminal history, the saved source checkpoint
and the current physical endpoint have exactly the same excluded players. -/
theorem phaseTerminalExclusion_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (finished : control.execution.application.phases = []) :
    control.execution.application.entry.excluded = control.execution.application.current.excluded :=
  (phaseApplication_terminalExclusion runtime leaks).history _ _ _
    (fun state supported => by
      obtain ⟨draw, _supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact PhaseRuntimeState.settle_terminal_excluded _ _ _ _ _ (fun _ => rfl)) trace finished

end Vegas.EventGraphRuntime
