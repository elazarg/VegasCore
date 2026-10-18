/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCompletion
import Vegas.Pending.PhaseSeedBudget

/-! # The actual permanent exclusion checkpoint of a survivor retry -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- A two-player retry with a surviving owner has already saved the other
owner's exclusion. Servicing that other owner adds no new excluded principal. -/
theorem retry_exclusion_checkpoint (selected : app.Scheduler) (current : app.Control)
    (trace : (app.protocol initial horizon selected).Trace (some current))
    (retired : current.execution.application.attempt ≠ originalAttempt)
    (installed : current.execution.application.phases.head? = some commitmentPhase)
    (owner : Player) (active : owner ∉ current.execution.application.current.excluded) :
    current.execution.application.entry.excluded = current.execution.application.current.excluded ∧
      opponent owner ∈ current.execution.application.entry.excluded := by
  classical
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon selected
    (by
      intro state supported
      rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
      subst state
      exact PhaseRuntimeState.initial_seedBudget plan
        (encodeInputs (Env.empty (CellVal simpleExpr)))) trace
  have positive : 0 < current.execution.application.generation := by
    by_contra missing
    have zero : current.execution.application.generation = 0 := by omega
    apply retired
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, zero]
    rfl
  have nonempty := Finset.card_pos.mp (lt_of_lt_of_le positive budget.generation)
  obtain ⟨failed, saved⟩ := nonempty
  have failedDifferent : failed ≠ owner := by
    intro same
    exact active (same ▸ budget.excluded saved)
  have only (other : Player) (different : other ≠ owner) : other = opponent owner := by
    fin_cases owner <;> fin_cases other <;> simp_all [opponent, alice, bob]
  have foreignSaved : opponent owner ∈ current.execution.application.entry.excluded := by
    rwa [only failed failedDifferent] at saved
  refine ⟨Finset.Subset.antisymm budget.excluded ?_, foreignSaved⟩
  intro other member
  have different : other ≠ owner := by
    intro same
    exact active (same ▸ member)
  rw [only other different]
  exact foreignSaved

end Vegas.Examples.CommitSeedSignalling
