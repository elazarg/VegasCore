/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourcePhaseAutomatic
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # First stable source frontiers after automatic excluded instructions -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Stop only after the required genuine source instructions, at Nature,
termination, or the next owner who remains active. -/
def sourceFrontierReached (setup : Setup (Player := Player) (L := L)) (minimum : Nat)
    (history : setup.commitRecoveryProtocol.History) : Prop :=
  minimum ≤ history.trace.length ∧ history.state.elim False (fun current =>
    (ProtocolState.actor setup.program current.point).elim True
      (fun owner => owner ∉ current.excluded))

/-- A literal source interval of already excluded instructions reaches the same
first stable frontier under every profile. Each preceding source point has an
excluded actor, so the actual stopped evaluator cannot halt at an earlier
prefix. The reachability budget never pads the source history. -/
theorem SourceProgram.Setup.commitRecovery_excluded_interval_until
    (setup : Setup (Player := Player) (L := L))
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (minimum : Nat) {fuel : Nat} {first last : setup.commitRecoveryProtocol.History}
    (path : setup.commitRecoveryProtocol.ReachesWithin fuel first last)
    (before after : CommitRecoveryState setup.program)
    (start : first.state = some before) (ending : last.state = some after)
    (generation : before.generation = after.generation)
    (exclusions : before.excluded = after.excluded)
    (automatic : ∀ point : SourceProgram.ProtocolState setup.program,
      instructionCount setup.program - ProtocolState.remaining setup.program before.point ≤
        instructionCount setup.program - ProtocolState.remaining setup.program point →
      instructionCount setup.program - ProtocolState.remaining setup.program point <
        instructionCount setup.program - ProtocolState.remaining setup.program after.point →
      ∃ owner ∈ before.excluded, ProtocolState.actor setup.program point = some owner)
    (elapsed : minimum ≤ first.trace.length)
    (stable : (ProtocolState.actor setup.program after.point).elim True
      (fun owner => owner ∉ after.excluded)) :
    setup.commitRecoveryModel.runBehavioralUntil certificate profile
      (sourceFrontierReached setup minimum) first = PMF.pure last := by
  induction path generalizing before with
  | refl =>
      apply setup.commitRecoveryModel.runBehavioralUntil_of_stopped certificate profile
      refine ⟨elapsed, ?_⟩
      rw [ending]
      exact stable
  | @step budget first last joint legal next supported rest ih =>
      rcases first with ⟨state, trace⟩
      change state = some before at start
      subst state
      obtain ⟨middle, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      subst next
      obtain ⟨final, finalState, laterGeneration, laterExcluded⟩ :=
        setup.commitRecovery_path_controls rest middle rfl
      have finalEq : final = after := Option.some.inj (finalState.symm.trans ending)
      subst final
      have earlierGeneration := before.step_generation_mono joint middle reached
      have earlierExcluded := before.step_excluded_monotone joint middle reached
      have sameGeneration : before.generation = middle.generation := by omega
      have sameExcluded : before.excluded = middle.excluded :=
        Finset.Subset.antisymm earlierExcluded (laterExcluded.trans exclusions.ge)
      have rank := before.step_rank joint middle legal.1 reached
      have consumed : ProtocolState.remaining setup.program middle.point + 1 =
          ProtocolState.remaining setup.program before.point := by rcases rank with h | h <;> omega
      have length := setup.commitRecovery_same_generation_length rest middle after rfl ending
        (sameGeneration.symm.trans generation)
      have leftBound := ProtocolState.remaining_le_instructionCount setup.program before.point
      have rightBound := ProtocolState.remaining_le_instructionCount setup.program after.point
      have traceBound := rest.trace_length_le
      change trace.length + 1 ≤ last.trace.length at traceBound
      change ProtocolState.remaining setup.program after.point + last.trace.length =
        ProtocolState.remaining setup.program middle.point + (trace.length + 1) at length
      obtain ⟨owner, excluded, acting⟩ := automatic before.point le_rfl (by omega)
      have going : ¬ sourceFrontierReached setup minimum
          (⟨some before, trace⟩ : setup.commitRecoveryProtocol.History) := by
        intro stopped
        have surviving := stopped.2
        change (ProtocolState.actor setup.program before.point).elim True
          (fun who => who ∉ before.excluded) at surviving
        rw [acting] at surviving
        exact surviving excluded
      have single := setup.commitRecovery_excluded_owned_step_law profile before trace owner
        acting excluded joint legal supported
      rw [setup.commitRecoveryModel.runBehavioralUntil_of_running certificate profile going
        legal.1, single, PMF.pure_bind]
      apply ih middle rfl ending (sameGeneration.symm.trans generation)
        (sameExcluded.symm.trans exclusions)
      · intro later low high
        obtain ⟨who, inactive, actor⟩ := automatic later (by omega) high
        exact ⟨who, sameExcluded ▸ inactive, actor⟩
      · change minimum ≤ trace.length + 1
        change minimum ≤ trace.length at elapsed
        omega

end Vegas
