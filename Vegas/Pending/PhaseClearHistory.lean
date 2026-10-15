/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSeedBudget
import Vegas.Pending.PhaseNativeInvariant

/-! # Clear physical histories contain no retries or retired attempts -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace PhaseRuntimeState

/-- With no excluded owner, automatic drain is the identity and no phase can
retry. Clean phase advances preserve the complete current recovery state. -/
theorem settle_of_clear (phases : List (RuntimePhase graph)) (generation : Nat)
    (entry current : RecoveryState graph) (retired : List (RetiredCommitAttempt graph))
    (clear : current.excluded = ∅) :
    (settle phases generation entry current retired).current = current ∧
      (settle phases generation entry current retired).generation = generation ∧
      (settle phases generation entry current retired).retired = retired := by
  classical
  induction phases generalizing entry with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons phase remaining ih =>
      have drained := phase.drain_eq_of_clear current (by
        rintro event ⟨_member, automatic⟩
        obtain ⟨owner, _acting, excluded⟩ := automatic.owned
        simp only [clear, Finset.notMem_empty] at excluded)
      simp only [settle, drained, clear, Finset.empty_sdiff, Finset.empty_inter,
        Finset.not_nonempty_empty, and_false, ite_false]
      split
      · exact ih current
      · exact ⟨rfl, rfl, rfl⟩

/-- A clear normalized endpoint has exactly the original current state,
namespace generation and archive; the clear premise may be read at either end. -/
theorem normalize_of_clear (state : PhaseRuntimeState graph)
    (clear : state.normalize.current.excluded = ∅) :
    state.normalize.current = state.current ∧
      state.normalize.generation = state.generation ∧ state.normalize.retired = state.retired := by
  have excluded :=
    (settle_physical state.phases state.generation state.entry state.current state.retired).1
  have before : state.current.excluded = ∅ := excluded.symm.trans clear
  exact settle_of_clear state.phases state.generation state.entry state.current state.retired before

end PhaseRuntimeState

/-- Any actual clear initialized prefix has an empty retired-attempt archive.
This applies to arbitrary raw submissions, scheduler commands and passive leaks. -/
theorem phaseApplication_clearArchive (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)) :
    (phaseApplication runtime leaks).Invariant (fun state =>
      state.current.excluded = ∅ → state.retired = []) where
  submit state who submission valid := valid
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, _handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      intro clear
      have same := PhaseRuntimeState.normalize_of_clear
        ({state with current := state.current.inclusionResult message.payload.packet.call native} :
          PhaseRuntimeState graph) clear
      have updated : (state.current.inclusionResult message.payload.packet.call native).excluded =
          ∅ := (congrArg RecoveryState.excluded same.1).symm.trans clear
      have before : state.current.excluded = ∅ := Finset.subset_empty.mp
        (updated ▸ state.current.inclusionResult_excluded_subset message.payload.packet.call native)
      exact same.2.2.trans (valid before)
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · obtain ⟨native, _supported, rfl⟩ := PMF.support_map .. ▸ reached
      intro clear
      have same := PhaseRuntimeState.normalize_of_clear
        ({state with current := state.current.environmentResult command native} :
          PhaseRuntimeState graph) clear
      have updated : (state.current.environmentResult command native).excluded = ∅ :=
        (congrArg RecoveryState.excluded same.1).symm.trans clear
      have before : state.current.excluded = ∅ := Finset.subset_empty.mp
        (updated ▸ state.current.environmentResult_excluded_subset command native)
      exact same.2.2.trans (valid before)
    · cases (PMF.mem_support_pure_iff _ _).mp reached
      exact valid

/-- Empty permanent exclusion at an actual initialized raw history rules out
every retry generation and every retired attempt. -/
theorem phase_clear_history (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((phaseApplication runtime leaks).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    control.execution.application.generation = 0 ∧ control.execution.application.retired = [] := by
  have budget := (phaseApplication_seedBudget runtime leaks).history _ horizon scheduler
    (fun state member => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
      exact PhaseRuntimeState.initial_seedBudget plan draw) trace
  have generation := budget.current_generation
  rw [clear, Finset.card_empty] at generation
  refine ⟨Nat.eq_zero_of_le_zero generation, ?_⟩
  have archives := (phaseApplication_clearArchive runtime leaks).history _ horizon scheduler
    (fun state member => by
      obtain ⟨draw, _, rfl⟩ := PMF.support_map .. ▸ member
      intro _clear
      exact (PhaseRuntimeState.settle_of_clear plan.phases 0
        ⟨State.initial draw, ∅⟩ ⟨State.initial draw, ∅⟩ [] rfl).2.2) trace
  exact archives clear

end Vegas.EventGraphRuntime
