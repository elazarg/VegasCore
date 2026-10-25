/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionEvidence
import Vegas.Pending.PhaseCompletion

/-! # Exclusion evidence within a saved source phase

The saved excluded set already accounts for retired attempts. Subsequent
exclusion has an actual new public failure at or after the saved source rank;
accepted unusable bindings remain outside this detector.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace ExclusionEvidence

variable {low : Nat} {inherited : Finset Player} {state : RecoveryState graph}

omit [DecidableEq Player] in
/-- An exact saved phase prefix supplies the rank-cut evidence boundary. -/
theorem of_prefix (receipts : state.native.ReceiptsComplete)
    (atPrefix : state.native.config.cut.IsPrefix low) (excluded : state.excluded = inherited) :
    ExclusionEvidence low inherited state :=
  of_rank_cut receipts atPrefix.2 excluded

/-- Local automatic service preserves evidence relative to the same saved rank. -/
theorem phase_drainFuel (phase : RuntimePhase graph) (fuel : Nat)
    (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited (phase.drainFuel fuel state) := by
  exact phase.drainFuel_induction (ExclusionEvidence low inherited)
    (fun _ event eligible previous => previous.completeAutomatic event eligible.2) fuel state valid

theorem phase_drain (phase : RuntimePhase graph)
    (valid : ExclusionEvidence low inherited state) :
    ExclusionEvidence low inherited (phase.drain state) :=
  valid.phase_drainFuel phase _

omit [DecidableEq Player] in
/-- At a completed binding interval, the only new exclusion evidence is an
actual absent receipt, independent of hidden typed binding failures. -/
theorem commitment_owners (phase : RuntimePhase graph) (kind : phase.kind = .commitment)
    (valid : ExclusionEvidence phase.low inherited state)
    (within : state.native.config.cut.Within phase.low phase.high) (who : Player) :
    who ∈ state.excluded ↔ who ∈ inherited ∨
      ∃ event ∈ phase.events, event ∈ state.native.config.cut.completed ∧
        state.native.accepted (.inr event) = none ∧ graph.actor? event = some who := by
  classical
  rw [valid.excluded who]
  constructor
  · rintro (previous | ⟨event, lower, acting, failed⟩)
    · exact Or.inl previous
    have completed := failed.completed
    have upper := within.2 event completed
    have binding := phase.fields event lower upper
    rw [kind] at binding
    obtain ⟨owner, payload, outputEq⟩ := binding
    have omitted : state.native.publicView.missedBinding event = true := by
      rcases failed with omitted | publication
      · exact omitted
      · cases view : nodeView graph event with
        | bind => simp only [RecoveryState.publicationFailed, view, Bool.false_eq_true]
            at publication
        | resolve author ty ref checks layout code => cases outputEq.symm.trans layout
        | sample ty law layout code => cases outputEq.symm.trans layout
    exact Or.inr ⟨event, (phase.mem_events event).mpr ⟨lower, upper⟩, completed,
      ((State.publicView_missedBinding state.native event owner payload outputEq).mp omitted).2,
      acting⟩
  · rintro (previous | ⟨event, inside, completed, absent, acting⟩)
    · exact Or.inl previous
    obtain ⟨lower, upper⟩ := (phase.mem_events event).mp inside
    have binding := phase.fields event lower upper
    rw [kind] at binding
    obtain ⟨owner, payload, outputEq⟩ := binding
    exact Or.inr ⟨event, lower, acting, Or.inl
      ((State.publicView_missedBinding state.native event owner payload outputEq).mpr
        ⟨completed, absent⟩)⟩

end ExclusionEvidence
end Vegas.EventGraphRuntime
