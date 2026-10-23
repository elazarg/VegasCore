/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingPreparationMemory

/-! # Actual nonfresh candidate meanings in an evolving binding memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

omit [DecidableEq Player] in
/-- Empty memory cannot reconstruct a prepared slot as fresh. -/
theorem empty_candidates_not_fresh (slot : CandidateSlot graph) :
    (empty : BindingShadow graph).candidates slot ≠ some .fresh := by
  intro impossible
  cases impossible

omit [DecidableEq Player] in
/-- Remembering an actual consumed candidate preserves the earlier constraint. -/
theorem rememberCandidate_candidates_not_fresh (memory : BindingShadow graph)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (slot : CandidateSlot graph) (material : CommitmentCandidate (Raw L))
    (fixed : material ≠ .fresh) :
    ∀ query, (memory.rememberCandidate slot material).candidates query ≠ some .fresh := by
  classical
  intro query
  by_cases same : query = slot
  · subst query
    simp only [rememberCandidate, Function.update_self]
    exact fun same => fixed (Option.some.inj same)
  · simpa only [rememberCandidate, Function.update_of_ne same] using valid query

omit [DecidableEq Player] in
/-- Under the actual memory constraint, reconstruction preserves physical
freshness even for slots observed before a later preparation was remembered. -/
theorem candidate_fresh_iff (memory : BindingShadow graph)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (slot : CandidateSlot graph) (material : CommitmentCandidate (Raw L)) :
    memory.candidate slot material = .fresh ↔ material = .fresh := by
  cases material with
  | fresh => exact Iff.rfl
  | unopenable =>
      cases stored : memory.candidates slot with
      | none => simp only [candidate, stored, Option.getD_none, reduceCtorEq]
      | some value =>
          have fixed : value ≠ .fresh := fun same => valid slot (stored.trans (congrArg some same))
          simpa only [candidate, stored, Option.getD_some, reduceCtorEq, iff_false] using fixed
  | openable raw =>
      cases stored : memory.candidates slot with
      | none => simp only [candidate, stored, Option.getD_none, reduceCtorEq]
      | some value =>
          have fixed : value ≠ .fresh := fun same => valid slot (stored.trans (congrArg some same))
          simpa only [candidate, stored, Option.getD_some, reduceCtorEq, iff_false] using fixed

end Vegas.EventGraphRuntime.BindingShadow
