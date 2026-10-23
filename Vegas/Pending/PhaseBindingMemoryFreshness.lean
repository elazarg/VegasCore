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
/-- Result bookkeeping changes neither catalogue meanings nor their freshness. -/
theorem rememberCompletion_candidates_not_fresh (memory : BindingShadow graph)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (event : graph.EventId) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    ∀ query, (memory.rememberCompletion event action value).candidates query ≠ some .fresh := valid

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

/-- A real nonmissing commitment response consumes its named handle before it
can be remembered, independently of the result and the old slot meaning. -/
theorem response_candidate_not_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
    (execution : (phaseApplication runtime leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat) :
    let after := execution.respond (phaseApplication runtime leaks) owner
      (phaseBindingResponse runtime leaks owner event payload result serial)
    after.application.current.native.candidates.lookup (owner, .prepared serial) ≠ .fresh := by
  intro after
  let material : WitnessedSubmission graph :=
    ⟨⟨.commitment event (owner, .prepared serial), match result with
      | .failure => none
      | .success value => some ⟨payload, value⟩⟩, .none⟩
  change (submitStep (Submission.register material.call execution.application.current.native owner)
    owner (.commitment event (owner, .prepared serial))).candidates.lookup
      (owner, .prepared serial) ≠ .fresh
  simp only [submitStep, ite_true]
  exact CommitmentCandidates.lookup_freeze_ne_fresh _ _

end Vegas.EventGraphRuntime.BindingShadow
