/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingCompletionMemory

/-! # Fresh physical preparation with an existing all-value private memory -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Updating the memory for a genuinely fresh slot has no effect on an older
physical catalogue. Earlier remembered meanings and actions are retained. -/
theorem rememberCandidate_native_fresh (memory : BindingShadow graph)
    (state : State graph) (owner : Player) (slot : CandidateSlot graph)
    (material : CommitmentCandidate (Raw L))
    (fresh : state.candidates.lookup (owner, slot) = .fresh) :
    (memory.rememberCandidate slot material).native owner state = memory.native owner state := by
  classical
  change (⟨memory.config state.config, state.accepted, _, state.clock, state.activatedAt⟩ :
    State graph) = ⟨memory.config state.config, state.accepted, _, state.clock, state.activatedAt⟩
  congr 1
  congr 1
  funext who query
  by_cases sameOwner : who = owner
  · subst who
    simp only [↓reduceIte]
    by_cases sameSlot : query = slot
    · subst query
      change (memory.rememberCandidate slot material).candidate slot
          (state.candidates.lookup (owner, slot)) =
        memory.candidate slot (state.candidates.lookup (owner, slot))
      rw [fresh]
      rfl
    · cases state.candidates.table owner query <;>
        simp only [candidate, rememberCandidate, Function.update_of_ne sameSlot]
  · simp only [sameOwner, ↓reduceIte]

/-- A same-slot nonmissing encoding updates the actual private catalogue memory,
while preserving all previously remembered results. The original and replacement
may independently be absent, mistyped, failed, or successful preparations. -/
theorem binding_preparation_memory (memory : BindingShadow graph) (state : State graph)
    (owner : Player) (event : graph.EventId) (serial : Nat)
    (first second : Option (Raw L))
    (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh) :
    let prepare (before : State graph) (material : Option (Raw L)) :=
      submitStep (Submission.register ⟨.commitment event (owner, .prepared serial), material⟩
        before owner) owner (.commitment event (owner, .prepared serial))
    let original := prepare (memory.native owner state) first
    let repaired := prepare state second
    let remembered := memory.rememberCandidate (.prepared serial)
      (original.candidates.lookup (owner, .prepared serial))
    remembered.native owner repaired = original := by
  classical
  let call (material : Option (Raw L)) : Submission graph :=
    ⟨.commitment event (owner, .prepared serial), material⟩
  let prepare (before : State graph) (material : Option (Raw L)) :=
    submitStep ((call material).register before owner) owner (call material).packet
  let original := prepare (memory.native owner state) first
  let repaired := prepare state second
  let remembered := memory.rememberCandidate (.prepared serial)
    (original.candidates.lookup (owner, .prepared serial))
  have configs (before : State graph) (material) :
      (prepare before material).config = before.config :=
    (submitStep_config _ _ _).trans ((call material).register_facts owner before).1
  have publics (before : State graph) (material) :
      (prepare before material).publicView = before.publicView :=
    (submitStep_publicView _ _ _).trans ((call material).register_facts owner before).2
  have own (before : State graph) (material) (slot : CandidateSlot graph) :
      (prepare before material).candidates.lookup (owner, slot) =
        (call material).candidateAfter owner (fun query => before.candidates.lookup (owner, query))
          slot := (call material).candidateAfter_eq owner before slot
  have other (before : State graph) (material) (who : Player) (different : who ≠ owner)
      (slot : CandidateSlot graph) :
      (prepare before material).candidates.lookup (who, slot) =
        before.candidates.lookup (who, slot) := by
    have observed := (submitStep_playerView_other ((call material).register before owner)
      owner who different (call material).packet).trans
        ((call material).register_other before owner who different)
    exact congrFun (congrArg PlayerView.candidates observed) slot
  have fixed : repaired.candidates.lookup (owner, .prepared serial) ≠ .fresh := by
    rw [own]
    cases second <;>
      simp only [call, Submission.candidateAfter, fresh, and_self, ↓reduceIte] <;>
      intro impossible <;> cases impossible
  have candidates : (remembered.native owner repaired).candidates = original.candidates := by
    change (⟨fun who slot => if who = owner then
        remembered.candidate slot (repaired.candidates.table who slot)
        else repaired.candidates.table who slot⟩ :
        CommitmentCandidates Player (CandidateSlot graph) (Raw L)) = ⟨original.candidates.table⟩
    congr 1
    funext who slot
    by_cases sameOwner : who = owner
    · subst who
      simp only [↓reduceIte]
      change remembered.candidate slot (repaired.candidates.lookup (owner, slot)) =
        original.candidates.lookup (owner, slot)
      by_cases sameSlot : slot = .prepared serial
      · subst slot
        cases actual : repaired.candidates.lookup (owner, .prepared serial) with
        | fresh => exact (fixed actual).elim
        | unopenable | openable raw =>
            simp only [candidate, remembered, rememberCandidate, Function.update_self,
              Option.getD_some]
      · have retained : remembered.candidates slot = memory.candidates slot := by
          simp only [remembered, rememberCandidate, Function.update_of_ne sameSlot]
        rw [own, own]
        simp only [call, Submission.candidateAfter, sameSlot, and_false, ↓reduceIte]
        simp only [native, CommitmentCandidates.lookup, ↓reduceIte]
        cases state.candidates.table owner slot <;>
          simp only [candidate, retained]
    · simp only [sameOwner, ↓reduceIte]
      change repaired.candidates.lookup (who, slot) = original.candidates.lookup (who, slot)
      rw [other state second who sameOwner slot,
        other (memory.native owner state) first who sameOwner slot]
      simp only [native, CommitmentCandidates.lookup, sameOwner, ↓reduceIte]
  change (⟨remembered.config repaired.config, repaired.accepted,
    (remembered.native owner repaired).candidates, repaired.clock, repaired.activatedAt⟩ :
      State graph) = ⟨original.config, original.accepted, original.candidates,
        original.clock, original.activatedAt⟩
  rw [State.mk.injEq]
  refine ⟨?_, ?_, candidates, ?_, ?_⟩
  · change memory.config repaired.config = original.config
    rw [configs, configs]
    rfl
  · have retained : original.accepted = state.accepted :=
      congrArg PublicView.accepted (publics (memory.native owner state) first)
    exact (congrArg PublicView.accepted (publics state second)).trans retained.symm
  · have retained : original.clock = state.clock :=
      congrArg PublicView.clock (publics (memory.native owner state) first)
    exact (congrArg PublicView.clock (publics state second)).trans retained.symm
  · have retained : original.activatedAt = state.activatedAt :=
      congrArg PublicView.activatedAt (publics (memory.native owner state) first)
    exact (congrArg PublicView.activatedAt (publics state second)).trans retained.symm

end Vegas.EventGraphRuntime.BindingShadow
