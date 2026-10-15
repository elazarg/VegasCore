/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingShadowStep
import Vegas.Pending.PhaseRawBindingRepair

/-! # Actual private preparation and its saved-checkpoint reconstruction -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace BindingShadow

/-- An older saved catalogue has not yet consumed this physical slot. Remembered
later material does not change that checkpoint or allocate a preparation there. -/
theorem native_rememberCandidate_of_fresh (state : State graph) (owner : Player)
    (slot : CandidateSlot graph) (original : CommitmentCandidate (Raw L))
    (fresh : state.candidates.lookup (owner, slot) = .fresh) :
    ((empty : BindingShadow graph).rememberCandidate slot original).native owner state = state := by
  classical
  have configs : ((empty : BindingShadow graph).rememberCandidate slot original).config
      state.config = state.config := config_empty _
  change (⟨_, state.accepted, _, state.clock, state.activatedAt⟩ : State graph) =
    ⟨state.config, state.accepted, state.candidates, state.clock, state.activatedAt⟩
  rw [State.mk.injEq]
  refine ⟨configs, rfl, ?_, rfl, rfl⟩
  cases catalogue : state.candidates with
  | mk table =>
      change (⟨fun who query => if who = owner then
          ((empty : BindingShadow graph).rememberCandidate slot original).candidate query
            (table who query) else table who query⟩ :
          CommitmentCandidates Player (CandidateSlot graph) (Raw L)) = ⟨table⟩
      congr 1
      funext who query
      by_cases sameOwner : who = owner
      · subst who
        simp only [↓reduceIte]
        by_cases sameSlot : query = slot
        · subst query
          have present : table owner slot = .fresh := by
            simpa only [catalogue, CommitmentCandidates.lookup] using fresh
          rw [present]
          rfl
        · cases actual : table owner query <;>
            simp only [candidate, rememberCandidate, Function.update_of_ne sameSlot,
              empty, Option.getD_none]
      · simp only [sameOwner, ↓reduceIte]

/-- Both physical preparations emit the same handle, while the remembered
original catalogue exactly reconstructs absent or wrongly typed private material. -/
theorem native_binding_preparation (state : State graph) (owner : Player)
    (event : graph.EventId) (serial : Nat) (opening : Option (Raw L))
    (payload : L.Ty) (value : L.Val payload)
    (fresh : state.candidates.lookup (owner, .prepared serial) = .fresh) :
    let prepare (material : Option (Raw L)) :=
      submitStep (Submission.register ⟨.commitment event (owner, .prepared serial), material⟩
        state owner) owner (.commitment event (owner, .prepared serial))
    let original := prepare opening
    let repaired := prepare (some ⟨payload, value⟩)
    let memory := (empty : BindingShadow graph).rememberCandidate (.prepared serial)
      (original.candidates.lookup (owner, .prepared serial))
    memory.native owner repaired = original := by
  classical
  let call (material : Option (Raw L)) : Submission graph :=
    ⟨.commitment event (owner, .prepared serial), material⟩
  let prepare (material : Option (Raw L)) :=
    submitStep ((call material).register state owner) owner (call material).packet
  let original := prepare opening
  let repaired := prepare (some ⟨payload, value⟩)
  let memory := (empty : BindingShadow graph).rememberCandidate (.prepared serial)
    (original.candidates.lookup (owner, .prepared serial))
  have configEq (material : Option (Raw L)) : (prepare material).config = state.config :=
    (submitStep_config _ _ _).trans ((call material).register_facts owner state).1
  have publicEq (material : Option (Raw L)) : (prepare material).publicView = state.publicView :=
    (submitStep_publicView _ _ _).trans ((call material).register_facts owner state).2
  have own (material : Option (Raw L)) (slot : CandidateSlot graph) :
      (prepare material).candidates.lookup (owner, slot) =
        (call material).candidateAfter owner (fun query => state.candidates.lookup (owner, query))
          slot := (call material).candidateAfter_eq owner state slot
  have other (material : Option (Raw L)) (who : Player) (different : who ≠ owner)
      (slot : CandidateSlot graph) :
      (prepare material).candidates.lookup (who, slot) = state.candidates.lookup (who, slot) := by
    have observed := (submitStep_playerView_other ((call material).register state owner)
      owner who different (call material).packet).trans
        ((call material).register_other state owner who different)
    exact congrFun (congrArg PlayerView.candidates observed) slot
  have target : repaired.candidates.lookup (owner, .prepared serial) =
      .openable ⟨payload, value⟩ := by
    rw [own]
    simp only [call, Submission.candidateAfter, fresh, and_self, ↓reduceIte]
  have candidates : (memory.native owner repaired).candidates = original.candidates := by
    change (⟨fun who slot => if who = owner then
        memory.candidate slot (repaired.candidates.table who slot)
        else repaired.candidates.table who slot⟩ :
        CommitmentCandidates Player (CandidateSlot graph) (Raw L)) = ⟨original.candidates.table⟩
    congr 1
    funext who slot
    by_cases sameOwner : who = owner
    · subst who
      simp only [↓reduceIte]
      change memory.candidate slot (repaired.candidates.lookup (owner, slot)) =
        original.candidates.lookup (owner, slot)
      by_cases sameSlot : slot = .prepared serial
      · subst slot
        rw [target]
        simp only [candidate, memory, rememberCandidate, Function.update_self,
          Option.getD_some]
      · have none : memory.candidates slot = none := by
          simp only [memory, rememberCandidate, Function.update_of_ne sameSlot, empty]
        have unchanged : memory.candidate slot (repaired.candidates.lookup (owner, slot)) =
            repaired.candidates.lookup (owner, slot) := by
          cases repaired.candidates.lookup (owner, slot) <;>
            simp only [candidate, none, Option.getD_none]
        rw [unchanged, own, own]
        simp only [call, Submission.candidateAfter, sameSlot, and_false, ↓reduceIte]
    · simp only [sameOwner, ↓reduceIte]
      exact (other _ who sameOwner slot).trans (other _ who sameOwner slot).symm
  change (⟨memory.config repaired.config, repaired.accepted,
    (memory.native owner repaired).candidates, repaired.clock, repaired.activatedAt⟩ :
      State graph) = ⟨original.config, original.accepted, original.candidates,
        original.clock, original.activatedAt⟩
  rw [State.mk.injEq]
  refine ⟨?_, ?_, candidates, ?_, ?_⟩
  · change (empty : BindingShadow graph).config repaired.config = original.config
    rw [config_empty, configEq, configEq]
  · exact (congrArg PublicView.accepted (publicEq _)).trans
      (congrArg PublicView.accepted (publicEq _)).symm
  · exact (congrArg PublicView.clock (publicEq _)).trans
      (congrArg PublicView.clock (publicEq _)).symm
  · exact (congrArg PublicView.activatedAt (publicEq _)).trans
      (congrArg PublicView.activatedAt (publicEq _)).symm

end BindingShadow
end Vegas.EventGraphRuntime
