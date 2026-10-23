/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.FailedBindingDeviation

/-! # Every step from the intended game stays in it or leaves a debt

Whatever joint action a step takes from a point of the intended game, it
reaches a point of the intended game, or one at which some player owes a
failed reveal (`Vegas.SourceProgram.ProtocolState.intended_or_owesFailure_step`):
a failed binding, a value its guard is predicted to reject, and a withholding
each leave their actor owing a failure, and every other step stays intended.
Unlike `Vegas.SourceProgram.ProtocolState.owesFailure_of_deviation`, the
statement reads only what the step reads of the joint action, so it needs no
admission interface.
-/

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **Intended or indebted.** Every step from a point of the intended game
reaches a point of the intended game or one at which some player owes a failed
reveal. -/
theorem intended_or_owesFailure_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    Intended program state → target ∈ (step program state joint).support →
    Intended program target ∨ ∃ who, OwesFailure who program target
  | _, _, .ret _, _, _, _, intended, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact Or.inl intended
  | _, _, .sample _ fresh _ next, state, joint, target, intended, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, supported, rfl⟩ := reached
          exact Or.inl
            (intended_entry next _ (intended.1.sample fresh value) (intended.2 value supported))
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intended_or_owesFailure_step next rest joint after intended supported
  | _, _, .commit (payload := payload) name owner fresh guard next, state, joint, target,
      intended, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          cases bound : OwnAction.binding owner name payload (joint owner) with
          | failure =>
              exact Or.inr ⟨owner, Or.inr (failedBinding_entry next _
                (Config.failedBinding_commit config intended.1.unique fresh guard _))⟩
          | success value =>
              by_cases accepted : guard.predicts (sourceObserve owner config.state) value = true
              · exact Or.inl (intended_entry next _ (intended.1.commit fresh guard value accepted)
                  (intended.2.2 value accepted))
              · exact Or.inr ⟨owner, Or.inl (indebted_entry next _
                  (intended.1.indebted_commit fresh guard value (by simpa using accepted)))⟩
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intended_or_owesFailure_step next rest joint after intended supported
  | _, _, .reveal published owner name fresh source _ next, state, joint, target, intended,
      reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          cases disclosed : OwnAction.disclosure (joint owner) with
          | true =>
              obtain ⟨kept, opened⟩ := intended.1.reveal fresh source
              refine Or.inl ⟨?_, intended_entry next _ kept intended.2⟩
              rw [base_entry]
              exact opened
          | false =>
              refine Or.inr ⟨owner, Or.inl (Or.inl ⟨rfl, ?_⟩)⟩
              rw [base_entry]
              simp [revealSuccessor]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases intended_or_owesFailure_step next rest joint after intended.2 supported with
            kept | ⟨who, indebted | failed⟩
          · exact Or.inl ⟨(base_step next rest joint after supported).symm ▸ intended.1, kept⟩
          · exact Or.inr ⟨who, Or.inl (Or.inr indebted)⟩
          · exact Or.inr ⟨who, Or.inr (Or.inr failed)⟩

end Vegas.SourceProgram.ProtocolState
