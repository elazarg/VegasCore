/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.FailedBinding

/-! # Departures from intended play under arbitrary commitment admission

Irrevocable failed bindings, rejected values and withheld publications each
force a failed reveal of the deviating owner. This property uses the existing
source transitions and allows any choice of commitment admission at each site.
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

def OwesFailure (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) : Prop :=
  Indebted who program state ∨ FailedBinding who program state

theorem owesFailure_step (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (joint : Player → Option (OwnAction Player L)) (target : ProtocolState program)
    (owed : OwesFailure who program state) (reached : target ∈ (step program state joint).support) :
    OwesFailure who program target :=
  owed.elim (fun indebted => Or.inl (indebted_step who program state joint target indebted reached))
    (fun failed => Or.inr (failedBinding_step who program state joint target failed reached))

theorem failedReveals_pos_of_owesFailure (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    (owed : OwesFailure who program state) {terminal : State L program.terminalCtx}
    (read : readout program state = some terminal) :
    1 ≤ failedReveals program who (publicOutcome program terminal) :=
  owed.elim (fun indebted => failedReveals_pos_of_indebted who program state indebted read)
    (fun failed => failedReveals_pos_of_failedBinding who program state failed read)

theorem owesFailure_of_deviation (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (state : ProtocolState program) → Intended program state →
    (joint : Player → Option (OwnAction Player L)) → (action : OwnAction Player L) →
    joint who = some action →
    ProtocolView.actor who program (observe who program state) = some who →
    action ∈ ProtocolView.available who program admission (observe who program state) →
    action ∉ ProtocolView.intendedAvailable who program (observe who program state) →
    ∀ target ∈ (step program state joint).support, OwesFailure who program target
  | _, _, .ret _, _, _, _, _, _, _, acts, _, _, _, _ => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, admission, state, intended, joint, action, chosen, acts,
      available, new, target, reached => by
      cases state with
      | inl config => simp [ProtocolView.actor, observe] at acts
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact owesFailure_of_deviation who next admission rest intended joint action chosen
            acts available new after supported
  | _, _, .commit (payload := payload) name owner fresh guard next, admission, state,
      intended, joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨choice, _, rfl⟩ := available
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rw [chosen, OwnAction.binding_commit]
          cases choice with
          | failure =>
              right
              exact failedBinding_entry next _
                (Config.failedBinding_commit config intended.1.unique fresh guard _)
          | success value =>
              have rejected : guard.predicts (sourceObserve owner config.state) value = false := by
                have notIntended :
                    value ∉ intendedValues owner guard (sourceObserve owner config.state) :=
                  fun offered => new ⟨value, offered, rfl⟩
                rw [mem_intendedValues_self guard _ intended.2.1] at notIntended
                simpa using notIntended
              left
              exact indebted_entry next _ (intended.1.indebted_commit fresh guard value rejected)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact owesFailure_of_deviation who next (fun site => admission (some site)) rest intended
            joint action chosen acts available new after supported
  | _, _, .reveal published owner name fresh source _ next, admission, state, intended,
      joint, action, chosen, acts, available, new, target, reached => by
      cases state with
      | inl config =>
          have same : owner = who := by simpa [ProtocolView.actor, observe] using acts
          subst same
          obtain ⟨disclose, rfl⟩ := available
          cases disclose with
          | true => exact (new rfl).elim
          | false =>
              simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
              subst reached
              rw [chosen]
              left
              refine Or.inl ⟨rfl, ?_⟩
              rw [base_entry]
              simp [revealSuccessor, OwnAction.disclosure]
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases owesFailure_of_deviation who next admission rest intended.2 joint action chosen
            acts available new after supported with indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end Vegas.SourceProgram.ProtocolState
