/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryPoint
import Vegas.Source.Exclusion

/-! # Source recovery steps with distinct omissions and latent bad bindings -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A binding omission is distinct from an accepted binding with an unusable
typed result. Only the former excludes its owner before the reveal. -/
structure CommitRecoveryMove (Player : Type) (L : IExpr) where
  action : OwnAction Player L
  missing : Bool

namespace CommitRecoveryMove

def underlying (move : Option (CommitRecoveryMove Player L)) : Option (OwnAction Player L) :=
  move.map (·.action)

def missed (move : Option (CommitRecoveryMove Player L)) : Bool :=
  move.elim false (·.missing)

end CommitRecoveryMove

namespace ProtocolView

def atCommit (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → Bool
  | _, _, .ret _, _ => false
  | _, _, .sample _ _ _ next, view => view.elim (fun _ => false) (atCommit who next)
  | _, _, .commit _ _ _ _ next, view => view.elim (fun _ => true) (atCommit who next)
  | _, _, .reveal _ _ _ _ _ _ next, view => view.elim (fun _ => false) (atCommit who next)

/-- The original typed source menu, with physical omission allowed only for a
failed binding. Reveal moves have no separate omission marker. -/
def recoveryAvailable (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (view : ProtocolView who program) :
    Set (CommitRecoveryMove Player L) :=
  {move | move.action ∈ available who program (CommitmentInterface.forfeiture program) view ∧
    (if atCommit who program view then move.missing = true → move.action.IsFailure
      else move.missing = false)}

end ProtocolView

namespace ProtocolState

@[simp] theorem atCommit_observe : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) (who : Player),
    ProtocolView.atCommit who program (observe who program state) = atCommit program state
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact atCommit_observe next state who
  | _, _, .commit _ _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact atCommit_observe next state who
  | _, _, .reveal _ _ _ _ _ _ next, state, who => by
      cases state with
      | inl _ =>
          exact rfl
      | inr state =>
          exact atCommit_observe next state who

/-- One typed source instruction. Excluded owners fail automatically without
recording an owned action; accepted bad bindings remain latent. -/
def recoveryStep : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Finset Player →
    (Player → Option (CommitRecoveryMove Player L)) → PMF (ProtocolState program × Finset Player)
  | _, _, .ret _, config, excluded, _ => PMF.pure (config, excluded)
  | _, _, .sample name _ law next, state, excluded, joint => state.elim
      (fun config => (L.evalDist law (sourcePublicEnv config.state)).map fun value =>
        (Sum.inr (entry next (sampleSuccessor name config value)), excluded))
      (fun later => (recoveryStep next later excluded joint).map
        (fun result => (Sum.inr result.1, result.2)))
  | _, _, .commit (payload := payload) name owner _ guard next, state, excluded, joint =>
      state.elim
        (fun config => if owner ∈ excluded then
          PMF.pure (Sum.inr (entry next (automaticCommit name owner payload config)), excluded)
        else PMF.pure
          (Sum.inr (entry next (commitSuccessor name guard config
            (OwnAction.binding owner name payload ((joint owner).map (·.action))))),
            if CommitRecoveryMove.missed (joint owner) then insert owner excluded else excluded))
        (fun later => (recoveryStep next later excluded joint).map
          (fun result => (Sum.inr result.1, result.2)))
  | _, _, .reveal published owner _ _ source _ next, state, excluded, joint => state.elim
      (fun config =>
        let result := revealSuccessor published source config
          (if owner ∈ excluded then false else
            OwnAction.disclosure ((joint owner).map (·.action)))
        let kept := if owner ∈ excluded then { result with history := config.history } else result
        PMF.pure (Sum.inr (entry next kept), match result.state.get .here with
          | .failure => insert owner excluded
          | .success _ => excluded))
      (fun later => (recoveryStep next later excluded joint).map
        (fun result => (Sum.inr result.1, result.2)))

theorem recoveryStep_excluded_monotone : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    result ∈ (recoveryStep program point excluded joint).support → excluded ⊆ result.2
  | _, _, .ret _, _, _, _, _, supported => by
      simp only [recoveryStep, PMF.mem_support_pure_iff] at supported
      subst supported
      exact Finset.Subset.refl _
  | _, _, .sample _ _ _ next, state, excluded, joint, _, supported => by
      cases state with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact Finset.Subset.refl _
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_excluded_monotone next state excluded joint result member
  | _, _, .commit _ _ _ _ next, state, excluded, joint, _, supported => by
      cases state with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl] at supported
          split at supported
          · rw [PMF.mem_support_pure_iff] at supported
            subst supported
            exact Finset.Subset.refl _
          · rw [PMF.mem_support_pure_iff] at supported
            subst supported
            split
            · exact Finset.subset_insert _ _
            · exact Finset.Subset.refl _
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_excluded_monotone next state excluded joint result member
  | _, _, .reveal _ _ _ _ _ _ next, state, excluded, joint, _, supported => by
      cases state with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          subst supported
          dsimp only
          split
          · exact Finset.subset_insert _ _
          · exact Finset.Subset.refl _
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_excluded_monotone next state excluded joint result member

theorem recoveryStep_remaining : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    ¬ terminal program point → result ∈ (recoveryStep program point excluded joint).support →
      remaining program result.1 + 1 = remaining program point
  | _, _, .ret _, _, _, _, _, running, _ => (running trivial).elim
  | _, _, .sample _ _ _ next, state, excluded, joint, _, running, supported => by
      cases state with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          simp only [remaining, Sum.elim_inr, Sum.elim_inl, remaining_entry]
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_remaining next state excluded joint result running member
  | _, _, .commit _ _ _ _ next, state, excluded, joint, _, running, supported => by
      cases state with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl] at supported
          split at supported <;> rw [PMF.mem_support_pure_iff] at supported <;> subst supported <;>
            simp only [remaining, Sum.elim_inr, Sum.elim_inl, remaining_entry]
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_remaining next state excluded joint result running member
  | _, _, .reveal _ _ _ _ _ _ next, state, excluded, joint, _, running, supported => by
      cases state with
      | inl _ =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          subst supported
          simp only [remaining, Sum.elim_inr, Sum.elim_inl, remaining_entry]
      | inr state =>
          obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact recoveryStep_remaining next state excluded joint result running member

end ProtocolState
end Vegas.SourceProgram
