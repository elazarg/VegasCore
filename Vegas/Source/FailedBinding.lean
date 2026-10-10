/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedPlay

/-! # Irrevocable failed bindings force an owner publication failure

A failed commitment remains unresolved until its own reveal. Other source
actions cannot repair it. Every terminal continuation contains a failed reveal
of its owner, independently of guards, later policies and chance outcomes.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

variable {Γ : SourceCtx Player L} {unresolved : Finset VarId}

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem namesNodup_cons {name : VarId} {cell : CellTy Player L}
    (fresh : name ∉ Γ.map Prod.fst) (unique : (Γ.map Prod.fst).Nodup) :
    (((name, cell) :: Γ).map Prod.fst).Nodup := List.nodup_cons.mpr ⟨fresh, unique⟩

structure FailedBinding (who : Player) (unresolved : Finset VarId)
    (config : Config Player L Γ) : Prop where
  unique : (Γ.map Prod.fst).Nodup
  pending : ∃ (name : VarId) (payload : L.Ty)
    (source : HasVar Γ name (.commitment who payload)),
    name ∈ unresolved ∧ config.state.get source = .failure

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem FailedBinding.sample {who : Player} {name : VarId} {payload : L.Ty}
    {config : Config Player L Γ} (failed : config.FailedBinding who unresolved)
    (fresh : name ∉ Γ.map Prod.fst) (value : L.Val payload) :
    (sampleSuccessor name config value).FailedBinding who unresolved where
  unique := namesNodup_cons fresh failed.unique
  pending := by
    obtain ⟨subject, payload, source, pending, bound⟩ := failed.pending
    exact ⟨subject, payload, .there source, pending, bound⟩

omit [IExpr.ResultTypes L] in
theorem FailedBinding.commit {who owner : Player} {name : VarId} {payload : L.Ty}
    {config : Config Player L Γ} (failed : config.FailedBinding who unresolved)
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (choice : PublicationResult (L.Val payload)) :
    (commitSuccessor name guard config choice).FailedBinding who (insert name unresolved) where
  unique := namesNodup_cons fresh failed.unique
  pending := by
    obtain ⟨subject, payload, source, pending, bound⟩ := failed.pending
    exact ⟨subject, payload, .there source, Finset.mem_insert_of_mem pending, bound⟩

omit [IExpr.ResultTypes L] in
theorem failedBinding_commit {who : Player} {name : VarId} {payload : L.Ty}
    (config : Config Player L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ who name payload)
    (unresolved : Finset VarId) :
    (commitSuccessor name guard config .failure).FailedBinding who (insert name unresolved) where
  unique := namesNodup_cons fresh unique
  pending := ⟨name, payload, .here, Finset.mem_insert_self _ _, rfl⟩

omit [IExpr.ResultTypes L] in
theorem FailedBinding.reveal {who owner : Player} {payload : L.Ty} {name published : VarId}
    {config : Config Player L Γ} (failed : config.FailedBinding who unresolved)
    (fresh : published ∉ Γ.map Prod.fst) (source : HasVar Γ name (.commitment owner payload))
    (disclose : Bool) :
    (owner = who ∧ (revealSuccessor published source config disclose).state.get .here = .failure) ∨
      (revealSuccessor published source config disclose).FailedBinding who
        (unresolved.erase name) := by
  obtain ⟨subject, τ, cell, pending, bound⟩ := failed.pending
  by_cases same : subject = name
  · subst subject
    have types := HasVar.type_unique failed.unique cell source
    cases types
    have cells := HasVar.eq_of_nodup failed.unique cell source
    cases cells
    left
    refine ⟨rfl, ?_⟩
    simp [revealSuccessor, bound]
  · right
    exact { unique := namesNodup_cons fresh failed.unique
            pending := ⟨subject, τ, .there cell, Finset.mem_erase.mpr ⟨same, pending⟩, bound⟩ }

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem FailedBinding.not_resolved {who : Player} {config : Config Player L Γ}
    (failed : config.FailedBinding who ∅) : False := by
  obtain ⟨_, _, _, pending, _⟩ := failed.pending
  exact Finset.notMem_empty _ pending

end Config

namespace ProtocolState

def FailedBinding (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => Config.FailedBinding who ∅ config
  | _, O, .sample _ _ _ next => Sum.elim (Config.FailedBinding who O) (FailedBinding who next)
  | _, O, .commit _ _ _ _ next => Sum.elim (Config.FailedBinding who O) (FailedBinding who next)
  | _, O, .reveal _ owner _ _ _ _ next =>
      Sum.elim (Config.FailedBinding who O)
        (fun rest => (owner = who ∧ (base next rest).get .here = .failure) ∨
          FailedBinding who next rest)

theorem failedBinding_entry {who : Player} {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (failed : config.FailedBinding who O) : FailedBinding who program (entry program config) := by
  cases program <;> exact failed

theorem failedBinding_step (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    (joint : Player → Option (OwnAction Player L)) → (target : ProtocolState program) →
    FailedBinding who program state → target ∈ (step program state joint).support →
      FailedBinding who program target
  | _, _, .ret _, _, _, _, failed, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact failed
  | _, _, .sample _ fresh _ next, state, joint, target, failed, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact failedBinding_entry next _ (Config.FailedBinding.sample failed fresh value)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact failedBinding_step who next rest joint after failed supported
  | _, _, .commit _ _ fresh guard next, state, joint, target, failed, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact failedBinding_entry next _ (Config.FailedBinding.commit failed fresh guard _)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact failedBinding_step who next rest joint after failed supported
  | _, _, .reveal _ _ _ fresh source _ next, state, joint, target, failed, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          rcases Config.FailedBinding.reveal failed fresh source _ with forfeited | failed
          · left
            rw [base_entry]
            exact forfeited
          · exact Or.inr (failedBinding_entry next _ failed)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases failed with ⟨own, publication⟩ | failed
          · exact Or.inl ⟨own, (base_step next rest joint after supported).symm ▸ publication⟩
          · exact Or.inr (failedBinding_step who next rest joint after failed supported)

theorem failedReveals_pos_of_failedBinding (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    FailedBinding who program state → {terminal : State L program.terminalCtx} →
    readout program state = some terminal →
      1 ≤ failedReveals program who (publicOutcome program terminal)
  | _, _, .ret _, _, failed, _, _ => (Config.FailedBinding.not_resolved failed).elim
  | _, _, .sample _ _ _ next, state, failed, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_pos_of_failedBinding who next rest failed read
  | _, _, .commit _ _ _ _ next, state, failed, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest => exact failedReveals_pos_of_failedBinding who next rest failed read
  | _, _, .reveal _ _ _ _ _ _ next, state, failed, terminal, read => by
      cases state with
      | inl _ => cases read
      | inr rest =>
          rcases failed with ⟨own, publication⟩ | failed
          · have holds : terminal.get (terminalRef next .here) = .failure :=
              (terminalRef_get next terminal .here).trans
                ((congrArg (fun state => state.get .here)
                  (initialState_of_readout next rest read)).trans publication)
            subst own
            refine failedReveals_reveal_pos (publicOutcome next terminal) ?_
            simp [RevealCell.failed, publicOutcome, sourcePublicEnv_get_publicRef, holds,
              PublicationResult.isSuccess]
          · exact (failedReveals_pos_of_failedBinding who next rest failed read).trans
              (failedReveals_reveal_le who _)

end ProtocolState

end Vegas.SourceProgram
