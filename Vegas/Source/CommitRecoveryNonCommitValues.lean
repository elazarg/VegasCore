/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryAttemptReadout

/-! # Existing binding values survive public source instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem sample_bindingsHoldValues {Γ : SourceCtx Player L}
    (who : Player) (name : VarId) (config : Config Player L Γ)
    {payload : L.Ty} (value : L.Val payload) (live : config.BindingsHoldValues who) :
    (sampleSuccessor name config value).BindingsHoldValues who := by
  intro selected ty cell
  cases cell with
  | there cell => exact live cell

omit [IExpr.ResultTypes L] in
private theorem reveal_bindingsHoldValues {Γ : SourceCtx Player L}
    (who : Player) (published : VarId) {owner : Player} {name : VarId} {payload : L.Ty}
    (selected : HasVar Γ name (.commitment owner payload)) (config : Config Player L Γ)
    (disclose : Bool) (live : config.BindingsHoldValues who) :
    (revealSuccessor published selected config disclose).BindingsHoldValues who := by
  intro selected ty cell
  cases cell with
  | there cell => exact live cell

/-- A real sample or publication instruction retains every existing typed
binding value, regardless of its disclosure bit, guard result or exclusions. -/
theorem ProtocolState.recoveryStep_noncommit_bindingsHoldValues :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player) (who : Player),
    atCommit program point = false → BindingsHoldValues who program point →
    result ∈ (recoveryStep program point excluded joint).support →
      BindingsHoldValues who program result.1 := by
  intro Γ O program
  induction program with
  | ret payoff =>
      intro point excluded joint result who _notCommit live supported
      cases (PMF.mem_support_pure_iff _ _).mp supported
      exact live
  | sample name fresh law next ih =>
      intro point excluded joint result who notCommit live supported
      cases point with
      | inl config =>
          obtain ⟨value, _sampled, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact (ProtocolState.bindingsHoldValues_entry who next _).mpr
            (sample_bindingsHoldValues who name config value live)
      | inr later =>
          obtain ⟨target, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih later excluded joint target who notCommit live member
  | commit name owner fresh guard next ih =>
      intro point excluded joint result who notCommit live supported
      cases point with
      | inl config => cases notCommit
      | inr later =>
          obtain ⟨target, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih later excluded joint target who notCommit live member
  | reveal published owner name fresh selected unresolved next ih =>
      intro point excluded joint result who notCommit live supported
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at supported
          cases supported
          apply (ProtocolState.bindingsHoldValues_entry who next _).mpr
          by_cases inactive : owner ∈ excluded
          · simpa only [inactive, ↓reduceIte] using
              reveal_bindingsHoldValues who published selected config false live
          · simpa only [inactive, ↓reduceIte] using
              reveal_bindingsHoldValues who published selected config
                (OwnAction.disclosure ((joint owner).map (·.action))) live
      | inr later =>
          obtain ⟨target, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact ih later excluded joint target who notCommit live member

/-- Along the same actual noncommitment path, a surviving owner's initial
successful bindings remain successful at the final typed source cursor. -/
theorem ProtocolState.noncommit_path_bindingsHoldValues
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O)
    {relation : (ProtocolState program × Finset Player) →
      (ProtocolState program × Finset Player) → Prop}
    (steps : ∀ first last, relation first last →
      atCommit program first.1 = false ∧
      ∃ joint, last ∈ (recoveryStep program first.1 first.2 joint).support)
    (first last : ProtocolState program × Finset Player)
    (path : Relation.ReflTransGen relation first last) (who : Player)
    (initial : who ∉ first.2 → BindingsHoldValues who program first.1)
    (survives : who ∉ last.2) : BindingsHoldValues who program last.1 := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact initial survives
  | @head first middle moved _remaining ih =>
      obtain ⟨notCommit, joint, supported⟩ := steps first middle moved
      apply ih
      intro active
      apply recoveryStep_noncommit_bindingsHoldValues program first.1 first.2 joint middle who
        notCommit (initial (fun absent => active
          (recoveryStep_excluded_monotone program first.1 first.2 joint middle supported absent)))
        supported

end Vegas.SourceProgram
