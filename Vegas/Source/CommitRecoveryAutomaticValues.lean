/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryNonCommitValues
import Vegas.Source.CommitRecoveryCommitEntry
import Vegas.Source.CommitRecoveryNoMissInformation
import Vegas.Source.CommitRecoveryValueMenu

/-! # Surviving live values through inherited-exclusion commitment rows -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An automatic commitment for an already excluded actor preserves every
surviving owner's proper live fields; its newly appended failure is foreign. -/
theorem ProtocolState.recoveryStep_excluded_commit_bindingsHoldValues
    {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player) (who owner : Player)
    (unique : (Γ.map Prod.fst).Nodup) (committing : atCommit program point = true)
    (acting : actor program point = some owner) (absent : owner ∈ excluded)
    (survives : who ∉ excluded) (live : BindingsHoldValues who program point)
    (supported : result ∈ (recoveryStep program point excluded joint).support) :
    BindingsHoldValues who program result.1 := by
  classical
  obtain ⟨Δ, P, name, actualOwner, payload, fresh, guard, suffix, lift, entry,
    origin, atEntry, _names⟩ := exists_committing_entry program point unique committing
  subst point
  have ownerEq : actualOwner = owner := by
    have observed := origin.actor_lift
      (ProtocolState.entry (.commit name actualOwner fresh guard suffix) entry)
    exact Option.some.inj (observed.symm.trans acting)
  subst actualOwner
  have localLive : entry.BindingsHoldValues who :=
    (origin.bindingsHoldValues_lift who
      (ProtocolState.entry (.commit name owner fresh guard suffix) entry)).mp live
  rw [origin.recoveryStep_lift] at supported
  obtain ⟨target, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  simp only [recoveryStep, ProtocolState.entry, Sum.elim_inl, absent, ↓reduceIte,
    PMF.mem_support_pure_iff] at member
  subst target
  apply (origin.bindingsHoldValues_lift who _).mpr
  apply (bindingsHoldValues_entry who suffix _).mpr
  intro selected ty cell
  cases cell with
  | here => exact (survives absent).elim
  | there cell => exact localLive cell

end Vegas.SourceProgram
