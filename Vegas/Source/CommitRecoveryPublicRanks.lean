/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryObservedMemory
import Vegas.Source.CommitRecoveryFrontier

/-! # Public source observations retained across actual commitment closures -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- An actual accepted binding and an automatic failure have the same typed
public observation. Their private result and owned action word remain distinct. -/
theorem commit_public_eq_automatic {Γ : SourceCtx Player L}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (who : Player) (guard : SourceGuard L Γ owner name payload)
    (config : Config Player L Γ) (choice : PublicationResult (L.Val payload)) :
    ((commitSuccessor name guard config choice).view who).1.publicOnly =
      ((automaticCommit name owner payload config).view who).1.publicOnly := by
  apply congrArg SourceObservation.mk
  funext readName cell member
  cases member with
  | here => rfl
  | there member => cases cell <;> rfl

omit [IExpr.ResultTypes L] in
/-- Publicly equal saved fields remain equal after the same automatic slot. -/
theorem automaticCommit_public_congr {Γ : SourceCtx Player L}
    (who owner : Player) (name : VarId) (payload : L.Ty)
    (first second : Config Player L Γ)
    (same : (first.view who).1.publicOnly = (second.view who).1.publicOnly) :
    ((automaticCommit name owner payload first).view who).1.publicOnly =
      ((automaticCommit name owner payload second).view who).1.publicOnly := by
  apply congrArg SourceObservation.mk
  funext readName cell member
  cases member with
  | here => rfl
  | there member =>
      have old := congrArg (fun observation : SourceObservation L who Γ =>
        observation.cells readName cell member) same
      cases cell <;> exact old

end Config

namespace ProtocolView

/-- Erased public views retain the exact original source cursor. -/
@[simp] theorem position_publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (view : ProtocolView who program),
      position who program (publicOnly who program view) = position who program view := by
  intro Γ O program
  induction program with
  | ret => intro view; rfl
  | sample name fresh law next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view => exact congrArg (fun index => index + 1) (ih view)
  | commit name owner fresh guard next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view => exact congrArg (fun index => index + 1) (ih view)
  | reveal published owner name fresh selected unresolved next ih =>
      intro view
      cases view with
      | inl => rfl
      | inr view => exact congrArg (fun index => index + 1) (ih view)

end ProtocolView

/-- Both actual chunk projections preserve the observed instruction position. -/
theorem SourceViewProjection.position_apply (projection : SourceViewProjection)
    (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (view : ProtocolView who program) :
    ProtocolView.position who program (projection.apply who program view) =
      ProtocolView.position who program view := by
  cases projection with
  | memory remember => exact ProtocolView.position_historyProjection who remember program view
  | publicOnly => exact ProtocolView.position_publicOnly who program view

namespace ProtocolState

/-- The public typed cursor determines all static recovery control fields. -/
theorem public_control (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolView.publicOnly who program (observe who program first) =
        ProtocolView.publicOnly who program (observe who program second) →
      remaining program first = remaining program second ∧
        atCommit program first = atCommit program second ∧
        commitEnd program first = commitEnd program second
  | _, _, .ret _, _, _, _ => ⟨rfl, rfl, rfl⟩
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact ⟨rfl, rfl, rfl⟩
      · cases same
      · cases same
      · exact public_control who next _ _ (Sum.inr.inj same)


/-- Changing a remembered word cannot change any public typed observation. -/
theorem publicOnly_observe_withHistory (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (point : ProtocolState program) (past : History Player L) :
    ProtocolView.publicOnly who program (observe who program (withHistory program point past)) =
      ProtocolView.publicOnly who program (observe who program point) := by
  rw [← ProtocolView.publicOnly_eraseHistory who program
    (observe who program (withHistory program point past)), ProtocolView.eraseHistory_observe,
    withHistory_withHistory, ← ProtocolView.eraseHistory_observe,
    ProtocolView.publicOnly_eraseHistory]

/-- A source entry exposes the same public fields even when every private
cell and every remembered word differs. -/
theorem publicOnly_observe_entry_congr (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (first second : Config Player L Γ)
    (same : (first.view who).1.publicOnly = (second.view who).1.publicOnly) :
    ProtocolView.publicOnly who program (observe who program (entry program first)) =
      ProtocolView.publicOnly who program (observe who program (entry program second)) := by
  cases program with
  | ret => exact Prod.ext same rfl
  | sample => exact congrArg Sum.inl (Prod.ext same rfl)
  | commit => exact congrArg Sum.inl (Prod.ext same rfl)
  | reveal => exact congrArg Sum.inl (Prod.ext same rfl)

/-- Filling a commitment suffix automatically depends only on its public
entry fields. It does not recover any private binding or retired private word. -/
theorem automaticCommitBlock_public_congr (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (first second : ProtocolState program),
      ProtocolView.publicOnly who program (observe who program first) =
        ProtocolView.publicOnly who program (observe who program second) →
      ProtocolView.publicOnly who program
          (observe who program (automaticCommitBlock program first)) =
        ProtocolView.publicOnly who program
          (observe who program (automaticCommitBlock program second))
  | _, _, .ret _, _, _, same => same
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact congrArg Sum.inr
          (automaticCommitBlock_public_congr who next _ _ (Sum.inr.inj same))
  | _, _, .commit (payload := payload) name owner fresh guard next, first, second, same => by
      cases first with
      | inl first =>
          cases second with
          | inl second =>
              apply congrArg Sum.inr
              apply automaticCommitBlock_public_congr who next
              have cells := congrArg Prod.fst (Sum.inl.inj same)
              have after := Config.automaticCommit_public_congr who owner name payload first second
                cells
              exact publicOnly_observe_entry_congr who next _ _ after
          | inr second => cases same
      | inr first =>
          cases second with
          | inl second => cases same
          | inr second =>
              exact congrArg Sum.inr
                (automaticCommitBlock_public_congr who next first second (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact same
      · cases same
      · cases same
      · exact congrArg Sum.inr
          (automaticCommitBlock_public_congr who next _ _ (Sum.inr.inj same))

/-- An actual binding instruction changes no public value in the automatically
completed current block. Accepted failure and physical omission are both retained
by the original raw instruction; no legal-choice or success restriction is used. -/
theorem recoveryStep_commit_public_expansion (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program) (excluded : Finset Player)
      (joint : Player → Option (CommitRecoveryMove Player L))
      (result : ProtocolState program × Finset Player),
      atCommit program point = true → result ∈ (recoveryStep program point excluded joint).support →
      ProtocolView.publicOnly who program
          (observe who program (automaticCommitBlock program result.1)) =
        ProtocolView.publicOnly who program
          (observe who program (automaticCommitBlock program point))
  | _, _, .ret _, _, _, _, _, impossible, _ => Bool.noConfusion impossible
  | _, _, .sample _ _ _ next, point, excluded, joint, result, committing, reached => by
      cases point with
      | inl => cases committing
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact congrArg Sum.inr
            (recoveryStep_commit_public_expansion who next point excluded joint after
              committing supported)
  | _, _, .commit name owner fresh guard next, point, excluded, joint, result,
      committing, reached => by
      cases point with
      | inl config =>
          by_cases inactive : owner ∈ excluded
          · simp only [recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
              PMF.mem_support_pure_iff] at reached
            subst result
            rfl
          · simp only [recoveryStep, Sum.elim_inl, inactive, ↓reduceIte,
              PMF.mem_support_pure_iff] at reached
            subst result
            apply congrArg Sum.inr
            apply automaticCommitBlock_public_congr who next
            have cells := Config.commit_public_eq_automatic who guard config
              (OwnAction.binding owner name _ ((joint owner).map (·.action)))
            exact publicOnly_observe_entry_congr who next _ _ cells
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact congrArg Sum.inr
            (recoveryStep_commit_public_expansion who next point excluded joint after
              committing supported)
  | _, _, .reveal _ _ _ _ _ _ next, point, excluded, joint, result, committing, reached => by
      cases point with
      | inl => cases committing
      | inr point =>
          obtain ⟨after, supported, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
          exact congrArg Sum.inr
            (recoveryStep_commit_public_expansion who next point excluded joint after
              committing supported)
/-- The automatic block operation adds no second block when applied twice. -/
@[simp] theorem automaticCommitBlock_idempotent :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program),
      automaticCommitBlock program (automaticCommitBlock program point) =
        automaticCommitBlock program point := by
  intro Γ O program
  induction program with
  | ret => intro point; rfl
  | sample name fresh law next ih =>
      intro point
      cases point with
      | inl => rfl
      | inr point => exact congrArg Sum.inr (ih point)
  | commit name owner fresh guard next ih =>
      intro point
      cases point with
      | inl config =>
          exact congrArg Sum.inr (ih (entry next (automaticCommit name owner _ config)))
      | inr point => exact congrArg Sum.inr (ih point)
  | reveal published owner name fresh selected unresolved next ih =>
      intro point
      cases point with
      | inl => rfl
      | inr point => exact congrArg Sum.inr (ih point)


end ProtocolState

namespace CommitRecoveryState

/-- This relation records actual public data inside the saved maximal block.
It permits all live private choices and all old private words to differ. -/
def PublicExpansion {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) : Prop :=
  ProtocolView.publicOnly who program
      (ProtocolState.observe who program (ProtocolState.automaticCommitBlock program state.saved)) =
    ProtocolView.publicOnly who program
      (ProtocolState.observe who program (ProtocolState.automaticCommitBlock program state.point))

/-- Actual close retains every public typed field, including both restored
branches; the last instruction emits only its actual post-close target. -/
theorem close_public_expansion {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (who : Player) (valid : state.PublicExpansion who) :
    ProtocolView.publicOnly who program
        (ProtocolState.observe who program
          (ProtocolState.automaticCommitBlock program state.close.point)) =
      ProtocolView.publicOnly who program
        (ProtocolState.observe who program
          (ProtocolState.automaticCommitBlock program state.point)) := by
  have restored : ProtocolView.publicOnly who program
      (ProtocolState.observe who program (ProtocolState.automaticCommitBlock program
        state.restored)) =
    ProtocolView.publicOnly who program
      (ProtocolState.observe who program (ProtocolState.automaticCommitBlock program
        state.saved)) := by
    rw [CommitRecoveryState.restored, ProtocolState.withHistory_automaticCommitBlock,
      ProtocolState.publicOnly_observe_withHistory]
  unfold close
  split
  · split
    · split
      · exact restored.trans valid
      · simpa only [exhausted, atPoint, ProtocolState.automaticCommitBlock_idempotent]
          using restored.trans valid
    · rfl
  · split <;> rfl

/-- A real supported recovery instruction propagates the public saved/live
relation; no successful, clear, surviving or intended path is assumed. -/
theorem step_public_expansion {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (state : CommitRecoveryState program)
    (frontier : state.BlockFrontier) (who : Player) (valid : state.PublicExpansion who)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support) :
    next.PublicExpansion who := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  let image := state.install result.1 result.2
  by_cases savedCommit : ProtocolState.atCommit program state.saved = true
  · have liveCommit : ProtocolState.atCommit program state.point = true := by
      rcases frontier with ⟨_, committing, _⟩ | same
      · exact committing
      · rwa [← same]
    have after := ProtocolState.recoveryStep_commit_public_expansion who program state.point
      state.excluded joint result.1 liveCommit raw
    have imageValid : image.PublicExpansion who := valid.trans after.symm
    unfold close
    split
    · split
      · split <;> rfl
      · rfl
    · split
      · exact imageValid
      · rfl
  · change (state.install result.1 result.2).close.PublicExpansion who
    simp only [close, Finished, install, savedCommit, Bool.false_eq_true, false_and, ↓reduceIte]
    rfl

end CommitRecoveryState

namespace Setup

/-- Every actual initialized source history retains the same public typed
block image at its saved and current frontiers, across arbitrary earlier retries. -/
theorem commitRecovery_public_expansion (setup : Setup (Player := Player) (L := L))
    (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    state.elim True (fun current => current.PublicExpansion who) := by
  induction trace with
  | start => trivial
  | @extend before after prior joint _ supported ih =>
      cases before with
      | none =>
          obtain ⟨input, _member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          rfl
      | some current =>
          obtain ⟨next, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
          exact current.step_public_expansion (setup.commitRecovery_blockFrontier prior) who
            ih joint next reached

/-- A genuine binding step, including its actual final close, preserves the
whole padded public typed source image. The exact omission scan and exclusion
updates are not changed or hidden by the readback statement. -/
theorem commitRecovery_commit_public_readback
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (before after : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some before))
    (committing : ProtocolState.atCommit setup.program before.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some before) joint)
    (supported : some after ∈
      (setup.commitRecoveryProtocol.step (some before) ⟨joint, legal⟩).support) :
    ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program after.point)) =
      ProtocolView.publicOnly who setup.program
        (ProtocolState.observe who setup.program
          (ProtocolState.automaticCommitBlock setup.program before.point)) := by
  obtain ⟨target, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have targetEq : target = after := Option.some.inj same
  subst target
  obtain ⟨result, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  subst after
  have raw : result.1 ∈
      (ProtocolState.recoveryStep setup.program before.point before.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep setup.program before.point before.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone setup.program
        before.point before.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  let image := before.install result.1 result.2
  have rawPublic := ProtocolState.recoveryStep_commit_public_expansion who setup.program
    before.point before.excluded joint result.1 committing raw
  have imageValid : image.PublicExpansion who :=
    (setup.commitRecovery_public_expansion who trace).trans rawPublic.symm
  exact (image.close_public_expansion who imageValid).trans rawPublic


end Setup

end Vegas.SourceProgram
