/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryDebt
import Vegas.Source.IntendedForPlayer

/-! # Guard-safe play through actual source recovery

The existing player-specific validity predicate survives arbitrary foreign
actions, automatic foreign slots, and the real checkpoint close.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
theorem IntendedFor.automaticCommit_other {Γ : SourceCtx Player L} {O : Finset VarId}
    {who owner : Player} {name : VarId} {payload : L.Ty} {config : Config Player L Γ}
    (intended : config.IntendedFor who O) (fresh : name ∉ Γ.map Prod.fst)
    (different : owner ≠ who) :
    (automaticCommit name owner payload config).IntendedFor who (insert name O) where
  unique := List.nodup_cons.mpr ⟨fresh, intended.unique⟩
  accounted := Accounted.commit fresh intended.accounted
  bound cell := by
    cases cell with
    | here => exact (different rfl).elim
    | there cell => exact intended.bound cell
  publishes := PublishesBindings.weaken _ intended.publishes
  predicted := by
    intro obligation member own value bound
    obtain ⟨original, kept, rfl⟩ := List.mem_map.mp member
    exact (SourceGuard.predicts_weaken _ _ _ _).trans
      (intended.predicted original kept own value bound)

omit [IExpr.ResultTypes L] in
theorem intendedFor_withHistory {Γ : SourceCtx Player L} {O : Finset VarId} (who : Player)
    (config : Config Player L Γ) (past : History Player L) :
    IntendedFor who O { config with history := past } ↔ IntendedFor who O config :=
  ⟨fun valid => ⟨valid.unique, valid.accounted, valid.bound, valid.publishes, valid.predicted⟩,
    fun valid => ⟨valid.unique, valid.accounted, valid.bound, valid.publishes, valid.predicted⟩⟩

end Config

namespace ProtocolView

/-- The current guard admits a predicted value. This is a local observation
property, without an intended-reachability restriction or a total-menu fallback. -/
def guardSatisfiable (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → Prop
  | _, _, .ret _, _ => True
  | _, _, .sample _ _ _ next, view => view.elim (fun _ => True) (guardSatisfiable who next)
  | _, _, .commit _ _ _ guard next, view => view.elim
      (fun before => (predictedValues who guard before.1).Nonempty) (guardSatisfiable who next)
  | _, _, .reveal _ _ _ _ _ _ next, view =>
      view.elim (fun _ => True) (guardSatisfiable who next)

end ProtocolView

namespace ProtocolState

theorem intendedFor_withHistory (who : Player) : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    IntendedFor who program (withHistory program point past) ↔ IntendedFor who program point
  | _, _, .ret _, config, past => Config.intendedFor_withHistory who config past
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => exact Config.intendedFor_withHistory who _ past
      | inr point => exact intendedFor_withHistory who next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => exact Config.intendedFor_withHistory who _ past
      | inr point => exact intendedFor_withHistory who next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => exact Config.intendedFor_withHistory who _ past
      | inr point => exact intendedFor_withHistory who next point past

/-- Actual recovery retains every safe own obligation under arbitrary foreign
moves, including excluded automatic slots. Only the focal intended move and
the current guard's satisfiability are required. -/
theorem intendedFor_recoveryStep (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (excluded : Finset Player) (joint : Player → Option (CommitRecoveryMove Player L))
    (result : ProtocolState program × Finset Player),
    IntendedFor who program point → who ∉ excluded →
    ProtocolView.guardSatisfiable who program (observe who program point) →
    ProtocolView.intendedMenu who program (observe who program point)
      ((joint who).map (·.action)) →
    result ∈ (recoveryStep program point excluded joint).support →
    IntendedFor who program result.1
  | _, _, .ret _, _, _, _, _, intended, _, _, _, reached => by
      rw [recoveryStep, PMF.mem_support_pure_iff] at reached
      cases reached
      exact intended
  | _, _, .sample _ fresh _ next, point, excluded, joint, result,
      intended, active, satisfiable, legal, reached => by
      cases point with
      | inl config =>
          simp only [recoveryStep, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact intendedFor_entry next _ (Config.IntendedFor.sample intended fresh value)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intendedFor_recoveryStep who next point excluded joint after
            intended active satisfiable legal supported
  | _, _, .commit (payload := payload) name owner fresh guard next, point, excluded,
      joint, result, intended, active, satisfiable, legal, reached => by
      cases point with
      | inl config =>
          by_cases same : owner = who
          · subst who
            simp only [recoveryStep, Sum.elim_inl, active, ↓reduceIte,
              PMF.mem_support_pure_iff] at reached
            cases reached
            have offered := legal
            change ProtocolView.intendedMenu owner (.commit name owner fresh guard next)
              (Sum.inl (sourceObserve owner config.state, config.history owner))
              ((joint owner).map (·.action)) at offered
            cases chosen : (joint owner).map (·.action) with
            | none => simp [ProtocolView.intendedMenu, ProtocolView.actor, chosen] at offered
            | some action =>
                rw [chosen] at offered
                obtain ⟨_, value, member, actionEq⟩ := offered
                have accepted : guard.predicts (sourceObserve owner config.state) value = true := by
                  obtain ⟨witness, predicted⟩ := satisfiable
                  exact (mem_intendedValues_self guard _
                    ⟨witness, (mem_predictedValues_self guard _ _).mp predicted⟩ value).mp member
                rw [actionEq, OwnAction.binding_commit]
                exact intendedFor_entry next _
                  (Config.IntendedFor.commit_own intended fresh guard value accepted)
          · simp only [recoveryStep, Sum.elim_inl] at reached
            split at reached
            · rw [PMF.mem_support_pure_iff] at reached
              cases reached
              exact intendedFor_entry next _
                (Config.IntendedFor.automaticCommit_other intended fresh same)
            · rw [PMF.mem_support_pure_iff] at reached
              cases reached
              exact intendedFor_entry next _
                (Config.IntendedFor.commit_other intended fresh guard same _)
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intendedFor_recoveryStep who next point excluded joint after
            intended active satisfiable legal supported
  | _, _, .reveal published owner name fresh source unresolved next, point, excluded,
      joint, result, intended, active, satisfiable, legal, reached => by
      cases point with
      | inl config =>
          by_cases same : owner = who
          · subst who
            have opening : OwnAction.disclosure ((joint owner).map (·.action)) = true := by
              cases chosen : (joint owner).map (·.action) with
              | none =>
                  simp [ProtocolView.intendedMenu, ProtocolView.actor, observe, chosen] at legal
              | some action =>
                  rw [chosen] at legal
                  have actionEq : action = .reveal owner name true := legal.2
                  rw [actionEq]
                  rfl
            simp only [recoveryStep, Sum.elim_inl, active, ↓reduceIte, opening,
              PMF.mem_support_pure_iff] at reached
            cases reached
            exact intendedFor_entry next _ (Config.IntendedFor.reveal_own intended fresh source).1
          · simp only [recoveryStep, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
            cases reached
            apply intendedFor_entry next
            by_cases inactive : owner ∈ excluded
            · simp only [inactive, ↓reduceIte]
              exact (Config.intendedFor_withHistory who _ _).mpr
                (Config.IntendedFor.reveal_other intended fresh source same false)
            · simp only [inactive, ↓reduceIte]
              exact Config.IntendedFor.reveal_other intended fresh source same _
      | inr point =>
          simp only [recoveryStep, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact intendedFor_recoveryStep who next point excluded joint after
            intended active satisfiable legal supported

theorem commitOwners_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    commitOwners program (entry program config) = (commitPhase program).block.owners := by
  cases program <;> rfl

theorem commitOwners_withHistory : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program)
    (past : History Player L),
    commitOwners program (withHistory program point past) = commitOwners program point
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past
  | _, _, .commit _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past
  | _, _, .reveal _ _ _ _ _ _ next, point, past => by
      cases point with
      | inl _ => rfl
      | inr point => exact commitOwners_withHistory next point past

/-- Automatic exhaustion cannot harm a player outside the exhausted block. -/
theorem intendedFor_automaticCommitBlock (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : ProtocolState program),
    IntendedFor who program point → who ∉ commitOwners program point →
    IntendedFor who program (automaticCommitBlock program point)
  | _, _, .ret _, _, intended, _ => intended
  | _, _, .sample _ _ _ next, point, intended, outside => by
      cases point with
      | inl _ => exact intended
      | inr point => exact intendedFor_automaticCommitBlock who next point intended outside
  | _, _, .commit name owner fresh _ next, point, intended, outside => by
      cases point with
      | inl config =>
          have absent : who ∉ insert owner (commitPhase next).block.owners := outside
          have different : owner ≠ who := fun equal => absent (equal ▸ Finset.mem_insert_self _ _)
          apply intendedFor_automaticCommitBlock who next
          · exact intendedFor_entry next _
              (Config.IntendedFor.automaticCommit_other intended fresh different)
          · rw [commitOwners_entry]
            exact fun member => absent (Finset.mem_insert_of_mem member)
      | inr point => exact intendedFor_automaticCommitBlock who next point intended outside
  | _, _, .reveal _ _ _ _ _ _ next, point, intended, outside => by
      cases point with
      | inl _ => exact intended
      | inr point => exact intendedFor_automaticCommitBlock who next point intended outside

end ProtocolState

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- A surviving player's safe checkpoint and current obligations remain safe
under the actual retry, clean, unfinished and exhausted close. -/
theorem close_preserves_intendedFor (who : Player) (state : CommitRecoveryState program)
    (saved : ProtocolState.IntendedFor who program state.saved)
    (live : ProtocolState.IntendedFor who program state.point) (active : who ∉ state.excluded) :
    ProtocolState.IntendedFor who program state.close.saved ∧
      ProtocolState.IntendedFor who program state.close.point := by
  have restored : ProtocolState.IntendedFor who program state.restored :=
    (ProtocolState.intendedFor_withHistory who program state.saved _).mpr saved
  unfold close
  split
  · split
    · split
      · exact ⟨restored, restored⟩
      · next exhausted =>
        have outside : who ∉ ProtocolState.commitOwners program state.restored := by
          rw [CommitRecoveryState.restored, ProtocolState.commitOwners_withHistory]
          exact fun member => exhausted ⟨who, Finset.mem_sdiff.mpr ⟨member, active⟩⟩
        have valid := ProtocolState.intendedFor_automaticCommitBlock who program _ restored outside
        exact ⟨valid, valid⟩
    · exact ⟨live, live⟩
  · split
    · exact ⟨saved, live⟩
    · exact ⟨live, live⟩

/-- One real recovery transition preserves a surviving player's safe current
and saved obligations without restricting foreign actions or exclusions. -/
theorem step_preserves_intendedFor (who : Player) (state : CommitRecoveryState program)
    (saved : ProtocolState.IntendedFor who program state.saved)
    (live : ProtocolState.IntendedFor who program state.point)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (satisfiable : ProtocolView.guardSatisfiable who program
      (ProtocolState.observe who program state.point))
    (legal : ProtocolView.intendedMenu who program (ProtocolState.observe who program state.point)
      ((joint who).map (·.action)))
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support)
    (active : who ∉ next.excluded) :
    ProtocolState.IntendedFor who program next.saved ∧
      ProtocolState.IntendedFor who program next.point := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  rw [close_excluded] at active
  have raw : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  exact (state.install result.1 result.2).close_preserves_intendedFor who saved
    (ProtocolState.intendedFor_recoveryStep who program state.point state.excluded joint result.1
      live (fun member => active (result.2 member)) satisfiable legal raw) active

end CommitRecoveryState
end Vegas.SourceProgram
