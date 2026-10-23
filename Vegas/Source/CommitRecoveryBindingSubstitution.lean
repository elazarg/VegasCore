/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.BindingRepairTrace
import Vegas.Source.CommitRecoveryPublicReadback

/-! # Virtual domain bindings along actual recovery instructions -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- A reset may combine the saved semantic fields with the current attempted
words. The same replacement relation is retained without reconstructing a
private word from its erased observation. -/
theorem FocalRepair.withHistories {who : Player} {Γ : SourceCtx Player L}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (past changed : History Player L)
    (foreign : ∀ other, other ≠ who → changed other = past other) :
    FocalRepair who { original with history := past } { repaired with history := changed } := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  let fixed : PatchMap who Γ := fun selected _ =>
    patched selected (sourceObserve who repaired.state, repaired.history who)
  refine ⟨fun _ => (sourceObserve who original.state, past who), fixed, ?_, registry, revelations⟩
  exact ⟨invariant.publicEq, invariant.inputEq, invariant.publicationEq,
    invariant.foreignEq, invariant.replacedEq, invariant.keptEq, foreign, rfl⟩

omit [IExpr.ResultTypes L] in
/-- An excluded automatic slot creates neither a declaration nor a guard.
Its failed cell remains automatic even when other focal cells were replaced. -/
theorem FocalRepair.automaticCommit {who : Player} {Γ : SourceCtx Player L}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (name : VarId) (owner : Player) (payload : L.Ty) :
    FocalRepair who (SourceProgram.automaticCommit name owner payload original)
      (SourceProgram.automaticCommit name owner payload repaired) := by
  obtain ⟨unpatch, patched, invariant, registry, revelations⟩ := related
  let fixed : PatchMap who ((name, .commitment owner payload) :: Γ) := fun selected _ =>
    match selected with
    | .here => false
    | .there prior => patched prior (sourceObserve who repaired.state, repaired.history who)
  refine ⟨fun _ => (SourceProgram.automaticCommit name owner payload original).view who, fixed, ?_,
    congrArg Registry.weaken registry, congrArg Revelations.weaken revelations⟩
  constructor
  · intro _ _ selected
    cases selected with | there selected => exact invariant.publicEq selected
  · intro _ _ _ selected
    cases selected with | there selected => exact invariant.inputEq selected
  · intro _ _ selected
    cases selected with | there selected => exact invariant.publicationEq selected
  · intro _ _ _ selected outside
    cases selected with
    | here => rfl
    | there selected => exact invariant.foreignEq selected outside
  · intro _ _ selected changed
    cases selected with
    | here => cases changed
    | there selected => exact invariant.replacedEq selected changed
  · intro _ _ selected unchanged
    cases selected with
    | here => rfl
    | there selected => exact invariant.keptEq selected unchanged
  · exact invariant.historyEq
  · rfl

omit [IExpr.ResultTypes L] in
/-- All actual public cells agree under the virtual replacement relation. -/
theorem FocalRepair.publicOnly {who : Player} {Γ : SourceCtx Player L}
    {original repaired : Config Player L Γ} (related : FocalRepair who original repaired)
    (observer : Player) : (repaired.view observer).1.publicOnly =
      (original.view observer).1.publicOnly := by
  obtain ⟨_, _, invariant, _, _⟩ := related
  apply congrArg SourceObservation.mk
  funext name cell selected
  cases cell with
  | publicData => exact invariant.publicEq selected
  | publication => exact invariant.publicationEq selected
  | privateInput => rfl
  | commitment => rfl

end Config

namespace ProtocolState

/-- The existing repair changes values, never the program point, owner,
remaining instruction count or maximal commitment interval. -/
theorem FocalRepair.control (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), FocalRepair who program original repaired →
      remaining program repaired = remaining program original ∧
      actor program repaired = actor program original ∧
      atCommit program repaired = atCommit program original ∧
      commitEnd program repaired = commitEnd program original ∧
      commitOwners program repaired = commitOwners program original := by
  intro Γ O program
  induction program with
  | ret => intro original repaired related; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | sample name fresh law next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related
  | commit name owner fresh guard next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related

/-- Saved fields can be restored with the attempted histories. Only foreign
history equality is needed; the focal player's voided words remain genuine. -/
theorem FocalRepair.withHistories (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), FocalRepair who program original repaired →
      ∀ past changed, (∀ other, other ≠ who → changed other = past other) →
      FocalRepair who program (withHistory program original past)
        (withHistory program repaired changed) := by
  intro Γ O program
  induction program with
  | ret =>
      intro original repaired related past changed foreign
      exact Config.FocalRepair.withHistories related past changed foreign
  | sample name fresh law next ih =>
      intro original repaired related past changed foreign
      cases original <;> cases repaired
      · exact Config.FocalRepair.withHistories related past changed foreign
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related past changed foreign
  | commit name owner fresh guard next ih =>
      intro original repaired related past changed foreign
      cases original <;> cases repaired
      · exact Config.FocalRepair.withHistories related past changed foreign
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related past changed foreign
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related past changed foreign
      cases original <;> cases repaired
      · exact Config.FocalRepair.withHistories related past changed foreign
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related past changed foreign

/-- Foreign complete attempted words are preserved, including through restores. -/
theorem FocalRepair.foreign_history (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), FocalRepair who program original repaired →
      ∀ observer, observer ≠ who →
        history program repaired observer = history program original observer :=
  by
  intro Γ O program
  induction program with
  | ret =>
      intro original repaired related observer outside
      obtain ⟨_, _, invariant, _, _⟩ := related
      exact invariant.historyEq observer outside
  | sample name fresh law next ih =>
      intro original repaired related observer outside
      cases original <;> cases repaired
      · obtain ⟨_, _, invariant, _, _⟩ := related
        exact invariant.historyEq observer outside
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related observer outside
  | commit name owner fresh guard next ih =>
      intro original repaired related observer outside
      cases original <;> cases repaired
      · obtain ⟨_, _, invariant, _, _⟩ := related
        exact invariant.historyEq observer outside
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related observer outside
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related observer outside
      cases original <;> cases repaired
      · obtain ⟨_, _, invariant, _, _⟩ := related
        exact invariant.historyEq observer outside
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related observer outside

/-- Automatic exhaustion rebuilds the same private-only syntax and preserves
existing virtual replacements in the saved entry. -/
theorem FocalRepair.automaticCommitBlock (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), FocalRepair who program original repaired →
      FocalRepair who program (automaticCommitBlock program original)
        (automaticCommitBlock program repaired) := by
  intro Γ O program
  induction program with
  | ret => intro original repaired related; exact related
  | sample name fresh law next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact related
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related
  | commit name owner fresh guard next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact ih _ _ (focalRepair_entry who next (related.automaticCommit name owner _))
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related
      cases original <;> cases repaired
      · exact related
      · exact related.elim
      · exact related.elim
      · exact ih _ _ related

/-- All public typed source observations, including their exact cursor, agree. -/
theorem FocalRepair.publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), FocalRepair who program original repaired →
      ∀ observer, ProtocolView.publicOnly observer program (observe observer program repaired) =
        ProtocolView.publicOnly observer program (observe observer program original) := by
  intro Γ O program
  induction program with
  | ret =>
      intro original repaired related observer
      exact congrArg (fun view => (view, [])) (Config.FocalRepair.publicOnly related observer)
  | sample name fresh law next ih =>
      intro original repaired related observer
      cases original <;> cases repaired
      · exact congrArg (fun view => Sum.inl (view, []))
          (Config.FocalRepair.publicOnly related observer)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (ih _ _ related observer)
  | commit name owner fresh guard next ih =>
      intro original repaired related observer
      cases original <;> cases repaired
      · exact congrArg (fun view => Sum.inl (view, []))
          (Config.FocalRepair.publicOnly related observer)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (ih _ _ related observer)
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired related observer
      cases original <;> cases repaired
      · exact congrArg (fun view => Sum.inl (view, []))
          (Config.FocalRepair.publicOnly related observer)
      · exact related.elim
      · exact related.elim
      · exact congrArg Sum.inr (ih _ _ related observer)

end ProtocolState

namespace CommitRecoveryState

/-- The saved and current recovery fields share one actual binding repair.
Exclusions and the full occurrence identity remain the original ones. -/
structure FocalRepair {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} (who : Player)
    (original repaired : CommitRecoveryState program) : Prop where
  point : ProtocolState.FocalRepair who program original.point repaired.point
  saved : ProtocolState.FocalRepair who program original.saved repaired.saved
  excluded : repaired.excluded = original.excluded
  entryExcluded : repaired.entryExcluded = original.entryExcluded
  generation : repaired.generation = original.generation

/-- Closing takes the same clean, retry or exhausted branch, while carrying
literal attempted words from the paired current states into the saved fields. -/
theorem FocalRepair.close {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {who : Player}
    {original repaired : CommitRecoveryState program}
    (related : FocalRepair who original repaired) :
    FocalRepair who original.close repaired.close := by
  have current := ProtocolState.FocalRepair.control who program _ _ related.point
  have saved := ProtocolState.FocalRepair.control who program _ _ related.saved
  have restored : ProtocolState.FocalRepair who program original.restored repaired.restored :=
    ProtocolState.FocalRepair.withHistories who program _ _ related.saved _ _
      (ProtocolState.FocalRepair.foreign_history who program _ _ related.point)
  have complete : repaired.Finished ↔ original.Finished := by
    simp only [Finished, current.1, saved.2.2.1, saved.2.2.2.1]
  have failure : repaired.NewFailure ↔ original.NewFailure := by
    simp only [NewFailure, related.excluded, related.entryExcluded]
  have survivor : repaired.Survives ↔ original.Survives := by
    simp only [Survives, saved.2.2.2.2, related.excluded]
  have pairedPoint (first second : ProtocolState program)
      (paired : ProtocolState.FocalRepair who program first second) :
      FocalRepair who (atPoint first original.excluded original.generation)
        (atPoint second repaired.excluded repaired.generation) :=
    ⟨paired, paired, related.excluded, related.excluded, related.generation⟩
  by_cases finished : original.Finished
  · have finished' := complete.mpr finished
    by_cases failed : original.NewFailure
    · have failed' := failure.mpr failed
      by_cases survives : original.Survives
      · have survives' := survivor.mpr survives
        simp only [CommitRecoveryState.close, finished, finished', failed, failed',
          survives, survives', ↓reduceIte]
        exact ⟨restored, restored, related.excluded, related.excluded,
          congrArg (· + 1) related.generation⟩
      · have survives' : ¬ repaired.Survives := fun yes => survives (survivor.mp yes)
        simp only [CommitRecoveryState.close, finished, finished', failed, failed',
          survives, survives', ↓reduceIte]
        exact pairedPoint _ _
          (ProtocolState.FocalRepair.automaticCommitBlock who program _ _ restored)
    · have failed' : ¬ repaired.NewFailure := fun yes => failed (failure.mp yes)
      simp only [CommitRecoveryState.close, finished, finished', failed, failed',
        ↓reduceIte]
      exact pairedPoint _ _ related.point
  · have finished' : ¬ repaired.Finished := fun yes => finished (complete.mp yes)
    by_cases committing : ProtocolState.atCommit program original.saved = true
    · have committing' : ProtocolState.atCommit program repaired.saved = true := by
        rw [saved.2.2.1, committing]
      simpa only [CommitRecoveryState.close, finished, finished', committing, committing',
        ↓reduceIte] using related
    · have committing' : ProtocolState.atCommit program repaired.saved ≠ true := by
        rwa [saved.2.2.1]
      simp only [CommitRecoveryState.close, finished, finished', committing, committing',
        ↓reduceIte]
      exact pairedPoint _ _ related.point

end CommitRecoveryState

end Vegas.SourceProgram
