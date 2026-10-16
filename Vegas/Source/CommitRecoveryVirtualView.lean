/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryBindingSubstitution

/-! # Deterministic typed views of virtual domain declarations -/

noncomputable section

namespace Vegas

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace SourceObservation

/-- Replace introduced unusable own declarations; original setup cells and
all public and private input cells remain literal. No sampling-tier tag is read. -/
def virtualBindings {who : Player} {Γ : SourceCtx Player L} (preserved : Finset VarId)
    (view : SourceObservation L who Γ) : SourceObservation L who Γ :=
  ⟨fun name cell selected => match cell with
    | .commitment owner payload =>
        (view.cells name (.commitment owner payload) selected).map fun binding =>
        if name ∈ preserved then binding else SourceProgram.repairBinding owner who binding
    | .publicData payload => view.cells name (.publicData payload) selected
    | .publication payload => view.cells name (.publication payload) selected
    | .privateInput owner payload => view.cells name (.privateInput owner payload) selected⟩

end SourceObservation

namespace SourceProgram

namespace Config

/-- A virtual counterpart records the exact origin-blind replacement on each
introduced binding. The original initializer's bindings are explicitly fixed. -/
structure VirtualRepair (preserved : Finset VarId) (who : Player) {Γ : SourceCtx Player L}
    (original repaired : Config Player L Γ) : Prop where
  related : FocalRepair who original repaired
  bindings : ∀ {name owner payload} (selected : HasVar Γ name (.commitment owner payload)),
    repaired.state.get selected = if name ∈ preserved then original.state.get selected
      else repairBinding owner who (original.state.get selected)

omit [IExpr.ResultTypes L] in
/-- The original supported initializer is its own virtual counterpart. -/
theorem VirtualRepair.initial (who : Player) {Γ : SourceCtx Player L}
    (config : Config Player L Γ) : VirtualRepair (Γ.map Prod.fst).toFinset who config config := by
  refine ⟨FocalRepair.refl who config, ?_⟩
  intro name owner payload selected
  rw [ite_eq_left (List.mem_toFinset.mpr selected.mem_map_fst)]

omit [IExpr.ResultTypes L] in
/-- Resetting a remembered word leaves the entire virtual typed store fixed. -/
theorem VirtualRepair.withHistories {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired) (past changed : History Player L)
    (foreign : ∀ other, other ≠ who → changed other = past other) :
    VirtualRepair preserved who { original with history := past }
      { repaired with history := changed } :=
  ⟨related.related.withHistories past changed foreign, related.bindings⟩

omit [IExpr.ResultTypes L] in
/-- A shared sample extends both exact stores with the same public cell. -/
theorem VirtualRepair.sample {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired) {payload : L.Ty}
    (name : VarId) (value : L.Val payload) :
    VirtualRepair preserved who (sampleSuccessor name original value)
      (sampleSuccessor name repaired value) := by
  refine ⟨related.related.sample name value, ?_⟩
  intro name owner payload selected
  cases selected with | there selected => exact related.bindings selected

omit [IExpr.ResultTypes L] in
/-- Actual binding translation reads the declaration, independently of which
native sampling tier emitted it. Fresh program names are not setup cells. -/
theorem VirtualRepair.commit {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired) {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload) (fresh : name ∉ preserved)
    (binding : PublicationResult (L.Val payload)) :
    VirtualRepair preserved who (commitSuccessor name guard original binding)
      (commitSuccessor name guard repaired (repairBinding owner who binding)) := by
  refine ⟨related.related.commit name guard binding, ?_⟩
  intro cellName cellOwner cellPayload selected
  cases selected with
  | here => simp only [commitSuccessor, Env.cons_get_here, fresh, ↓reduceIte]
  | there selected => exact related.bindings selected

omit [IExpr.ResultTypes L] in
/-- Automatic excluded foreign slots retain failure as an automatic result;
no declaration of the surviving owner is inserted by this operation. -/
theorem VirtualRepair.automaticCommit {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired)
    (name : VarId) (owner : Player) (payload : L.Ty) (foreign : owner ≠ who) :
    VirtualRepair preserved who (SourceProgram.automaticCommit name owner payload original)
      (SourceProgram.automaticCommit name owner payload repaired) := by
  refine ⟨related.related.automaticCommit name owner payload, ?_⟩
  intro cellName cellOwner cellPayload selected
  cases selected with
  | here => simp only [SourceProgram.automaticCommit, Env.cons_get_here, repairBinding,
      foreign, ↓reduceIte, ite_self]
  | there selected => exact related.bindings selected

omit [IExpr.ResultTypes L] in
/-- A public resolution changes no private binding cells and chooses the
existing guard-preserving translated disclosure. -/
theorem VirtualRepair.reveal {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired)
    {owner : Player} {payload : L.Ty} {name : VarId} (published : VarId)
    (source : HasVar Γ name (.commitment owner payload)) (disclose : Bool) :
    ∃ translated : Bool,
      VirtualRepair preserved who (revealSuccessor published source original disclose)
        (revealSuccessor published source repaired translated) ∧
      (owner ≠ who → translated = disclose) := by
  obtain ⟨translated, paired, foreign⟩ := related.related.reveal published source disclose
  refine ⟨translated, ⟨paired, ?_⟩, foreign⟩
  intro cellName cellOwner cellPayload selected
  cases selected with | there selected => exact related.bindings selected

omit [IExpr.ResultTypes L] in
/-- The complete current typed observation is the deterministic virtual map
of the original observation. The word is erased separately. -/
theorem VirtualRepair.observe {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {original repaired : Config Player L Γ}
    (related : VirtualRepair preserved who original repaired) :
    sourceObserve who repaired.state =
      (sourceObserve who original.state).virtualBindings preserved := by
  obtain ⟨unpatch, patched, invariant, _registry, _revelations⟩ := related.related
  apply congrArg SourceObservation.mk
  funext name cell selected
  cases cell with
  | publicData => exact invariant.publicEq selected
  | publication => exact invariant.publicationEq selected
  | privateInput owner payload =>
      simp only [sourceObserve]
      by_cases own : owner = who
      · simp only [own, ↓reduceIte]
        exact congrArg some (invariant.inputEq selected)
      · simp only [own, ↓reduceIte]
  | commitment owner payload =>
      simp only [sourceObserve]
      by_cases own : owner = who
      · simp only [own, ↓reduceIte, Option.map_some]
        exact congrArg some (by simpa only [own] using related.bindings selected)
      · simp only [own, ↓reduceIte, Option.map_none]

end Config

namespace ProtocolView

/-- The current virtual query retains its exact cursor, typed private tuple,
and all live own values, while discarding the old remembered private word. -/
def virtualBindings (who : Player) (preserved : Finset VarId) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} →
      (program : SourceProgram Player L Γ O) → ProtocolView who program → ProtocolView who program
  | _, _, .ret _, view => (view.1.virtualBindings preserved, [])
  | _, _, .sample _ _ _ next, view => view.elim
      (fun current => .inl (current.1.virtualBindings preserved, []))
      (fun later => .inr (virtualBindings who preserved next later))
  | _, _, .commit _ _ _ _ next, view => view.elim
      (fun current => .inl (current.1.virtualBindings preserved, []))
      (fun later => .inr (virtualBindings who preserved next later))
  | _, _, .reveal _ _ _ _ _ _ next, view => view.elim
      (fun current => .inl (current.1.virtualBindings preserved, []))
      (fun later => .inr (virtualBindings who preserved next later))

/-- The virtual typed query does not inspect an erased remembered word. -/
theorem virtualBindings_eraseHistory (who : Player) (preserved : Finset VarId) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (view : ProtocolView who program),
      virtualBindings who preserved program (eraseHistory who program view) =
        virtualBindings who preserved program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (virtualBindings_eraseHistory who preserved next view)
  | _, _, .commit _ _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (virtualBindings_eraseHistory who preserved next view)
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view with
      | inl => rfl
      | inr view => exact congrArg Sum.inr (virtualBindings_eraseHistory who preserved next view)

end ProtocolView

namespace ProtocolState

/-- Exact typed domain replacement at the actual source cursor. -/
def VirtualRepair (preserved : Finset VarId) (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
      ProtocolState program → ProtocolState program → Prop
  | _, _, .ret _, original, repaired => Config.VirtualRepair preserved who original repaired
  | _, _, .sample _ _ _ next, original, repaired => match original, repaired with
    | .inl first, .inl second => Config.VirtualRepair preserved who first second
    | .inr first, .inr second => VirtualRepair preserved who next first second
    | _, _ => False
  | _, _, .commit _ _ _ _ next, original, repaired => match original, repaired with
    | .inl first, .inl second => Config.VirtualRepair preserved who first second
    | .inr first, .inr second => VirtualRepair preserved who next first second
    | _, _ => False
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired => match original, repaired with
    | .inl first, .inl second => Config.VirtualRepair preserved who first second
    | .inr first, .inr second => VirtualRepair preserved who next first second
    | _, _ => False

/-- Exact virtual relations retain the existing deferred-guard repair relation. -/
theorem VirtualRepair.focalRepair (preserved : Finset VarId) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), VirtualRepair preserved who program
        original repaired → FocalRepair who program original repaired
  | _, _, .ret _, _, _, paired => paired.related
  | _, _, .sample _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact paired.related
      · exact paired.elim
      · exact paired.elim
      · exact focalRepair preserved who next _ _ paired
  | _, _, .commit _ _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact paired.related
      · exact paired.elim
      · exact paired.elim
      · exact focalRepair preserved who next _ _ paired
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact paired.related
      · exact paired.elim
      · exact paired.elim
      · exact focalRepair preserved who next _ _ paired

/-- Entering a genuine suffix retains its exact virtual typed fields. -/
theorem virtualRepair_entry (preserved : Finset VarId) (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    {original repaired : Config Player L Γ}
    (paired : Config.VirtualRepair preserved who original repaired) :
    VirtualRepair preserved who program (entry program original) (entry program repaired) := by
  cases program <;> exact paired

/-- Current virtual readback is deterministic even though old private words
and hidden foreign cells need not be reconstructed by its native caller. -/
theorem VirtualRepair.observe (preserved : Finset VarId) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), VirtualRepair preserved who program
        original repaired → ProtocolView.eraseHistory who program (observe who program repaired) =
      ProtocolView.virtualBindings who preserved program (observe who program original)
  | _, _, .ret _, _, _, paired =>
      congrArg (fun view => (view, [])) (Config.VirtualRepair.observe paired)
  | _, _, .sample _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl
          (congrArg (fun view => (view, [])) (Config.VirtualRepair.observe paired))
      · exact paired.elim
      · exact paired.elim
      · exact congrArg Sum.inr (observe preserved who next _ _ paired)
  | _, _, .commit _ _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl
          (congrArg (fun view => (view, [])) (Config.VirtualRepair.observe paired))
      · exact paired.elim
      · exact paired.elim
      · exact congrArg Sum.inr (observe preserved who next _ _ paired)
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired, paired => by
      cases original <;> cases repaired
      · exact congrArg Sum.inl
          (congrArg (fun view => (view, [])) (Config.VirtualRepair.observe paired))
      · exact paired.elim
      · exact paired.elim
      · exact congrArg Sum.inr (observe preserved who next _ _ paired)

/-- Attempted words can be carried through reset without changing the exact
virtual typed fields. Only foreign words participate in the guard relation. -/
theorem VirtualRepair.withHistories (preserved : Finset VarId) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), VirtualRepair preserved who program
        original repaired → ∀ past changed,
      (∀ other, other ≠ who → changed other = past other) →
      VirtualRepair preserved who program (withHistory program original past)
        (withHistory program repaired changed)
  | _, _, .ret _, _, _, paired, past, changed, foreign =>
      Config.VirtualRepair.withHistories paired past changed foreign
  | _, _, .sample _ _ _ next, original, repaired, paired, past, changed, foreign => by
      cases original <;> cases repaired
      · exact Config.VirtualRepair.withHistories paired past changed foreign
      · exact paired.elim
      · exact paired.elim
      · exact withHistories preserved who next _ _ paired past changed foreign
  | _, _, .commit _ _ _ _ next, original, repaired, paired, past, changed, foreign => by
      cases original <;> cases repaired
      · exact Config.VirtualRepair.withHistories paired past changed foreign
      · exact paired.elim
      · exact paired.elim
      · exact withHistories preserved who next _ _ paired past changed foreign
  | _, _, .reveal _ _ _ _ _ _ next, original, repaired, paired, past, changed, foreign => by
      cases original <;> cases repaired
      · exact Config.VirtualRepair.withHistories paired past changed foreign
      · exact paired.elim
      · exact paired.elim
      · exact withHistories preserved who next _ _ paired past changed foreign

private theorem commitOwners_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    commitOwners program (entry program config) = (commitPhase program).block.owners := by
  cases program <;> rfl

private theorem commitOwners_head {Γ : SourceCtx Player L} {O : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ) (insert name O))
    (config : Config Player L Γ) :
    commitOwners (.commit name owner fresh guard next) (.inl config) =
      insert owner (commitOwners next
        (entry next (automaticCommit name owner payload config))) := by
  change insert owner (commitPhase next).block.owners = _
  rw [commitOwners_entry]

/-- Exhaustion inserts only excluded foreign automatic slots. It cannot
replace an active owner's domain declaration by an automatic failed binding. -/
theorem VirtualRepair.automaticCommitBlock (preserved : Finset VarId) (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (original repaired : ProtocolState program), VirtualRepair preserved who program
        original repaired → who ∉ commitOwners program original →
      VirtualRepair preserved who program (automaticCommitBlock program original)
        (automaticCommitBlock program repaired) := by
  intro Γ O program
  induction program with
  | ret => intro original repaired paired _outside; exact paired
  | sample name fresh law next ih =>
      intro original repaired paired outside
      cases original <;> cases repaired
      · exact paired
      · exact paired.elim
      · exact paired.elim
      · exact ih _ _ paired outside
  | commit name owner fresh guard next ih =>
      intro original repaired paired outside
      cases original <;> cases repaired
      · rw [commitOwners_head fresh guard next] at outside
        have foreign : owner ≠ who := fun same =>
          outside (same ▸ Finset.mem_insert_self owner _)
        have rest : who ∉ commitOwners next
            (entry next (automaticCommit name owner _ _)) := fun member =>
          outside (Finset.mem_insert_of_mem member)
        exact ih _ _ (virtualRepair_entry preserved who next
          (paired.automaticCommit name owner _ foreign)) rest
      · exact paired.elim
      · exact paired.elim
      · exact ih _ _ paired outside
  | reveal published owner name fresh selected unresolved next ih =>
      intro original repaired paired outside
      cases original <;> cases repaired
      · exact paired
      · exact paired.elim
      · exact paired.elim
      · exact ih _ _ paired outside

end ProtocolState
namespace CommitRecoveryState

/-- A genuine virtual recovery state fixes all setup cells, translates exact
introduced declarations, and retains the full actual occurrence controls. -/
structure VirtualRepair (preserved : Finset VarId) (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    (original repaired : CommitRecoveryState program) : Prop where
  point : ProtocolState.VirtualRepair preserved who program original.point repaired.point
  saved : ProtocolState.VirtualRepair preserved who program original.saved repaired.saved
  excluded : repaired.excluded = original.excluded
  entryExcluded : repaired.entryExcluded = original.entryExcluded
  generation : repaired.generation = original.generation

/-- Exact virtual state readback includes the existing guard/public relation. -/
theorem VirtualRepair.focalRepair {preserved : Finset VarId} {who : Player}
    {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}
    {original repaired : CommitRecoveryState program}
    (related : VirtualRepair preserved who original repaired) :
    FocalRepair who original repaired :=
  ⟨ProtocolState.VirtualRepair.focalRepair preserved who _ _ _ related.point,
    ProtocolState.VirtualRepair.focalRepair preserved who _ _ _ related.saved,
    related.excluded, related.entryExcluded, related.generation⟩

/-- Closing takes the same clean, retry or exhausted branch, while carrying
literal attempted words from the paired current states into the saved fields. -/
theorem VirtualRepair.close {Γ : SourceCtx Player L} {O : Finset VarId}
    {preserved : Finset VarId} {program : SourceProgram Player L Γ O} {who : Player}
    {original repaired : CommitRecoveryState program}
    (related : VirtualRepair preserved who original repaired)
    (active : who ∉ original.excluded) :
    VirtualRepair preserved who original.close repaired.close := by
  have current := ProtocolState.FocalRepair.control who program _ _
    (ProtocolState.VirtualRepair.focalRepair preserved who _ _ _ related.point)
  have saved := ProtocolState.FocalRepair.control who program _ _
    (ProtocolState.VirtualRepair.focalRepair preserved who _ _ _ related.saved)
  have restored : ProtocolState.VirtualRepair preserved who program original.restored
      repaired.restored :=
    ProtocolState.VirtualRepair.withHistories preserved who program _ _ related.saved _ _
      (ProtocolState.FocalRepair.foreign_history who program _ _
        (ProtocolState.VirtualRepair.focalRepair preserved who _ _ _ related.point))
  have complete : repaired.Finished ↔ original.Finished := by
    simp only [Finished, current.1, saved.2.2.1, saved.2.2.2.1]
  have failure : repaired.NewFailure ↔ original.NewFailure := by
    simp only [NewFailure, related.excluded, related.entryExcluded]
  have survivor : repaired.Survives ↔ original.Survives := by
    simp only [Survives, saved.2.2.2.2, related.excluded]
  have pairedPoint (first second : ProtocolState program)
      (paired : ProtocolState.VirtualRepair preserved who program first second) :
      VirtualRepair preserved who (atPoint first original.excluded original.generation)
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
          (ProtocolState.VirtualRepair.automaticCommitBlock preserved who program _ _ restored (by
            intro member
            apply survives
            refine ⟨who, Finset.mem_sdiff.mpr ⟨?_, active⟩⟩
            exact (ProtocolState.withHistory_control program original.saved
              (ProtocolState.history program original.point)).2.2 ▸ member))
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

end SourceProgram
end Vegas
