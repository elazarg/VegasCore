/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.Semantics

/-! # Revelation accounting

The syntax's open-resource index tracks unresolved commitments. `Accounted`
ties it to the static revelations. Every checked program therefore resolves
every commitment before `ret` (`SourceProgram.Initial.revealed`), independently
of policies, chance outcomes, and publication failure. Private inputs persist.
-/

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A commitment is resolved exactly when its name has left the open index. -/
def Accounted {Γ : SourceCtx Player L} (revelations : Revelations Γ) (O : Finset VarId) :
    Prop :=
  ∀ {owner : Player} {payload : L.Ty} {name : VarId}
    (h : HasVar Γ name (.commitment owner payload)),
    (revelations h).isRevealed = true ↔ name ∉ O

/-- The revelations after following the remaining source syntax. -/
def finalRevelations : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → Revelations Γ →
      Revelations (terminalCtx program)
  | _, _, .ret _, revelations => revelations
  | _, _, .sample _ _ _ next, revelations => finalRevelations next revelations.weaken
  | _, _, .commit _ _ _ _ next, revelations => finalRevelations next revelations.weaken
  | _, _, .reveal published _ _ _ source _ next, revelations =>
      finalRevelations next (revelations.reveal (published := published) source)

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem mem_commitmentNames {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    {name : VarId} (h : HasVar Γ name (.commitment owner payload)) : name ∈ commitmentNames Γ := by
  induction Γ with
  | nil => nomatch h
  | cons entry tail ih =>
      obtain ⟨head, cell⟩ := entry
      cases h with
      | here => simp [commitmentNames]
      | there h => cases cell <;> simp [commitmentNames, ih h]

namespace Accounted

omit [DecidableEq Player] [IExpr.ResultTypes L]

theorem initial (Γ : SourceCtx Player L) :
    Accounted (Revelations.initial Γ) (commitmentNames Γ) := by
  intro owner payload name h
  simp only [Revelations.initial, Revelation.isRevealed, Bool.false_eq_true, false_iff,
    not_not]
  exact mem_commitmentNames h

theorem weaken_noncommitment {Γ : SourceCtx Player L} {O : Finset VarId}
    {revelations : Revelations Γ}
    {name : VarId} {cell : CellTy Player L} (nonCommitment : ∀ owner payload,
      cell ≠ .commitment owner payload)
    (accounted : Accounted revelations O) :
    Accounted (revelations.weaken (name := name) (cell := cell)) O := by
  intro owner payload private_ h
  cases h with
  | here => exact absurd rfl (nonCommitment owner payload)
  | there h => simpa using accounted h

theorem commit {Γ : SourceCtx Player L} {O : Finset VarId} {revelations : Revelations Γ}
    {name : VarId} {owner : Player} {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (accounted : Accounted revelations O) :
    Accounted (revelations.weaken (name := name) (cell := .commitment owner payload))
      (insert name O) := by
  intro readOwner readPayload readName h
  cases h with
  | here => simp [Revelations.weaken, HasVar.tail?, Revelation.isRevealed]
  | there h =>
      have different : readName ≠ name := fun same => fresh (same ▸ h.mem_map_fst)
      simpa [different] using accounted h

theorem reveal {Γ : SourceCtx Player L} {O : Finset VarId} {revelations : Revelations Γ}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (source : HasVar Γ name (.commitment owner payload)) (unique : (Γ.map Prod.fst).Nodup)
    (accounted : Accounted revelations O) :
    Accounted (revelations.reveal (published := published) source) (O.erase name) := by
  intro readOwner readPayload readName h
  cases h with
  | there h =>
      by_cases same : readName = name
      · subst readName
        have cellEq := HasVar.type_unique unique h source
        cases cellEq
        cases HasVar.eq_of_nodup unique h source
        simp [Revelation.isRevealed]
      · simp only [Revelations.reveal_of_ne revelations source h same,
          Revelation.isRevealed_weaken]
        simpa [same] using accounted h

end Accounted

/-- Following a checked program resolves every commitment. -/
theorem finalRevelations_revealed {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (revelations : Revelations Γ), (Γ.map Prod.fst).Nodup → Accounted revelations O →
      ∀ {owner : Player} {payload : L.Ty} {name : VarId}
        (h : HasVar (terminalCtx program) name (.commitment owner payload)),
        (finalRevelations program revelations h).isRevealed = true := by
  induction program with
  | ret payoffs =>
      intro revelations _ accounted owner payload name h
      exact (accounted h).mpr (Finset.notMem_empty name)
  | sample name fresh law next ih =>
      intro revelations unique accounted
      exact ih _ (by simp [fresh, unique])
        (Accounted.weaken_noncommitment (by intro _ _ equal; cases equal) accounted)
  | commit name owner fresh guard next ih =>
      intro revelations unique accounted
      exact ih _ (by simp [fresh, unique]) (Accounted.commit fresh accounted)
  | reveal published owner name fresh source unresolved next ih =>
      intro revelations unique accounted
      exact ih _ (by simp [fresh, unique]) (Accounted.reveal source unique accounted)

/-- Every commitment of a checked initial source game is resolved by the end of
its syntax. -/
theorem Initial.revealed (initial : Initial (Player := Player) (L := L))
    {owner : Player} {payload : L.Ty} {name : VarId}
    (h : HasVar initial.program.terminalCtx name (.commitment owner payload)) :
    (finalRevelations initial.program (Revelations.initial initial.context) h).isRevealed =
      true :=
  finalRevelations_revealed initial.program _ initial.namesNodup
    (initial.accounts ▸ Accounted.initial initial.context) h

end Vegas.SourceProgram
