/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSwapRegular

/-! # What two indistinguishable source points share

Two program points one player observes alike are at the same position and give
that player the same source observation of the current configuration, so every
cell visible to the player, found by name and kind, has the same value at both
(`Vegas.visibleCellsAgree_of_observe`); in particular every public cell does
(`Vegas.publicCellsAgree_of_observe`).

At a point of the intended game every commitment cell holds a value
(`Vegas.SourceProgram.ProtocolState.cell?_commitment_success`), so two such
points have only successful commitment cells
(`Vegas.commitmentCellsSucceed_of_intended`).

A commitment is revealed at a point when the publication status of the current
configuration records it as published into a publication cell
(`Vegas.SourceProgram.ProtocolState.RevealedInto`). An intended reveal publishes
the binding, and two intended points one player cannot tell apart differ by a
cell swap, which keeps the publication status; so a commitment revealed at one
has the same value at both (`Vegas.revealedCellsAgree_of_observe`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The current configuration of a program point, with its context. -/
def ProtocolState.currentConfig : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
      Σ Δ : SourceCtx Player L, Config Player L Δ
  | _, _, .ret _ => fun config => ⟨_, config⟩
  | _, _, .sample _ _ _ next => Sum.elim (fun config => ⟨_, config⟩) (currentConfig next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun config => ⟨_, config⟩) (currentConfig next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun config => ⟨_, config⟩) (currentConfig next)

/-- The commitment cell `name` of a configuration is revealed into the
publication cell `published`. -/
def Config.RevealedInto {Γ : SourceCtx Player L} (config : Config Player L Γ) (owner : Player)
    (payload : L.Ty) (name published : VarId) : Prop :=
  ∃ (source : HasVar Γ name (.commitment owner payload))
    (cell : HasVar Γ published (.publication payload)),
    config.revelations source = .revealed cell

/-- The commitment cell `name` is revealed into the publication cell `published`
at the current configuration of a program point. -/
def ProtocolState.RevealedInto {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (state : ProtocolState program) (owner : Player)
    (payload : L.Ty) (name published : VarId) : Prop :=
  (ProtocolState.currentConfig program state).2.RevealedInto owner payload name published

/-- A cell swap leaves the current context and acts on the current configuration. -/
theorem ProtocolState.currentConfig_swap (swap : CellSwap Player L) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (state : ProtocolState program),
      currentConfig program (swap.protocolState program state) =
        ⟨(currentConfig program state).1, swap.config (currentConfig program state).2⟩
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact currentConfig_swap swap next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact currentConfig_swap swap next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact currentConfig_swap swap next rest

/-- A cell swap keeps the publication status, hence what is revealed. -/
theorem ProtocolState.revealedInto_swap (swap : CellSwap Player L) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (state : ProtocolState program)
    {owner : Player} {payload : L.Ty} {name published : VarId} :
    RevealedInto program (swap.protocolState program state) owner payload name published ↔
      RevealedInto program state owner payload name published := by
  unfold RevealedInto
  rw [currentConfig_swap]
  exact Iff.rfl

/-- The current configuration of an intended program point is intended. -/
theorem ProtocolState.intended_currentConfig : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) {state : ProtocolState program},
    Intended program state → ∃ unresolved, (currentConfig program state).2.Intended unresolved
  | _, _, .ret _, _, intended => ⟨∅, intended⟩
  | _, _, .sample _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact ⟨_, intended.1⟩
      | inr rest => exact intended_currentConfig next intended
  | _, _, .commit _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact ⟨_, intended.1⟩
      | inr rest => exact intended_currentConfig next intended
  | _, _, .reveal _ _ _ _ _ _ next, state, intended => by
      cases state with
      | inl _ => exact ⟨_, intended.1⟩
      | inr rest => exact intended_currentConfig next intended.2

section CellLookup

variable [DecidableEq (CellTy Player L)]

/-- A lookup at a program point is a lookup in its current configuration. -/
theorem ProtocolState.cell?_eq_currentConfig (name : VarId) (kind : CellTy Player L) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (state : ProtocolState program),
      cell? program state name kind = State.cell? (currentConfig program state).2.state name kind
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact cell?_eq_currentConfig name kind next rest
  | _, _, .commit _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact cell?_eq_currentConfig name kind next rest
  | _, _, .reveal _ _ _ _ _ _ next, state => by
      cases state with
      | inl _ => rfl
      | inr rest => exact cell?_eq_currentConfig name kind next rest

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A found cell is the value at a witness of it. -/
theorem State.exists_hasVar_of_cell?_eq_some {name : VarId} {kind : CellTy Player L}
    {value : CellVal L kind} :
    ∀ {Γ : SourceCtx Player L} {cells : State L Γ},
      State.cell? cells name kind = some value →
        ∃ source : HasVar Γ name kind, cells.get source = value
  | [], _, found => by simp [State.cell?] at found
  | (current, currentKind) :: Γ, cells, found => by
      unfold State.cell? at found
      split_ifs at found with same
      · obtain ⟨rfl, rfl⟩ := same
        exact ⟨.here, Option.some.inj found⟩
      · obtain ⟨source, equal⟩ := State.exists_hasVar_of_cell?_eq_some found
        exact ⟨.there source, equal⟩

omit [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
/-- Equal observations of one player agree on every cell visible to that player. -/
private theorem get_eq_of_sourceObserve {who : Player} {Γ : SourceCtx Player L}
    {left right : State L Γ} (same : sourceObserve who left = sourceObserve who right)
    {name : VarId} {kind : CellTy Player L} (visible : (cellField kind).VisibleTo who)
    (source : HasVar Γ name kind) : left.get source = right.get source := by
  have cell := congrArg (fun observation => observation.cells name kind source) same
  cases kind with
  | publicData _ => exact cell
  | publication _ => exact cell
  | commitment owner _ =>
      have mine : owner = who := visible
      subst mine
      simp only [sourceObserve_commitment, ↓reduceIte] at cell
      exact Option.some.inj cell
  | privateInput owner _ =>
      have mine : owner = who := visible
      subst mine
      simp only [sourceObserve_privateInput, ↓reduceIte] at cell
      exact Option.some.inj cell

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- States agreeing at every witness of a cell agree on its lookup. -/
private theorem cell?_eq_of_get_eq {name : VarId} {kind : CellTy Player L} :
    ∀ {Γ : SourceCtx Player L} {left right : State L Γ},
      (∀ source : HasVar Γ name kind, left.get source = right.get source) →
        State.cell? left name kind = State.cell? right name kind
  | [], _, _, _ => rfl
  | (current, currentKind) :: Γ, left, right, agree => by
      rw [State.cell?.eq_2, State.cell?.eq_2]
      split_ifs with found
      · obtain ⟨rfl, rfl⟩ := found
        exact congrArg some (agree .here)
      · exact cell?_eq_of_get_eq fun source => agree (.there source)

omit [IExpr.ResultTypes L] in
/-- Equal observations of one player give equal lookups of every cell visible
to that player. -/
theorem State.cell?_eq_of_sourceObserve {who : Player} {name : VarId}
    {kind : CellTy Player L} (visible : (cellField kind).VisibleTo who)
    {Γ : SourceCtx Player L} {left right : State L Γ}
    (same : sourceObserve who left = sourceObserve who right) :
    State.cell? left name kind = State.cell? right name kind :=
  cell?_eq_of_get_eq fun source => get_eq_of_sourceObserve same visible source

/-- Equal observations of one player give equal lookups, at the two program
points, of every cell visible to that player. -/
theorem ProtocolState.cell?_eq_of_observe {who : Player} {name : VarId}
    {kind : CellTy Player L} (visible : (cellField kind).VisibleTo who) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      {first second : ProtocolState program},
      observe who program first = observe who program second →
        cell? program first name kind = cell? program second name kind
  | _, _, .ret _, _, _, same => State.cell?_eq_of_sourceObserve visible (congrArg Prod.fst same)
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at same
      · exact State.cell?_eq_of_sourceObserve visible (congrArg Prod.fst same)
      · exact cell?_eq_of_observe visible next same
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at same
      · exact State.cell?_eq_of_sourceObserve visible (congrArg Prod.fst same)
      · exact cell?_eq_of_observe visible next same
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second <;> simp only [observe, Sum.elim_inl, Sum.elim_inr,
        reduceCtorEq, Sum.inr.injEq, Sum.inl.injEq] at same
      · exact State.cell?_eq_of_sourceObserve visible (congrArg Prod.fst same)
      · exact cell?_eq_of_observe visible next same

/-- **Commitment cells of the intended game hold values.** -/
theorem ProtocolState.cell?_commitment_success {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {state : ProtocolState program}
    (intended : Intended program state) {name : VarId} {owner : Player} {payload : L.Ty}
    {found : PublicationResult (L.Val payload)}
    (lookup : cell? program state name (.commitment owner payload) = some found) :
    ∃ value, found = .success value := by
  rw [cell?_eq_currentConfig] at lookup
  obtain ⟨_, current⟩ := intended_currentConfig program intended
  obtain ⟨source, rfl⟩ := State.exists_hasVar_of_cell?_eq_some lookup
  exact current.bound source

omit [IExpr.ResultTypes L] in
/-- In an intended configuration a revealed commitment has the value of the
publication cell it is revealed into. -/
theorem Config.cell?_eq_of_revealedInto {Γ : SourceCtx Player L} {config : Config Player L Γ}
    {unresolved : Finset VarId} (intended : config.Intended unresolved) {owner : Player}
    {payload : L.Ty} {name published : VarId}
    (revealed : config.RevealedInto owner payload name published) :
    State.cell? config.state name (.commitment owner payload) =
      State.cell? config.state published (.publication payload) := by
  obtain ⟨source, cell, recorded⟩ := revealed
  have publishes : (config.revelations source).result config.state = config.state.get source :=
    intended.publishes owner source (by simp only [recorded, Revelation.isRevealed])
  rw [recorded] at publishes
  rw [State.cell?_eq_of_hasVar source intended.unique,
    State.cell?_eq_of_hasVar cell intended.unique]
  exact congrArg some publishes.symm

/-- At an intended program point a revealed commitment has the value of the
publication cell it is revealed into. -/
theorem ProtocolState.cell?_eq_of_revealedInto {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {state : ProtocolState program}
    (intended : Intended program state) {owner : Player} {payload : L.Ty}
    {name published : VarId} (revealed : RevealedInto program state owner payload name published) :
    cell? program state name (.commitment owner payload) =
      cell? program state published (.publication payload) := by
  obtain ⟨_, current⟩ := intended_currentConfig program intended
  rw [cell?_eq_currentConfig, cell?_eq_currentConfig]
  exact Config.cell?_eq_of_revealedInto current revealed

end CellLookup

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [IExpr.ResultTypes L] [DecidableEq (CellTy Player L)] in
private theorem visibleTo_of_isPublic {kind : CellTy Player L} (who : Player)
    (isPublic : (cellField kind).IsPublic) : (cellField kind).VisibleTo who := by
  cases kind <;> simp_all [cellField, EventGraph.EventField.IsPublic,
    EventGraph.EventField.VisibleTo]

/-- **Indistinguishable points agree on visible cells.** At two program points
one player observes alike, every cell visible to that player has the same
lookup. -/
theorem visibleCellsAgree_of_observe {p q : ProtocolState setup.program} {who : Player}
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    (name : VarId) {kind : CellTy Player L} (visible : (cellField kind).VisibleTo who) :
    ProtocolState.cell? setup.program p name kind =
      ProtocolState.cell? setup.program q name kind :=
  ProtocolState.cell?_eq_of_observe visible setup.program sameView

/-- **Indistinguishable points agree on public cells.** -/
theorem publicCellsAgree_of_observe {p q : ProtocolState setup.program} {who : Player}
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q) :
    PublicCellsAgree setup p q := by
  intro name kind isPublic left right leftFound rightFound
  have same := visibleCellsAgree_of_observe sameView name (visibleTo_of_isPublic who isPublic)
  rw [leftFound, rightFound] at same
  exact Option.some.inj same

/-- **Intended points have successful commitment cells.** -/
theorem commitmentCellsSucceed_of_intended (wellFormed : setup.WellFormed)
    {first second : setup.intendedProtocol.History} {p q : ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q) :
    CommitmentCellsSucceed setup p q := by
  intro name owner payload left right leftFound rightFound _
  obtain ⟨_, rfl⟩ := ProtocolState.cell?_commitment_success
    (intended_of_history wellFormed first.trace p firstState) leftFound
  obtain ⟨_, rfl⟩ := ProtocolState.cell?_commitment_success
    (intended_of_history wellFormed second.trace q secondState) rightFound
  exact ⟨by rintro ⟨⟩, by rintro ⟨⟩⟩

/-- **Indistinguishable intended points agree on revealed commitments.** A
commitment revealed at one of two intended points one player observes alike has
the same lookup at both: both reveal it into the same publication cell, which
holds its binding and is public. -/
theorem revealedCellsAgree_of_observe (wellFormed : setup.WellFormed)
    {first second : setup.intendedProtocol.History} {p q : ProtocolState setup.program}
    (firstState : first.state = some p) (secondState : second.state = some q) (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (revealed : ProtocolState.RevealedInto setup.program p owner payload name published) :
    ProtocolState.cell? setup.program p name (.commitment owner payload) =
      ProtocolState.cell? setup.program q name (.commitment owner payload) := by
  have firstIntended := intended_of_history wellFormed first.trace p firstState
  have secondIntended := intended_of_history wellFormed second.trace q secondState
  have swapped := setup.intended_eq_between_of_observe firstState secondState who sameView
  have secondRevealed :
      ProtocolState.RevealedInto setup.program q owner payload name published := by
    rw [swapped]
    exact (ProtocolState.revealedInto_swap _ setup.program p).mpr revealed
  rw [ProtocolState.cell?_eq_of_revealedInto firstIntended revealed,
    ProtocolState.cell?_eq_of_revealedInto secondIntended secondRevealed]
  exact visibleCellsAgree_of_observe sameView published trivial

end Vegas
