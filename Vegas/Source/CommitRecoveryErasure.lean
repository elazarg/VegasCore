/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryInformation

/-! # Source information after erasing remembered private words

Current typed observations retain every original private input and live own
binding. Every past public cell and the complete exclusion/attempt transcript
is retained. Private past signals and their own-play tags are not copied into
the strategy representative. The original information model and its perfect
recall are unchanged.
-/

noncomputable section

namespace Vegas

namespace SourceObservation

variable {Player : Type} {L : IExpr} {who : Player} {Γ : SourceCtx Player L}

/-- Retain exactly the public cells of an existing source observation. -/
def publicOnly (view : SourceObservation L who Γ) : SourceObservation L who Γ :=
  ⟨fun name cell member => match cell with
    | .publicData payload => view.cells name (.publicData payload) member
    | .publication payload => view.cells name (.publication payload) member
    | .privateInput _ _ => none
    | .commitment _ _ => none⟩

@[simp] theorem publicOnly_idempotent (view : SourceObservation L who Γ) :
    view.publicOnly.publicOnly = view.publicOnly := by
  unfold publicOnly
  congr 1

end SourceObservation

namespace SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

/-- Replace only the remembered action list at the current source cursor. -/
def eraseHistory (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → ProtocolView who program
  | _, _, .ret _, view => (view.1, [])
  | _, _, .sample _ _ _ next, view =>
      view.elim (fun current => .inl (current.1, []))
        (fun later => .inr (eraseHistory who next later))
  | _, _, .commit _ _ _ _ next, view =>
      view.elim (fun current => .inl (current.1, []))
        (fun later => .inr (eraseHistory who next later))
  | _, _, .reveal _ _ _ _ _ _ next, view =>
      view.elim (fun current => .inl (current.1, []))
        (fun later => .inr (eraseHistory who next later))

/-- A past signal keeps all of its public data and its exact source cursor. -/
def publicOnly (who : Player) : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolView who program → ProtocolView who program
  | _, _, .ret _, view => (view.1.publicOnly, [])
  | _, _, .sample _ _ _ next, view =>
      view.elim (fun current => .inl (current.1.publicOnly, []))
        (fun later => .inr (publicOnly who next later))
  | _, _, .commit _ _ _ _ next, view =>
      view.elim (fun current => .inl (current.1.publicOnly, []))
        (fun later => .inr (publicOnly who next later))
  | _, _, .reveal _ _ _ _ _ _ next, view =>
      view.elim (fun current => .inl (current.1.publicOnly, []))
        (fun later => .inr (publicOnly who next later))

@[simp] theorem eraseHistory_idempotent (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      eraseHistory who program (eraseHistory who program view) = eraseHistory who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, Sum.elim_inl, Sum.elim_inr,
        eraseHistory_idempotent who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, Sum.elim_inl, Sum.elim_inr,
        eraseHistory_idempotent who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, Sum.elim_inl, Sum.elim_inr,
        eraseHistory_idempotent who next]

@[simp] theorem publicOnly_idempotent (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      publicOnly who program (publicOnly who program view) = publicOnly who program view
  | _, _, .ret _, _ => by simp only [publicOnly, SourceObservation.publicOnly_idempotent]
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [publicOnly, Sum.elim_inl, Sum.elim_inr,
        SourceObservation.publicOnly_idempotent, publicOnly_idempotent who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [publicOnly, Sum.elim_inl, Sum.elim_inr,
        SourceObservation.publicOnly_idempotent, publicOnly_idempotent who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [publicOnly, Sum.elim_inl, Sum.elim_inr,
        SourceObservation.publicOnly_idempotent, publicOnly_idempotent who next]

theorem actor_publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : SourceProgram.ProtocolView who program),
      ProtocolView.actor who program (ProtocolView.publicOnly who program view) =
        ProtocolView.actor who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [ProtocolView.publicOnly, ProtocolView.actor,
        Sum.elim_inl, Sum.elim_inr, actor_publicOnly who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [ProtocolView.publicOnly, ProtocolView.actor,
        Sum.elim_inl, Sum.elim_inr, actor_publicOnly who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [ProtocolView.publicOnly, ProtocolView.actor,
        Sum.elim_inl, Sum.elim_inr, actor_publicOnly who next]


@[simp] theorem actor_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      actor who program (eraseHistory who program view) = actor who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, actor, Sum.elim_inl, Sum.elim_inr,
        actor_eraseHistory who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, actor, Sum.elim_inl, Sum.elim_inr,
        actor_eraseHistory who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, actor, Sum.elim_inl, Sum.elim_inr,
        actor_eraseHistory who next]

@[simp] theorem available_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
      (view : ProtocolView who program),
      available who program admission (eraseHistory who program view) =
        available who program admission view
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, admission, view => by
      cases view <;> simp only [eraseHistory, available, Sum.elim_inl, Sum.elim_inr,
        available_eraseHistory who next]
  | _, _, .commit _ _ _ _ next, admission, view => by
      cases view <;> simp only [eraseHistory, available, Sum.elim_inl, Sum.elim_inr,
        available_eraseHistory who next]
  | _, _, .reveal _ _ _ _ _ _ next, admission, view => by
      cases view <;> simp only [eraseHistory, available, Sum.elim_inl, Sum.elim_inr,
        available_eraseHistory who next]

@[simp] theorem atCommit_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      atCommit who program (eraseHistory who program view) = atCommit who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, atCommit, Sum.elim_inl, Sum.elim_inr,
        atCommit_eraseHistory who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, atCommit, Sum.elim_inl, Sum.elim_inr,
        atCommit_eraseHistory who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, atCommit, Sum.elim_inl, Sum.elim_inr,
        atCommit_eraseHistory who next]

@[simp] theorem recoveryAvailable_eraseHistory (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (view : ProtocolView who program) :
    recoveryAvailable who program (eraseHistory who program view) =
      recoveryAvailable who program view := by
  simp only [recoveryAvailable, available_eraseHistory, atCommit_eraseHistory]

/-- Erasing the remembered word leaves the complete typed observation fixed,
including the original correlated private input tuple. -/
theorem eraseHistory_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      eraseHistory who program (ProtocolState.observe who program point) =
        ProtocolState.observe who program (ProtocolState.withHistory program point (fun _ => []))
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, point => by
      cases point <;> simp only [eraseHistory, ProtocolState.observe, ProtocolState.withHistory,
        Sum.elim_inl, Sum.elim_inr, eraseHistory_observe who next, Config.view]
  | _, _, .commit _ _ _ _ next, point => by
      cases point <;> simp only [eraseHistory, ProtocolState.observe, ProtocolState.withHistory,
        Sum.elim_inl, Sum.elim_inr, eraseHistory_observe who next, Config.view]
  | _, _, .reveal _ _ _ _ _ _ next, point => by
      cases point <;> simp only [eraseHistory, ProtocolState.observe, ProtocolState.withHistory,
        Sum.elim_inl, Sum.elim_inr, eraseHistory_observe who next, Config.view]

@[simp] theorem publicOnly_eraseHistory (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      publicOnly who program (eraseHistory who program view) = publicOnly who program view
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, publicOnly, Sum.elim_inl, Sum.elim_inr,
        publicOnly_eraseHistory who next]
  | _, _, .commit _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, publicOnly, Sum.elim_inl, Sum.elim_inr,
        publicOnly_eraseHistory who next]
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view <;> simp only [eraseHistory, publicOnly, Sum.elim_inl, Sum.elim_inr,
        publicOnly_eraseHistory who next]

end ProtocolView

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- A strategy representative on the original full information type. Past
public typed observations and all public controls remain literal; prior
private signals and own-play tags are erased. Current live private data are
retained by `ProtocolView.eraseHistory`. -/
def commitRecoveryErasedInformation (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) : setup.commitRecoveryModel.InfoState who :=
  (((info.1.1.1.map (ProtocolView.eraseHistory who setup.program), info.1.1.2),
    info.1.2.map fun signal =>
      (signal.1.map (ProtocolView.publicOnly who setup.program), signal.2)), [])

@[simp] theorem commitRecoveryErasedInformation_idempotent (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryErasedInformation who (setup.commitRecoveryErasedInformation who info) =
      setup.commitRecoveryErasedInformation who info := by
  simp only [commitRecoveryErasedInformation, Option.map_map, List.map_map, Function.comp_def,
    ProtocolView.eraseHistory_idempotent, ProtocolView.publicOnly_idempotent]

/-- The representative has exactly the actual raw menu. This transports
choices without dropping accepted failed bindings or omission flags. -/
theorem commitRecoveryErasedInformation_menu (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.menu who (setup.commitRecoveryErasedInformation who info) =
      setup.commitRecoveryModel.menu who info := by
  ext choice
  change setup.commitRecoveryMenu who (setup.commitRecoveryErasedInformation who info) choice ↔
    setup.commitRecoveryMenu who info choice
  have active : setup.commitRecoveryActive who
      (setup.commitRecoveryErasedInformation who info).1.1 ↔
        setup.commitRecoveryActive who info.1.1 := by
    change ((info.1.1.1.map (ProtocolView.eraseHistory who setup.program)).elim False
      (fun view => ProtocolView.actor who setup.program view = some who ∧
        who ∉ info.1.1.2.1)) ↔ _
    unfold commitRecoveryActive
    cases current : info.1.1.1 with
    | none => simp only [Option.map_none, Option.elim_none]
    | some view =>
        simp only [Option.map_some, Option.elim_some, ProtocolView.actor_eraseHistory]
  cases choice with
  | none => exact not_congr active
  | some move =>
      apply and_congr active
      change (info.1.1.1.map (ProtocolView.eraseHistory who setup.program)).elim False
        (fun view => move ∈ ProtocolView.recoveryAvailable who setup.program view) ↔ _
      cases current : info.1.1.1 with
      | none => simp only [Option.map_none, Option.elim_none]
      | some view =>
          simp only [Option.map_some, Option.elim_some,
            ProtocolView.recoveryAvailable_eraseHistory]

/-- The source perfect-recall structure is unchanged; this equivalence only
transports a strategy's law along the derived equality of raw menus. -/
def commitRecoveryErasedChoice (who : Player)
    (info : setup.commitRecoveryModel.InfoState who) :
    setup.commitRecoveryModel.Choice who info ≃
      setup.commitRecoveryModel.Choice who (setup.commitRecoveryErasedInformation who info) where
  toFun choice := ⟨choice.1, by
    rw [setup.commitRecoveryErasedInformation_menu who info]
    exact choice.2⟩
  invFun choice := ⟨choice.1, by
    rw [← setup.commitRecoveryErasedInformation_menu who info]
    exact choice.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Setup
end SourceProgram
end Vegas
