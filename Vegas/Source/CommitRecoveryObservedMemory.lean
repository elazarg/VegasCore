/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryErasedStep
import Vegas.Source.ObservationRecall
import Vegas.Source.ProtocolSuffix

/-! # Typed current observations with independent remembered-word projection -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {wholeΓ : SourceCtx Player L} {wholeO : Finset VarId}


/-- Select the remembered-word part of an existing typed decision view.
Both choices keep every current typed cell. -/
def DecisionView.historyProjection {who : Player} {Γ : SourceCtx Player L}
    (remember : Bool) (view : DecisionView (L := L) who Γ) : DecisionView who Γ :=
  if remember then view else (view.1, [])

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Every current typed cell is retained by either memory projection. -/
@[simp] theorem DecisionView.historyProjection_cells {who : Player} {Γ : SourceCtx Player L}
    (remember : Bool) (view : DecisionView (L := L) who Γ) :
    (historyProjection remember view).1 = view.1 := by cases remember <;> rfl

/-- The semantic projection removes only the current remembered word; it
preserves the actual source cursor and the entire live typed observation. -/
def ProtocolView.historyProjection (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (remember : Bool) (view : ProtocolView who program) : ProtocolView who program :=
  if remember then view else eraseHistory who program view

/-- Either remembered-word convention has the same literal public cells and cursor. -/
@[simp] theorem ProtocolView.publicOnly_historyProjection (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (remember : Bool) (view : ProtocolView who program) :
    publicOnly who program (historyProjection who program remember view) =
      publicOnly who program view := by
  cases remember <;> simp only [historyProjection, Bool.false_eq_true, ↓reduceIte,
    publicOnly_eraseHistory]

/-- Actual suffix lifts commute with replacing remembered words. -/
theorem ProtocolSuffix.withHistory_lift
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) :
    ∀ point past, lift (ProtocolState.withHistory program point past) =
      ProtocolState.withHistory whole (lift point) past := by
  induction origin with
  | initial => intro point past; rfl
  | sampleTail fresh law next previous ih => exact fun point past => ih (.inr point) past
  | commitTail fresh guard next previous ih => exact fun point past => ih (.inr point) past
  | revealTail fresh selected unresolved next previous ih =>
      exact fun point past => ih (.inr point) past

/-- Comparing projected whole views reflects to the same genuine typed suffix. -/
theorem ProtocolSuffix.historyProjection_observe_reflect
    {Γ : SourceCtx Player L} {O : Finset VarId}
    {whole : SourceProgram Player L wholeΓ wholeO} {program : SourceProgram Player L Γ O}
    {lift : ProtocolState program → ProtocolState whole}
    (origin : ProtocolSuffix whole program lift) (who : Player) (remember : Bool)
    (first second : ProtocolState program)
    (same : ProtocolView.historyProjection who whole remember
        (ProtocolState.observe who whole (lift first)) =
      ProtocolView.historyProjection who whole remember
        (ProtocolState.observe who whole (lift second))) :
    ProtocolView.historyProjection who program remember
        (ProtocolState.observe who program first) =
      ProtocolView.historyProjection who program remember
        (ProtocolState.observe who program second) := by
  cases remember with
  | true => exact origin.observe_reflect who first second same
  | false =>
      have reflected := origin.observe_reflect who
        (ProtocolState.withHistory program first (fun _ => []))
        (ProtocolState.withHistory program second (fun _ => []))
        (by simpa only [ProtocolView.historyProjection, Bool.false_eq_true, ↓reduceIte,
          ProtocolView.eraseHistory_observe, ← origin.withHistory_lift] using same)
      simpa only [ProtocolView.historyProjection, Bool.false_eq_true, ↓reduceIte,
        ProtocolView.eraseHistory_observe] using reflected

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- The current-memory projection commutes with deleting an old source cell. -/
theorem DecisionView.back_historyProjection {who : Player} {Γ : SourceCtx Player L}
    {name : VarId} {cell : CellTy Player L} (remember owned : Bool)
    (view : DecisionView who ((name, cell) :: Γ)) :
    (DecisionView.historyProjection remember view).back owned =
      DecisionView.historyProjection remember (view.back owned) := by
  cases remember with
  | true => rfl
  | false =>
      simp only [DecisionView.historyProjection, Bool.false_eq_true, ↓reduceIte,
        DecisionView.back, List.dropLast_nil, ite_self]

/-- The projected entry view carries exactly the selected decision memory,
even when read retrospectively from a later source cursor. -/
theorem ProtocolView.entryView_historyProjection (who : Player) (remember : Bool) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (view : ProtocolView who program),
      entryView who program (historyProjection who program remember view) =
        DecisionView.historyProjection remember (entryView who program view) := by
  cases remember with
  | true => intro Γ O program view; rfl
  | false =>
      intro Γ O program
      induction program with
      | ret => intro view; rfl
      | sample name fresh law next ih =>
          intro view
          cases view with
          | inl => rfl
          | inr view =>
              exact (congrArg (DecisionView.back false) (ih view)).trans
                (DecisionView.back_historyProjection false false _)
      | commit name owner fresh guard next ih =>
          intro view
          cases view with
          | inl => rfl
          | inr view =>
              exact (congrArg (DecisionView.back (decide (owner = who))) (ih view)).trans
                (DecisionView.back_historyProjection false (decide (owner = who)) _)
      | reveal published owner name fresh selected unresolved next ih =>
          intro view
          cases view with
          | inl => rfl
          | inr view =>
              exact (congrArg (DecisionView.back (decide (owner = who))) (ih view)).trans
                (DecisionView.back_historyProjection false (decide (owner = who)) _)

/-- Reading a genuine earlier rank commutes with selecting its current memory. -/
theorem ProtocolView.atRank_historyProjection (who : Player) (remember : Bool) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (rank : Nat) (view : ProtocolView who program),
      atRank who program rank (historyProjection who program remember view) =
        (atRank who program rank view).map (historyProjection who program remember) := by
  cases remember with
  | true =>
      intro Γ O program rank view
      change _ = Option.map id _
      simp only [Option.map_id]
      rfl
  | false =>
      intro Γ O program
      induction program with
      | ret => intro rank view; cases rank <;> rfl
      | sample name fresh law next ih =>
          intro rank view
          cases rank with
          | zero =>
              exact congrArg (fun v => some (Sum.inl v))
                (ProtocolView.entryView_historyProjection who false _ view)
          | succ rank =>
              cases view with
              | inl => rfl
              | inr view =>
                  simpa only [atRank, ProtocolView.historyProjection, Bool.false_eq_true,
                    ↓reduceIte, eraseHistory, Sum.elim_inr, Option.map_map,
                    Function.comp_def] using congrArg (Option.map Sum.inr) (ih rank view)
      | commit name owner fresh guard next ih =>
          intro rank view
          cases rank with
          | zero =>
              exact congrArg (fun v => some (Sum.inl v))
                (ProtocolView.entryView_historyProjection who false _ view)
          | succ rank =>
              cases view with
              | inl => rfl
              | inr view =>
                  simpa only [atRank, ProtocolView.historyProjection, Bool.false_eq_true,
                    ↓reduceIte, eraseHistory, Sum.elim_inr, Option.map_map,
                    Function.comp_def] using congrArg (Option.map Sum.inr) (ih rank view)
      | reveal published owner name fresh selected unresolved next ih =>
          intro rank view
          cases rank with
          | zero =>
              exact congrArg (fun v => some (Sum.inl v))
                (ProtocolView.entryView_historyProjection who false _ view)
          | succ rank =>
              cases view with
              | inl => rfl
              | inr view =>
                  simpa only [atRank, ProtocolView.historyProjection, Bool.false_eq_true,
                    ↓reduceIte, eraseHistory, Sum.elim_inr, Option.map_map,
                    Function.comp_def] using congrArg (Option.map Sum.inr) (ih rank view)

/-- Current history erasure leaves the observable cursor position unchanged. -/
theorem ProtocolView.position_historyProjection (who : Player) (remember : Bool) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (view : ProtocolView who program),
      position who program (historyProjection who program remember view) =
        position who program view := by
  cases remember with
  | true => intro Γ O program view; rfl
  | false =>
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
      | reveal published owner name fresh source unresolved next ih =>
          intro view
          cases view with
          | inl => rfl
          | inr view => exact congrArg (fun index => index + 1) (ih view)

/-- Memory projection does not change whether the current instruction commits. -/
@[simp] theorem ProtocolView.atCommit_historyProjection (who : Player) (remember : Bool)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (view : ProtocolView who program) :
    atCommit who program (historyProjection who program remember view) =
      atCommit who program view := by
  cases remember with
  | true => rfl
  | false => exact atCommit_eraseHistory who program view

/-- The actual information retained when comparing source instruction chunks. -/
inductive SourceViewProjection where
  | memory (remember : Bool)
  | publicOnly

/-- Project a genuine typed view without changing its cursor. Public projection
is used only for older chunks whose private declarations have been voided. -/
def SourceViewProjection.apply (projection : SourceViewProjection) (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (view : ProtocolView who program) : ProtocolView who program :=
  match projection with
  | .memory remember => ProtocolView.historyProjection who program remember view
  | .publicOnly => ProtocolView.publicOnly who program view

/-- Both concrete projections retain the same original public observation. -/
@[simp] theorem SourceViewProjection.publicOnly_apply (projection : SourceViewProjection)
    (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (view : ProtocolView who program) :
    ProtocolView.publicOnly who program (projection.apply who program view) =
      ProtocolView.publicOnly who program view := by
  cases projection with
  | memory remember => exact ProtocolView.publicOnly_historyProjection who program remember view
  | publicOnly => exact ProtocolView.publicOnly_idempotent who program view

/-- Project the current source signal, retaining all original public controls. -/
def Setup.commitRecoveryObservationSignal (setup : Setup (Player := Player) (L := L))
    (who : Player) (projection : SourceViewProjection)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :=
  (signal.1.map (projection.apply who setup.program), signal.2)

/-- Apply the same concrete projection to every genuine source signal. -/
def Setup.commitRecoveryObservedRecall (setup : Setup (Player := Player) (L := L))
    (who : Player) (projection : SourceViewProjection) {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (recall : setup.commitRecoverySignals.InfoState who) :=
  Prod.map (observe ∘ setup.commitRecoveryObservationSignal who projection)
    (List.map (observe ∘ setup.commitRecoveryObservationSignal who projection)) recall

/-- Project only the remembered part of the current source signal. Exclusion,
generation and the actual saved boundary remain literal. -/
def Setup.commitRecoveryHistorySignal (setup : Setup (Player := Player) (L := L))
    (who : Player) (remember : Bool)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :=
  (signal.1.map (ProtocolView.historyProjection who setup.program remember), signal.2)

/-- Keeping the remembered word is the identity on the actual current signal. -/
@[simp] theorem Setup.commitRecoveryHistorySignal_true
    (setup : Setup (Player := Player) (L := L)) (who : Player)
    (signal : setup.ProtocolView who × (Finset Player × Nat × Nat)) :
    setup.commitRecoveryHistorySignal who true signal = signal := by
  rcases signal with ⟨view, control⟩
  cases view <;> rfl

/-- Apply the selected current-memory projection before observing the complete
signal recall. Public-only observations may discard all earlier private words. -/
def Setup.commitRecoveryProjectedRecall (setup : Setup (Player := Player) (L := L))
    (who : Player) (remember : Bool) {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (recall : setup.commitRecoverySignals.InfoState who) :=
  Prod.map (observe ∘ setup.commitRecoveryHistorySignal who remember)
    (List.map (observe ∘ setup.commitRecoveryHistorySignal who remember)) recall
/-- Retaining the current word leaves the chosen observation of recall literal. -/
@[simp] theorem Setup.commitRecoveryProjectedRecall_true
    (setup : Setup (Player := Player) (L := L)) (who : Player) {Observation : Type*}
    (observe : setup.ProtocolView who × (Finset Player × Nat × Nat) → Observation)
    (recall : setup.commitRecoverySignals.InfoState who) :
    setup.commitRecoveryProjectedRecall who true observe recall =
      Prod.map observe (List.map observe) recall := by
  have functions : observe ∘ setup.commitRecoveryHistorySignal who true = observe := by
    funext signal
    rw [Function.comp_apply, setup.commitRecoveryHistorySignal_true]
  simp only [commitRecoveryProjectedRecall, functions]


end Vegas.SourceProgram
