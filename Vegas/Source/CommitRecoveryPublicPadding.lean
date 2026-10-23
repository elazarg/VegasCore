/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.CommitRecoveryPublicHistory

/-! # Retained public typed image from an observable source cursor -/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolView

private def publicEntry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (view : SourceObservation L who Γ) :
    ProtocolView who program :=
  match program with
  | .ret _ => (view.publicOnly, [])
  | .sample _ _ _ _ | .commit _ _ _ _ _ | .reveal _ _ _ _ _ _ _ =>
      .inl (view.publicOnly, [])

/-- Extend only through the current private commitment interval. This is a
readback on existing typed observations, not a source transition or query at
an invented played information state. All current private cells are erased. -/
def publicPadding (who : Player) :
    {Γ : SourceCtx Player L} → {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
      ProtocolView who program → ProtocolView who program
  | _, _, .ret _, view => (view.1.publicOnly, [])
  | _, _, .sample _ _ _ next, view => view.elim
      (fun current => .inl (current.1.publicOnly, []))
      (fun later => .inr (publicPadding who next later))
  | _, _, .commit (payload := payload) name owner _ _ next, view => view.elim
      (fun current =>
        let later : SourceObservation L who ((name, .commitment owner payload) :: _) :=
          ⟨Env.cons none current.1.publicOnly.cells⟩
        .inr (publicPadding who next (publicEntry who next later)))
      (fun later => .inr (publicPadding who next later))
  | _, _, .reveal _ _ _ _ _ _ next, view => view.elim
      (fun current => .inl (current.1.publicOnly, []))
      (fun later => .inr (publicPadding who next later))

/-- Public padding never reads the private cells or the old action word. -/
theorem publicPadding_publicOnly (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (view : ProtocolView who program),
      publicPadding who program (publicOnly who program view) = publicPadding who program view
  | _, _, .ret _, view => by simp only [publicPadding, publicOnly,
      SourceObservation.publicOnly_idempotent]
  | _, _, .sample _ _ _ next, view => by
      cases view with
      | inl => simp only [publicPadding, publicOnly, Sum.elim_inl,
          SourceObservation.publicOnly_idempotent]
      | inr view => exact congrArg Sum.inr (publicPadding_publicOnly who next view)
  | _, _, .commit _ _ _ _ next, view => by
      cases view with
      | inl => simp only [publicPadding, publicOnly, Sum.elim_inl,
          SourceObservation.publicOnly_idempotent]
      | inr view => exact congrArg Sum.inr (publicPadding_publicOnly who next view)
  | _, _, .reveal _ _ _ _ _ _ next, view => by
      cases view with
      | inl => simp only [publicPadding, publicOnly, Sum.elim_inl,
          SourceObservation.publicOnly_idempotent]
      | inr view => exact congrArg Sum.inr (publicPadding_publicOnly who next view)

/-- Discarding the old private word leaves the entire retained public image unchanged. -/
theorem publicPadding_eraseHistory (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (view : ProtocolView who program) :
    publicPadding who program (eraseHistory who program view) =
      publicPadding who program view := by
  calc
    _ = publicPadding who program (publicOnly who program
        (eraseHistory who program view)) := (publicPadding_publicOnly who program _).symm
    _ = publicPadding who program (publicOnly who program view) :=
      congrArg (publicPadding who program) (publicOnly_eraseHistory who program view)
    _ = _ := publicPadding_publicOnly who program view

private theorem publicEntry_congr (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (first second : SourceObservation L who Γ) (same : first.publicOnly = second.publicOnly) :
    publicEntry who program first = publicEntry who program second := by
  cases program <;> simp only [publicEntry, same]

private theorem publicEntry_observe (who : Player) {Γ : SourceCtx Player L}
    {O : Finset VarId} (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    publicEntry who program (sourceObserve who config.state) =
      publicOnly who program (ProtocolState.observe who program (ProtocolState.entry program
        config)) := by
  cases program <;> rfl

omit [IExpr.ResultTypes L] in
private theorem public_automatic (who owner : Player) {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (config : Config Player L Γ) :
    (⟨Env.cons none (sourceObserve who config.state).publicOnly.cells⟩ :
      SourceObservation L who ((name, .commitment owner payload) :: Γ)).publicOnly =
      (sourceObserve who (automaticCommit name owner payload config).state).publicOnly := by
  apply congrArg SourceObservation.mk
  funext cellName cell selected
  cases selected with
  | here => rfl
  | there selected => cases cell <;> rfl

/-- The observable padding is exactly the public projection of the existing
source automatic commitment image, at every real typed program point. -/
theorem publicPadding_observe (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
      (point : ProtocolState program),
      publicPadding who program (ProtocolState.observe who program point) =
        publicOnly who program (ProtocolState.observe who program
          (ProtocolState.automaticCommitBlock program point)) := by
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
      | inr point => exact congrArg Sum.inr (ih point)
      | inl config =>
          have entry : publicEntry who next
              (⟨Env.cons none (sourceObserve who config.state).publicOnly.cells⟩ :
                SourceObservation L who ((name, .commitment owner _) :: _)) =
              publicOnly who next (ProtocolState.observe who next (ProtocolState.entry next
                (automaticCommit name owner _ config))) := by
            exact (publicEntry_congr who next _ _ (public_automatic who owner name config)).trans
              (publicEntry_observe who next (automaticCommit name owner _ config))
          change Sum.inr (publicPadding who next (publicEntry who next
            (⟨Env.cons none (sourceObserve who config.state).publicOnly.cells⟩ :
              SourceObservation L who ((name, .commitment owner _) :: _)))) = _
          rw [entry]
          exact congrArg Sum.inr ((publicPadding_publicOnly who next _).trans (ih _))
  | reveal published owner name fresh selected unresolved next ih =>
      intro point
      cases point with
      | inl => rfl
      | inr point => exact congrArg Sum.inr (ih point)

end ProtocolView
end Vegas.SourceProgram
