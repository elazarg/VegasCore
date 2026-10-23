/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptReadout
import Vegas.Source.CommitRecoveryVirtualView

/-! # Virtual query identity at an ordinary live source cursor

Typed guard-rejected declarations remain ordinary values. Only an unusable
stored binding can change the current observation under virtual replacement.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
theorem virtualBindings_observe_eq {Γ : SourceCtx Player L} (who : Player)
    (preserved : Finset VarId) (config : Config Player L Γ)
    (values : config.BindingsHoldValues who) :
    (sourceObserve who config.state).virtualBindings preserved =
      sourceObserve who config.state := by
  apply congrArg SourceObservation.mk
  funext name cell selected
  cases cell with
  | publicData => rfl
  | publication => rfl
  | privateInput => rfl
  | commitment owner payload =>
      by_cases own : owner = who
      · subst owner
        obtain ⟨value, stored⟩ := values selected
        simp only [sourceObserve, ↓reduceIte,
          Option.map_some, stored, repairBinding]
        split <;> rfl
      · simp only [sourceObserve, own, ↓reduceIte,
          Option.map_none]

end Config

namespace ProtocolState

/-- At an ordinary current cursor, virtual replacement does nothing beyond
the existing private-word erasure. No condition is imposed on guard results,
excluded foreign owners, public failures or earlier proposals. -/
theorem virtualBindings_observe_eq (who : Player) (preserved : Finset VarId) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (point : ProtocolState program),
      BindingsHoldValues who program point →
        ProtocolView.virtualBindings who preserved program (observe who program point) =
          ProtocolView.eraseHistory who program (observe who program point)
  | _, _, .ret _, config, values =>
      congrArg (fun view => (view, []))
        (Config.virtualBindings_observe_eq who preserved config values)
  | _, _, .sample _ _ _ next, point, values => by
      cases point with
      | inl config =>
          exact congrArg Sum.inl (congrArg (fun view => (view, []))
            (Config.virtualBindings_observe_eq who preserved config values))
      | inr point =>
          exact congrArg Sum.inr (virtualBindings_observe_eq who preserved next point values)
  | _, _, .commit _ _ _ _ next, point, values => by
      cases point with
      | inl config =>
          exact congrArg Sum.inl (congrArg (fun view => (view, []))
            (Config.virtualBindings_observe_eq who preserved config values))
      | inr point =>
          exact congrArg Sum.inr (virtualBindings_observe_eq who preserved next point values)
  | _, _, .reveal _ _ _ _ _ _ next, point, values => by
      cases point with
      | inl config =>
          exact congrArg Sum.inl (congrArg (fun view => (view, []))
            (Config.virtualBindings_observe_eq who preserved config values))
      | inr point =>
          exact congrArg Sum.inr (virtualBindings_observe_eq who preserved next point values)

end ProtocolState
end Vegas.SourceProgram
