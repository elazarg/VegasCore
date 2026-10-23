/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolTermination
import Vegas.Source.FiniteSupport

/-! # Agreement with source execution

The continuation law below selects the existing source runner at the current
program point. The protocol law agrees with it after every history, not only
from initialization. The horizon counts remaining source instructions; it is
not a renewed runtime deadline or service budget.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace ProtocolState

/-- Select the existing source continuation at this program point. -/
def continuationLaw : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (BehavioralProfile program) →
    ProtocolState program → PMF (State L program.terminalCtx)
  | _, _, .ret _ => fun _ config => PMF.pure config.state
  | _, _, .sample name fresh law next => fun profile =>
      Sum.elim
        (fun config => runFrom (.sample name fresh law next)
          profile config)
        (continuationLaw next profile)
  | _, _, .commit name owner fresh guard next => fun profile =>
      Sum.elim
        (fun config => runFrom (.commit name owner fresh guard next)
          profile config)
        (continuationLaw next (fun who => (profile who).2))
  | _, _, .reveal published owner name fresh source unresolved next => fun profile =>
      Sum.elim
        (fun config => runFrom (.reveal published owner name fresh source unresolved next)
          profile config)
        (continuationLaw next (fun who => (profile who).2))

@[simp] theorem continuationLaw_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (profile : BehavioralProfile program)
    (config : Config Player L Γ) :
    continuationLaw program profile (entry program config) =
      runFrom program profile config := by
  cases program <;> rfl

/-- Read a terminal store only at a return point. -/
def readout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    Option (State L program.terminalCtx)
  | _, _, .ret _ => fun config => some config.state
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun _ => none) (readout next)

/-- A finitely branching profile has a finitely supported continuation at every
protocol state. -/
theorem continuationLaw_support_finite : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    BehavioralProfile.FiniteSupport program profile → (state : ProtocolState program) →
    (continuationLaw program profile state).support.Finite
  | _, _, .ret _, _, _, config => by simp [continuationLaw]
  | _, _, .sample _ _ _ next, profile, finite, state => by
      cases state with
      | inl config => exact runFrom_support_finite _ profile finite config
      | inr rest => exact continuationLaw_support_finite next profile finite rest
  | _, _, .commit _ _ _ _ next, profile, finite, state => by
      cases state with
      | inl config => exact runFrom_support_finite _ profile finite config
      | inr rest => exact continuationLaw_support_finite next _ finite.2 rest
  | _, _, .reveal _ _ _ _ _ _ next, profile, finite, state => by
      cases state with
      | inl config => exact runFrom_support_finite _ profile finite config
      | inr rest => exact continuationLaw_support_finite next _ finite rest

theorem continuationLaw_terminal : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (profile : BehavioralProfile program) →
    (state : ProtocolState program) → terminal program state →
    (continuationLaw program profile state).map some = PMF.pure (readout program state)
  | _, _, .ret _, _, _, _ => PMF.pure_map _ _
  | _, _, .sample _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next profile rest stopped
  | _, _, .commit _ _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next (fun who => (profile who).2) rest stopped
  | _, _, .reveal _ _ _ _ _ _ next, profile, state, stopped => by
      cases state with
      | inl config => exact stopped.elim
      | inr rest => exact continuationLaw_terminal next (fun who => (profile who).2) rest stopped

end ProtocolState

end Vegas.SourceProgram
