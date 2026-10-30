/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProtocolTermination

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
    ProtocolState program → PMF (Config Player L program.terminalCtx)
  | _, _, .ret _ => fun _ config => PMF.pure config
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
    Option (Config Player L program.terminalCtx)
  | _, _, .ret _ => fun config => some config
  | _, _, .sample _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .commit _ _ _ _ next => Sum.elim (fun _ => none) (readout next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim (fun _ => none) (readout next)

/-- Reading a retained terminal configuration returns every field unchanged. -/
@[simp] theorem readout_terminalState : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (config : Config Player L program.terminalCtx) →
    readout program (terminalState program config) = some config
  | _, _, .ret _, _ => rfl
  | _, _, .sample _ _ _ next, config => readout_terminalState next config
  | _, _, .commit _ _ _ _ next, config => readout_terminalState next config
  | _, _, .reveal _ _ _ _ _ _ next, config => readout_terminalState next config

/-- Terminal protocol points retain exactly their readout configuration. -/
theorem terminalState_readout : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    terminal program state → (readout program state).map (terminalState program) = some state
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr state =>
          simpa only [readout, Sum.elim_inr, terminalState, Option.map_map,
            Option.map_some, Function.comp_def] using
            congrArg (Option.map Sum.inr) (terminalState_readout next state stopped)
  | _, _, .commit _ _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr state =>
          simpa only [readout, Sum.elim_inr, terminalState, Option.map_map,
            Option.map_some, Function.comp_def] using
            congrArg (Option.map Sum.inr) (terminalState_readout next state stopped)
  | _, _, .reveal _ _ _ _ _ _ next, state, stopped => by
      cases state with
      | inl _ => exact stopped.elim
      | inr state =>
          simpa only [readout, Sum.elim_inr, terminalState, Option.map_map,
            Option.map_some, Function.comp_def] using
            congrArg (Option.map Sum.inr) (terminalState_readout next state stopped)

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
