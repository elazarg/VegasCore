/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceLaw

/-! # Exact timed continuations at supported source boundaries

The existing joint prefix induction also starts at an arbitrary supported
typed checkpoint. Its terminal marginal preserves the entire typed source
store, including persistent initial parameters and public outcomes. The
physical continuation uses the existing remaining service blocks.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- One source step followed by the source continuation is the source
continuation. -/
theorem sourceStep_continuation
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (profile : BehavioralProfile program)
    (state : ProtocolState program) :
    (ProtocolState.behavioralStateStep program profile state).bind
      (ProtocolState.continuationLaw program profile) =
        ProtocolState.continuationLaw program profile state := by
  classical
  unfold ProtocolState.behavioralStateStep
  split
  · exact PMF.pure_bind _ _
  · rename_i running
    exact ProtocolState.continuationLaw_behavioral_step program profile state running
      (independentProduct fun who => (profile who).protocolAction program
        (ProtocolState.observe who program state)) (fun who => independentProduct_map_eval _ who)

end Vegas
