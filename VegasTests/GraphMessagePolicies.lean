/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PolicyLaws
import VegasTests.SourceSemantics

/-! # Executable checks for graph message policy projection -/

namespace VegasTests.GraphMessagePolicies

open Interaction Vegas Vegas.Graph Vegas.GraphRuntime
open VegasTests.SourceSemantics

noncomputable section

inductive Actor where
  | alice
  | bob
  deriving DecidableEq

abbrev FinalCtx : VCtx Actor simpleExpr :=
  [(2, .sealed .bob (.result .bool)), (1, .sealed .alice (.result .bool))]

def twoPlayerGraph : Graph Actor simpleExpr [] FinalCtx :=
  .bind 1 .alice (by simp) <|
    .bind 2 .bob (by simp) <|
      .ret []

def finalEnv : VEnv simpleExpr FinalCtx :=
  VEnv.cons (PublicationResult.success false)
    (VEnv.cons (PublicationResult.success true) (VEnv.empty simpleExpr))

abbrev runtime : GraphRuntime Actor simpleExpr FinalCtx where
  deadline := fun _ => 2

/-- The completed-bind projection reads immutable owned graph fields and omits
the other player's sealed choice. No preparation command history is needed. -/
theorem alice_completed_bind_history :
    projectLogicalHistory (runtime := runtime) .alice (Graph.observe .alice finalEnv) []
        twoPlayerGraph 0 2 =
      [OwnAction.bind .alice 1 simpleExpr.bool (.success true)] := by
  rfl

/-- Symmetrically, Bob sees and remembers only Bob's own graph action even
though Alice's bind precedes it in the fixed graph. -/
theorem bob_completed_bind_history :
    projectLogicalHistory (runtime := runtime) .bob (Graph.observe .bob finalEnv) []
        twoPlayerGraph 0 2 =
      [OwnAction.bind .bob 2 simpleExpr.bool (.success false)] := by
  rfl

/-- Initialization finds a sealed field behind another owner's field and
installs the exact corresponding verifier, without executing a new bind. -/
theorem initial_owned_field_verifier :
    let state := GraphRuntime.State.initial (Graph.ret [] : Graph Actor simpleExpr
      FinalCtx FinalCtx) finalEnv
    lookupBinding state.publicView.bindings 1 = some (.alice, .initial 1) ∧
      state.candidates.verify (.alice, .initial 1)
        ⟨.result .bool, PublicationResult.success true⟩ = true :=
  GraphRuntime.State.initial_binding (.ret []) finalEnv (by decide) (.there .here)

end
end VegasTests.GraphMessagePolicies
