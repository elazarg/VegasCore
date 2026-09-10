/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.MessageApplicationPolicyLaws
import Interaction.SealedApplication
import Vegas.Compile.SealedSource

/-! # Native public-message policy executions and the checked source

The bounded policy game runs the compiled application through its native
transition function. Every outcome in its support has an actual native action
trace, so the operational source theorem applies to adversarial policies too.
The conclusion remains support-level and conditional on graph termination;
it supplies neither a source policy nor a settlement guarantee.
-/

namespace Vegas.WFProgram

open EventGraph Interaction Interaction.SealedProgram
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Every supported policy-game execution is a graph prefix of the actual
checked compilation; terminal prefixes reconstruct the written source with
all terminal bindings and its payout evaluation. -/
theorem sealed_policy_source (source : WFProgram Player L) (ty : L.Ty)
    [DecidableEq (L.Val ty)]
    (supported : SealedFragment (ToEventGraph.compile source.core).graph ty)
    (players : Player →
      (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment :
      (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution :
      (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmem : execution ∈
      ((MessageApplication.policyGame
        (supported.compile.messageApplication (Value := L.Val ty)) environment schedule
        (MessageApplication.State.initial
          (supported.compile.messageApplication (Value := L.Val ty))
          ⟨IdealCommitments.empty, []⟩)).play players).support) :
    ∃ cfg : Config (ToEventGraph.compile source.core).graph,
      (ToEventGraph.compile source.core).graph.decodeSealed ty
        (supported.compile.eraseReceipts execution.native) = some cfg ∧
      Reachable (ToEventGraph.compile source.core).graph cfg ∧
      (Terminal (ToEventGraph.compile source.core).graph cfg →
        ∃ terminalEnv : VEnv L (ToEventGraph.compile source.core).terminalCtx,
          SmallStep.Star
            { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
            { ctx := (ToEventGraph.compile source.core).terminalCtx,
              env := terminalEnv, cont := .ret (ToEventGraph.compile source.core).sourcePayoffs } ∧
          evalPayoffs? (ToEventGraph.compile source.core).payoffs cfg.store =
            some (evalPayoffs (ToEventGraph.compile source.core).sourcePayoffs terminalEnv) ∧
          ∀ {name bindTy}
            (h : VHasVar (ToEventGraph.compile source.core).terminalCtx name bindTy),
            Store.getAs cfg.store
              ((ToEventGraph.compile source.core).terminalState.fieldOf h) bindTy.base =
                some (terminalEnv.get h)) := by
  let app := supported.compile.messageApplication (Value := L.Val ty)
  let initialApplication : app.Application := ⟨IdealCommitments.empty, []⟩
  let initial := MessageApplication.State.initial app initialApplication
  have hnative := app.runPolicies_initial_native_support players environment schedule
    initial execution hmem
  have herased : supported.compile.eraseReceipts execution.native ∈
      ((app.run execution.nativeTrace initial).map supported.compile.eraseReceipts).support := by
    rw [FinDist.support_map]
    exact ⟨execution.native, hnative, rfl⟩
  rw [supported.compile.run_eraseReceipts] at herased
  simp only [FinDist.mem_support_pure] at herased
  rw [herased]
  exact source.sealed_run_source ty supported
    (execution.nativeTrace.map supported.compile.nativeAction)

end Vegas.WFProgram
