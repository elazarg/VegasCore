/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageContinuation
import Vegas.Graph.MessagePolicyLaws

/-! # Compiled-policy continuation identities -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- At an arbitrary typed bind cursor, invoking the owner under the policy
compiled from the original graph satisfies the continuation Bellman identity. -/
theorem continuation_bind_compiled_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (name : VarId) (owner : Player) {payload : L.Ty} (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.bind name owner fresh next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (execution : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.bind name owner fresh next) ideal values bindings candidates site clock enteredAt)
    (missing : preparedRaw (execution.principalHistory owner) site = none)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (environment : runtime.application.EnvironmentPolicy) :
    let residual := walk.profileTail profile
    let logical : History Player L := fun who =>
      projectLogicalHistory who (observe who ideal) (execution.principalHistory who) whole 0 site
    continuation runtime (.bind name owner fresh next) residual site ideal logical
        execution.principalHistory =
      (runtime.application.invoke (runtime.compileProfile whole profile) environment execution
        (.player owner)).bind fun after =>
          continuation runtime (.bind name owner fresh next) residual site ideal logical
            after.principalHistory := by
  dsimp only
  rcases execution with ⟨⟨application, pool, receipts⟩, principalHistory,
    environmentHistory, nativeTrace⟩
  dsimp only at atCursor ⊢
  subst application
  let execution : runtime.application.PolicyExecution :=
    ⟨⟨.running (.bind name owner fresh next) ideal values bindings candidates site clock enteredAt,
      pool, receipts⟩, principalHistory, environmentHistory, nativeTrace⟩
  apply continuation_bind_invoke runtime name owner fresh next (walk.profileTail profile) site
    ideal _ (runtime.compileProfile whole profile) environment execution missing
  let view := Interaction.MessageApplication.State.observe runtime.application
    execution.native owner
  have hpc : view.application.publicState.pc = site := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hwho : view.application.who = owner := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hΓ : view.application.publicState.Γ = Γ := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hobs : hΓ ▸ (hwho ▸ view.application.privateObservation) = observe owner ideal := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  rw [show runtime.compileProfile whole profile owner =
      runtime.compilePlayerPolicy whole owner (profile owner) by rfl]
  rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner)
    (execution.principalHistory owner) view hpc]
  rw [compileAt_bind_fresh runtime whole site name owner fresh next
    (walk.policyTail owner (profile owner)) _ view hpc hwho hΓ missing unsubmitted]
  rw [hobs]
  rfl

/-- At an arbitrary typed resolve cursor, invoking the owner under the policy
compiled from the original graph satisfies the continuation Bellman identity.

Like the bind theorem, this is an honest compiled-policy law. An arbitrary
focal deviation may forge private cache markers, so deviation backtranslation
must validate or extract its graph action rather than apply this cached
continuation theorem unchanged. -/
theorem continuation_resolve_compiled_invoke
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (site : Nat)
    (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole
      (.resolve outputName owner bindingName fresh source checks next) site)
    (ideal : VEnv L Γ) (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (execution : runtime.application.PolicyExecution)
    (atCursor : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks next)
        ideal values bindings candidates site clock enteredAt)
    (missing : rememberedDisclosure (execution.principalHistory owner) site = none)
    (unsubmitted : submittedAt (execution.principalHistory owner) site = false)
    (environment : runtime.application.EnvironmentPolicy) :
    let residual := walk.profileTail profile
    let logical : History Player L := fun who =>
      projectLogicalHistory who (observe who ideal) (execution.principalHistory who) whole 0 site
    continuation runtime
        (.resolve outputName owner bindingName fresh source checks next)
        residual site ideal logical execution.principalHistory =
      (runtime.application.invoke (runtime.compileProfile whole profile) environment execution
        (.player owner)).bind fun after =>
          continuation runtime
            (.resolve outputName owner bindingName fresh source checks next)
            residual site ideal logical after.principalHistory := by
  dsimp only
  rcases execution with ⟨⟨application, pool, receipts⟩, principalHistory,
    environmentHistory, nativeTrace⟩
  dsimp only at atCursor ⊢
  subst application
  let execution : runtime.application.PolicyExecution :=
    ⟨⟨.running (.resolve outputName owner bindingName fresh source checks next)
      ideal values bindings candidates site clock enteredAt, pool, receipts⟩,
      principalHistory, environmentHistory, nativeTrace⟩
  apply continuation_resolve_invoke runtime outputName bindingName owner fresh source checks next
    (walk.profileTail profile) site ideal _ (runtime.compileProfile whole profile) environment
    execution missing
  · simp [execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  let view := Interaction.MessageApplication.State.observe runtime.application
    execution.native owner
  have hpc : view.application.publicState.pc = site := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hwho : view.application.who = owner := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hΓ : view.application.publicState.Γ = Γ := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  have hobs : hΓ ▸ (hwho ▸ view.application.privateObservation) = observe owner ideal := by
    simp [view, execution, Interaction.MessageApplication.State.observe,
      GraphRuntime.application, State.playerView]
  rw [show runtime.compileProfile whole profile owner =
      runtime.compilePlayerPolicy whole owner (profile owner) by rfl]
  rw [Prefix.compilePlayerPolicy_eq_suffix walk owner (profile owner)
    (execution.principalHistory owner) view hpc]
  rw [compileAt_resolve_fresh runtime whole site outputName bindingName owner fresh source checks
    next (walk.policyTail owner (profile owner)) _ view hpc hwho hΓ missing unsubmitted]
  rw [hobs]
  rfl

end Vegas.GraphRuntime
