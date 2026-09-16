/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationAt
import Vegas.Pending.ContinuationStep
import Vegas.Pending.DisclosureAcceptance

/-! # Disclosure wire laws at actual initialized executions -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- At an actually reached disclosure cursor, arbitrary wire delivery and
inclusion preserve the residual outcome law when this node's owner is compiled.
The disclosure cache and exact accepted value are derived from the actual
emitting checkpoint, including when the wire accepts an earlier submission. -/
theorem Prefix.continuationAt_resolve_wire
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (site : Nat) (outputName bindingName : VarId) (owner : Player) {payload : L.Ty}
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck ((outputName, .pub (R.result payload)) :: Γ)))
    (tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (walk : Prefix Δ whole (.resolve outputName owner bindingName fresh source checks tail) site)
    (execution : runtime.application.PolicyExecution)
    (ideal : VEnv L Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat)
    (atCursor : execution.native.application =
      .running (.resolve outputName owner bindingName fresh source checks tail)
        ideal (PublicValues.ofVEnv ideal) bindings candidates site clock enteredAt)
    (follows : execution.native.application.Follows whole 0)
    (players : Player → runtime.application.PlayerPolicy)
    (ownerCompiled : players owner = runtime.compilePlayerPolicy whole owner (profile owner))
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (reached : execution ∈ (runtime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (wire : runtime.application.WirePolicy) :
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke players (runtime.application.wireEnvironment wire)
        execution .environment).bindOnSupport fun after supported =>
          runtime.continuationAt whole profile after.principalHistory after.native.application
            (runtime.invoke_follows whole 0 players (runtime.application.wireEnvironment wire)
              .environment execution after follows supported) := by
  apply runtime.continuationAt_wire whole profile execution follows players wire
  intro id message after lookup accepted
  obtain ⟨disclose, remembered, advanced⟩ :=
    runtime.accepted_initial_compiled_resolve_packet whole input unique discipline
      outputName bindingName owner fresh source checks tail (profile owner) players ownerCompiled
      environment schedule execution ideal bindings candidates site clock enteredAt message id
      after reached atCursor lookup accepted
  let successor : runtime.application.PolicyExecution :=
    { execution with native := { execution.native with application := after } }
  have afterFollows := runtime.handle_follows whole 0 execution.native.application after
    message follows accepted
  change runtime.continuationAt whole profile successor.principalHistory
    successor.native.application afterFollows = _
  rw [runtime.continuationAt_running whole profile successor afterFollows tail (site + 1)
    (walk.trans (.resolve (.refl tail)))
    (VEnv.cons ((R.valueEquiv payload).symm (acceptedResult source checks ideal disclose)) ideal)
    (PublicValues.consPublic ((R.valueEquiv payload).symm
      (acceptedResult source checks ideal disclose)) (PublicValues.ofVEnv ideal))
    bindings candidates clock clock advanced]
  rw [runtime.continuationAt_running whole profile execution follows
    (.resolve outputName owner bindingName fresh source checks tail) site walk ideal
    (PublicValues.ofVEnv ideal) bindings candidates clock enteredAt atCursor]
  exact (walk.continuation_resolve_advance runtime whole profile site outputName bindingName owner
    fresh source checks tail ideal execution.principalHistory disclose remembered
    (walk.target_names_nodup unique)).symm

end Vegas.GraphRuntime
