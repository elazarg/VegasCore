/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationEnvironment
import Vegas.Pending.ContinuationDisclosure
import Vegas.Pending.Invariant

/-! # Whole-graph wire invocations at initialized compiled executions -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Every wire invocation preserves the honest residual law at an actually
reached cursor, for the full typed graph language and every adaptive wire
policy. This is a one-invocation law: the service's expiry actions require a
separate no-expiry argument for unchanged players. -/
theorem continuationAt_initialized_wire
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ)
    (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies (runtime.compileProfile whole profile)
      environment schedule (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (wire : runtime.application.WirePolicy) :
    let follows := runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
      environment schedule _ execution (State.initial_follows whole input) reached
    runtime.continuationAt whole profile execution.principalHistory
        execution.native.application follows =
      (runtime.application.invoke (runtime.compileProfile whole profile)
        (runtime.application.wireEnvironment wire) execution .environment).bindOnSupport
        fun after supported => runtime.continuationAt whole profile after.principalHistory
          after.native.application
          (runtime.invoke_follows whole 0 (runtime.compileProfile whole profile)
            (runtime.application.wireEnvironment wire) .environment
            execution after follows supported) := by
  dsimp only
  have follows := runtime.runPolicies_follows whole 0 (runtime.compileProfile whole profile)
    environment schedule _ execution (State.initial_follows whole input) reached
  have agreement := runtime.runPolicies_preserves_publicAgreement
    (runtime.compileProfile whole profile) environment schedule _ execution
    (State.initial_publicAgreement whole input) reached
  obtain ⟨target, suffix, site, ideal, values, bindings, candidates, clock, enteredAt,
      walk, atCursor⟩ := (show execution.native.application.Follows whole 0 from follows)
  simp only [Nat.zero_add] at atCursor
  rw [atCursor] at agreement
  change (values : PublicValues target) = (PublicValues.ofVEnv ideal : PublicValues target)
    at agreement
  rw [agreement] at atCursor
  cases suffix with
  | ret output =>
      apply runtime.continuationAt_wire_of_handle_stutter whole profile execution follows
        (runtime.compileProfile whole profile) wire
      intro message next handled
      simp [atCursor, GraphRuntime.handle] at handled
  | sample name fresh law tail =>
      apply runtime.continuationAt_wire_of_handle_stutter whole profile execution follows
        (runtime.compileProfile whole profile) wire
      intro message next handled
      simp [atCursor, GraphRuntime.handle] at handled
  | bind name owner fresh tail =>
      have invariant := runtime.runPolicies_initial_preparationInvariant whole input owner
        (profile owner) (runtime.compileProfile whole profile) rfl environment schedule
        execution reached
      exact walk.continuationAt_bind_wire_initialized runtime whole profile site name owner fresh
        tail input (runtime.compileProfile whole profile) rfl environment schedule execution reached
        ideal (PublicValues.ofVEnv ideal) bindings candidates clock enteredAt atCursor follows
        invariant (walk.target_names_nodup unique) wire
  | resolve outputName owner bindingName fresh source checks tail =>
      exact walk.continuationAt_resolve_wire runtime whole profile input unique discipline site
        outputName bindingName owner fresh source checks tail execution ideal bindings candidates
        clock enteredAt atCursor follows (runtime.compileProfile whole profile) rfl
        environment schedule reached wire

/-- info: 'Vegas.GraphRuntime.continuationAt_initialized_wire' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.continuationAt_initialized_wire

end Vegas.GraphRuntime
