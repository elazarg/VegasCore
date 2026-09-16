/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationService
import Vegas.Pending.ServiceTermination
import Vegas.Pending.ServiceSafetyComposition
import Vegas.Pending.ServiceSafety

/-! # Outcome laws of the serviced graph compiler -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A complete initialized plan conserves the graph's outcome law if each
of its expiry slots either waits or performs a chance step. The condition is
checked at the actual prefix of the complete plan, with all histories intact. -/
theorem runPolicies_continuation_of_safe_expiry (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (input : VEnv L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (plan : List (ServiceInstruction Player)) (wire : runtime.application.WirePolicy)
    (safe : runtime.ExpirySafe (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment plan wire) plan
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole input)))) :
    let players := runtime.compileProfile whole profile
    let environment := runtime.serviceEnvironment plan wire
    let initial := MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application (State.initial whole input))
    (runtime.application.runPolicies players environment
      (plan.map ServiceInstruction.invocation) initial).bindOnSupport
      (fun execution supported => runtime.continuationAt whole profile
        execution.principalHistory execution.native.application
        (runtime.runPolicies_follows whole 0 players environment _ initial execution
          (State.initial_follows whole input) supported)) = Graph.run whole profile input := by
  dsimp only
  rw [← runtime.continuationAt_initial whole profile input]
  apply runtime.application.runPolicies_map_bindOnSupport_conservation
    ServiceInstruction.invocation plan
    (fun execution => execution.native.application.Follows whole 0)
    (fun execution follows => runtime.continuationAt whole profile execution.principalHistory
      execution.native.application follows)
    (runtime.compileProfile whole profile) (runtime.serviceEnvironment plan wire)
    _ (State.initial_follows whole input)
    (fun instruction execution follows next supported => runtime.invoke_follows whole 0
      (runtime.compileProfile whole profile) (runtime.serviceEnvironment plan wire)
      instruction.invocation execution next follows supported)
  intro before instruction after split execution reached follows
  have cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length := by
    simpa only [MessageApplication.PolicyExecution.initial, List.length_nil, Nat.zero_add] using
      runtime.runPolicies_service_cursor (runtime.compileProfile whole profile)
        (runtime.serviceEnvironment plan wire) before _ execution reached
  have slot (environmentSlot : instruction.environmentSlot = some instruction) :
      (plan.filterMap ServiceInstruction.environmentSlot)[execution.environmentHistory.length]? =
        some instruction := by
    rw [split, cursor]
    exact ServiceInstruction.environmentSlot_at before after instruction environmentSlot
  symm
  cases instruction with
  | player actor =>
      exact runtime.continuationAt_compiled_player_invoke whole profile execution follows
        (runtime.compileProfile whole profile) (runtime.serviceEnvironment plan wire) actor rfl
  | wire =>
      exact runtime.continuationAt_initialized_serviceWire whole profile input unique discipline
        (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
        execution reached plan wire (slot rfl)
  | includeLatest owner =>
      exact runtime.continuationAt_initialized_includeLatest whole profile input unique discipline
        (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
        execution reached plan wire owner (slot rfl)
  | expire phase =>
      exact runtime.continuationAt_initialized_expire whole profile input unique
        (runtime.serviceEnvironment plan wire) (before.map ServiceInstruction.invocation)
        execution reached plan wire phase (slot rfl)
        (safe before phase after split execution reached)

/-- At termination, conservation of the graph continuation determines the
actual optional outcome law. No outcome is supplied for a missing execution. -/
theorem outcome_map_of_continuation (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (executions : FinDist runtime.application.PolicyExecution)
    (follows : ∀ execution ∈ executions.support,
      execution.native.application.Follows whole 0)
    (completed : ∀ execution ∈ executions.support,
      execution.native.application.outcome?.isSome = true) :
    executions.map (fun execution => execution.native.application.outcome?) =
      (executions.bindOnSupport fun execution supported =>
        runtime.continuationAt whole profile execution.principalHistory
          execution.native.application (follows execution supported)).map some := by
  rw [FinDist.map_bindOnSupport]
  symm
  rw [FinDist.map_eq_bind]
  apply FinDist.bindOnSupport_eq_bind_of_eq_on_support
  intro execution supported
  obtain ⟨output, terminal⟩ := Option.isSome_iff_exists.mp (completed execution supported)
  rw [runtime.continuationAt_terminal whole profile execution.principalHistory
    execution.native.application (follows execution supported) output terminal]
  simp only [FinDist.map_pure, terminal]

/-- Honest compiled play of the complete concrete service plan has exactly
the graph outcome law, for every adaptive wire policy and reaction roster. -/
theorem servicePlan_honest_law (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (input : VEnv L Γ) (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy) :
    (runtime.application.runPolicies (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment (runtime.servicePlan roster reactionRounds whole 0) wire)
      ((runtime.servicePlan roster reactionRounds whole 0).map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application (State.initial whole input)))).map
      (fun execution => execution.native.application.outcome?) =
      (Graph.run whole profile input).map some := by
  let plan := runtime.servicePlan roster reactionRounds whole 0
  let players := runtime.compileProfile whole profile
  let environment := runtime.serviceEnvironment plan wire
  let initial := MessageApplication.PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application (State.initial whole input))
  let executions := runtime.application.runPolicies players environment
    (plan.map ServiceInstruction.invocation) initial
  have follows : ∀ execution ∈ executions.support,
      execution.native.application.Follows whole 0 := fun execution supported =>
    runtime.runPolicies_follows whole 0 players environment _ initial execution
      (State.initial_follows whole input) supported
  have completed : ∀ execution ∈ executions.support,
      execution.native.application.outcome?.isSome = true := fun execution supported =>
    runtime.servicePlan_terminates whole input roster reactionRounds players wire
      execution supported
  rw [runtime.outcome_map_of_continuation whole profile executions follows completed]
  rw [runtime.runPolicies_continuation_of_safe_expiry whole profile input unique discipline plan
    wire (runtime.servicePlan_expirySafe whole profile input unique discipline
      roster reactionRounds wire)]

/-- The graph-to-message compiler preserves the honest outcome law with one
profile shared across a finite initial-state distribution. -/
theorem servicedGame_honest_law (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (inputs : FinDist (VEnv L Γ)) (unique : (Γ.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (reactionRounds : Nat) (wire : runtime.application.WirePolicy) :
    ((runtime.servicedGame whole inputs roster reactionRounds wire).play
      (runtime.compileProfile whole profile)).map (fun execution =>
        execution.native.application.outcome?) =
      (inputs.bind fun input => Graph.run whole profile input).map some := by
  simp only [servicedGame, FinDist.map_bind]
  apply FinDist.bind_congr
  intro input _
  exact runtime.servicePlan_honest_law whole profile input unique discipline
    roster reactionRounds wire

/-- info: 'Vegas.GraphRuntime.servicedGame_honest_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.servicedGame_honest_law

end Vegas.GraphRuntime
