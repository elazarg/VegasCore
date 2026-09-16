/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.DeviationServiceSafety

/-! # Expiry safety of the complete honest graph service plan

The structural service proof is shared with unilateral deviations. Fully
honest execution is the specialization with no exceptional owner. -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Expiry safety of the remaining honest service plan at an actually reached
typed graph cursor. -/
theorem servicePlan_expirySafe_from
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy)
    (before : List (ServiceInstruction Player)) (phase : Nat)
    (graph : Graph Player L Γ Δ) (walk : Prefix Δ whole graph phase)
    (execution : runtime.application.PolicyExecution)
    (reached : execution ∈ (runtime.application.runPolicies
      (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      (before.map ServiceInstruction.invocation)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input)))).support)
    (follows : execution.native.application.Follows graph phase)
    (cursor : execution.environmentHistory.length =
      (before.filterMap ServiceInstruction.environmentSlot).length) :
    ExpirySafe runtime (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment
        (before ++ runtime.servicePlan roster rounds graph phase) wire)
      (runtime.servicePlan roster rounds graph phase) execution := by
  have mixed := runtime.servicePlan_deviationExpirySafe_from whole profile input unique
    discipline none (runtime.compileProfile whole profile) (by
      intro owner _
      rfl) roster rounds wire before phase graph walk execution reached follows cursor
  intro expiryBefore nominal after split next supported
  rcases mixed expiryBefore nominal after split next supported with stale | sample | owned
  · exact Or.inl stale
  · exact Or.inr sample
  · cases stateEq : next.native.application with
    | running graph =>
        cases graph <;> simp [State.IsOwnedBy, stateEq] at owned

/-- The complete honest service plan is expiry-safe from the canonical graph
runtime initialization. -/
theorem servicePlan_expirySafe
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (profile : BehavioralProfile whole) (input : VEnv L Γ₀)
    (unique : (Γ₀.map Prod.fst).Nodup)
    (discipline : whole.BindingDiscipline BindingOrigins.none)
    (roster : List Player) (rounds : Nat) (wire : runtime.application.WirePolicy) :
    ExpirySafe runtime (runtime.compileProfile whole profile)
      (runtime.serviceEnvironment (runtime.servicePlan roster rounds whole 0) wire)
      (runtime.servicePlan roster rounds whole 0)
      (MessageApplication.PolicyExecution.initial runtime.application
        (MessageApplication.State.initial runtime.application
          (State.initial whole input))) := by
  apply runtime.servicePlan_expirySafe_from whole profile input unique discipline roster rounds
    wire [] 0 whole (Prefix.refl whole)
  · simp [MessageApplication.runPolicies]
  · exact State.initial_follows whole input
  · rfl

end Vegas.GraphRuntime
