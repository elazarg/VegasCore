/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceCompletion

/-! # Stopping a policy-driven service run at its first effective invocation

Unlike a native-action witness, this retains the actual policy executions,
their authenticated histories, and the supported residual run to the endpoint.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L] {Δ : VCtx Player L}

/-- An advancing supported service run contains an actual first phase-changing
invocation. Both its initialized prefix and its suffix to the supplied endpoint
remain supported runs under the same policies. -/
theorem exists_first_phaseChange_invocation (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (plan : List (ServiceInstruction Player))
    (execution final : runtime.application.PolicyExecution)
    (supported : final ∈ (runtime.application.runPolicies players environment
      (plan.map ServiceInstruction.invocation) execution).support)
    (advanced : execution.native.application.phase < final.native.application.phase) :
    ∃ before instruction rest, plan = before ++ instruction :: rest ∧
      ∃ prior next : runtime.application.PolicyExecution,
        prior ∈ (runtime.application.runPolicies players environment
          (before.map ServiceInstruction.invocation) execution).support ∧
        next ∈ (runtime.application.invoke players environment prior
          instruction.invocation).support ∧
        final ∈ (runtime.application.runPolicies players environment
          (rest.map ServiceInstruction.invocation) next).support ∧
        prior.native.application.phase = execution.native.application.phase ∧
        prior.native.application.phase < next.native.application.phase := by
  induction plan generalizing execution with
  | nil =>
      simp only [List.map_nil, MessageApplication.runPolicies,
        FinDist.mem_support_pure] at supported
      subst final
      exact (Nat.lt_irrefl _ advanced).elim
  | cons instruction rest ih =>
      simp only [List.map_cons, MessageApplication.runPolicies,
        FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, first, tail⟩ := supported
      have monotone := runtime.runPolicies_phase_mono players environment
        [instruction.invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using first)
      by_cases changed : execution.native.application.phase < middle.native.application.phase
      · exact ⟨[], instruction, rest, rfl, execution, middle,
          by simp [MessageApplication.runPolicies], first, tail, rfl, changed⟩
      · have same : middle.native.application.phase = execution.native.application.phase := by
          omega
        obtain ⟨before, effective, suffix, split, prior, next, priorRun, nextStep,
            finalRun, priorPhase, changed⟩ :=
          ih middle tail (by omega)
        refine ⟨instruction :: before, effective, suffix, ?_, prior, next, ?_,
          nextStep, finalRun, priorPhase.trans same, changed⟩
        · simp only [List.cons_append, split]
        · simp only [List.map_cons, MessageApplication.runPolicies,
            FinDist.support_bind, Set.mem_iUnion]
          exact ⟨middle, first, priorRun⟩

end Vegas.GraphRuntime
