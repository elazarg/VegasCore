/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.Continuation

/-! # Continuation frames for message traffic

Submitting, replaying, or waiting records a native command without changing
the compiled policy's cached graph decisions. These equations keep the typed
graph cursor, ideal environment, and logical history fixed; phase-advancing
application transitions require the separate continuation step laws.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

private theorem continuation_append_nonprivate
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (profile : BehavioralProfile graph) (site : Nat) (env : VEnv L Γ)
    (logical : History Player L) (histories : Player → List (Entry runtime))
    (who : Player) (before : runtime.application.View) (command : Command runtime)
    (nonprivate : ∀ privateAction, command ≠ .privateCommand privateAction) :
    continuation runtime graph profile site env logical
        (Function.update histories who (histories who ++ [⟨before, command⟩])) =
      continuation runtime graph profile site env logical histories := by
  apply continuation_congr_histories
  · intro actor queried _lower payload
    by_cases same : actor = who
    · subst actor
      simp only [Function.update_self]
      cases command with
      | privateCommand privateAction => exact False.elim (nonprivate privateAction rfl)
      | submit | replay | wait =>
          simp [preparedChoice, preparedRaw, List.findSome?_append]
    · simp [Function.update, same]
  · intro actor queried _lower
    by_cases same : actor = who
    · subst actor
      simp only [Function.update_self]
      apply rememberedDisclosure_append_of_entry_none
      cases command with
      | privateCommand privateAction => exact False.elim (nonprivate privateAction rfl)
      | submit | replay | wait => rfl
    · simp [Function.update, same]

/-- Every supported non-private player step preserves the fixed-cursor
continuation. The player and packet are arbitrary; this includes replay and
malformed submission. -/
theorem continuation_playerStep_nonprivate
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (profile : BehavioralProfile graph) (site : Nat) (env : VEnv L Γ)
    (logical : History Player L) (who : Player)
    (execution after : runtime.application.PolicyExecution) (command : Command runtime)
    (nonprivate : ∀ privateAction, command ≠ .privateCommand privateAction)
    (supported : after ∈ (runtime.application.playerStep who execution command).support) :
    continuation runtime graph profile site env logical after.principalHistory =
      continuation runtime graph profile site env logical execution.principalHistory := by
  have histories : after.principalHistory = Function.update execution.principalHistory who
      (execution.principalHistory who ++
        [⟨MessageApplication.State.observe runtime.application execution.native who,
          command⟩]) := by
    funext actor
    by_cases same : actor = who
    · subst actor
      simp only [Function.update_self]
      exact runtime.application.playerStep_history_self who execution command after supported
    · simpa [Function.update, same] using
        runtime.application.playerStep_other_history who actor same execution command after
          supported
  rw [histories]
  exact continuation_append_nonprivate runtime graph profile site env logical
    execution.principalHistory who _ command nonprivate

/-- An invocation which emits only public traffic or waits satisfies the
fixed-cursor continuation equation without any restriction on that traffic's
distribution. -/
theorem continuation_invoke_nonprivate
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (profile : BehavioralProfile graph) (site : Nat) (env : VEnv L Γ)
    (logical : History Player L) (who : Player)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution)
    (nonprivate : ∀ command ∈ (players who (execution.principalHistory who)
      (MessageApplication.State.observe runtime.application execution.native who)).support,
      ∀ privateAction, command ≠ .privateCommand privateAction) :
    continuation runtime graph profile site env logical execution.principalHistory =
      (runtime.application.invoke players environment execution (.player who)).bind fun after =>
        continuation runtime graph profile site env logical after.principalHistory := by
  symm
  calc
    _ = (runtime.application.invoke players environment execution (.player who)).bind
        (fun _ => continuation runtime graph profile site env logical
          execution.principalHistory) := by
      apply FinDist.bind_congr
      intro after supported
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨command, commandMem, stepMem⟩ := supported
      exact continuation_playerStep_nonprivate runtime graph profile site env logical who
        execution after command (nonprivate command commandMem) stepMem
    _ = _ := FinDist.bind_const _ _

end Vegas.GraphRuntime
