/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ContinuationService
import Vegas.Pending.ServiceCompletion

/-! # Composing service expiry safety -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Δ : VCtx Player L}

/-- Every expiry instruction is safe at every state which can reach it: either
its nominal phase is stale or the actual typed cursor is a chance node. -/
def ExpirySafe (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (plan : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution) : Prop :=
  ∀ before phase after, plan = before ++ .expire phase :: after →
    ∀ next ∈ (runtime.application.runPolicies players environment
      (before.map ServiceInstruction.invocation) execution).support,
      next.native.application.phase ≠ phase ∨ next.native.application.IsSample

/-- Locate a distinguished cons either in the left or right side of an append. -/
theorem append_cons_split {A : Type} (left right before after : List A) (item : A)
    (equal : left ++ right = before ++ item :: after) :
    (∃ leftBefore leftAfter, left = leftBefore ++ item :: leftAfter ∧
      before = leftBefore ∧ after = leftAfter ++ right) ∨
    (∃ rightBefore rightAfter, right = rightBefore ++ item :: rightAfter ∧
      before = left ++ rightBefore ∧ after = rightAfter) := by
  induction left generalizing before with
  | nil =>
      right
      exact ⟨before, after, by simpa using equal, rfl, rfl⟩
  | cons head tail ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons_append] at equal
          injection equal with headEq restEq
          left
          exact ⟨[], tail, by simp [headEq], rfl, by simpa using restEq.symm⟩
      | cons beforeHead beforeTail =>
          simp only [List.cons_append] at equal
          injection equal with headEq restEq
          subst beforeHead
          rcases ih beforeTail restEq with hlocal | residual
          · rcases hlocal with ⟨leftBefore, leftAfter, leftEq, beforeEq, afterEq⟩
            left
            exact ⟨head :: leftBefore, leftAfter, by simp [leftEq], by simp [beforeEq], afterEq⟩
          · rcases residual with ⟨rightBefore, rightAfter, rightEq, beforeEq, afterEq⟩
            right
            exact ⟨rightBefore, rightAfter, rightEq, by simp [beforeEq], afterEq⟩

/-- A prefix containing no expiry instructions may be prepended when every
state reachable through it satisfies expiry safety for the suffix. -/
theorem expirySafe_append_of_prefix
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (left right : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution)
    (noExpiry : ∀ phase, .expire phase ∉ left)
    (suffixSafe : ∀ middle ∈ (runtime.application.runPolicies players environment
      (left.map ServiceInstruction.invocation) execution).support,
      ExpirySafe runtime players environment right middle) :
    ExpirySafe runtime players environment (left ++ right) execution := by
  intro before phase after split next supported
  rcases append_cons_split left right before after (.expire phase) split with localCase | residual
  · rcases localCase with ⟨leftBefore, leftAfter, leftEq, -, -⟩
    exact ((noExpiry phase) (leftEq ▸ by simp)).elim
  · rcases residual with ⟨rightBefore, rightAfter, rightEq, beforeEq, afterEq⟩
    subst before
    rw [List.map_append, runtime.application.runPolicies_append] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, leftRun, rightRun⟩ := supported
    exact suffixSafe middle leftRun rightBefore phase rightAfter rightEq next rightRun

/-- Once the public phase has passed `phase`, every reserved expiry for that
phase is safe, independently of how many of the slots have already run. -/
theorem expirySafe_replicate_expire_of_lt
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution) (phase count : Nat)
    (passed : phase < execution.native.application.phase) :
    ExpirySafe runtime players environment
      (List.replicate count (.expire phase)) execution := by
  intro before nominal after split next supported
  have member : (ServiceInstruction.expire nominal : ServiceInstruction Player) ∈
      List.replicate count (ServiceInstruction.expire phase : ServiceInstruction Player) := by
    rw [split]
    simp
  have nominalEq : nominal = phase := by
    simpa using (List.eq_of_mem_replicate member)
  subst nominal
  left
  have monotone := runtime.runPolicies_phase_mono players environment
    (before.map ServiceInstruction.invocation) execution next supported
  omega

/-- Sequential composition of expiry-safe instruction lists. -/
theorem expirySafe_append
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (left right : List (ServiceInstruction Player))
    (execution : runtime.application.PolicyExecution)
    (leftSafe : ExpirySafe runtime players environment left execution)
    (rightSafe : ∀ middle ∈ (runtime.application.runPolicies players environment
      (left.map ServiceInstruction.invocation) execution).support,
      ExpirySafe runtime players environment right middle) :
    ExpirySafe runtime players environment (left ++ right) execution := by
  intro before phase after split next supported
  rcases append_cons_split left right before after (.expire phase) split with localCase | residual
  · rcases localCase with ⟨leftBefore, leftAfter, leftEq, beforeEq, afterEq⟩
    subst before
    exact leftSafe leftBefore phase leftAfter leftEq next supported
  · rcases residual with ⟨rightBefore, rightAfter, rightEq, beforeEq, afterEq⟩
    subst before
    rw [List.map_append, runtime.application.runPolicies_append] at supported
    simp only [FinDist.support_bind, Set.mem_iUnion] at supported
    obtain ⟨middle, leftRun, rightRun⟩ := supported
    exact rightSafe middle leftRun rightBefore phase rightAfter rightEq next rightRun

end Vegas.GraphRuntime
