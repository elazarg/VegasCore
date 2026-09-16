/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageDeviationContinuation

/-! # Normalization and history erasure for deviation continuations -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Changing only the focal logical-action history does not change a
continuation whose focal policy ignores that history and whose focal runtime
cache is empty. -/
theorem continuation_congr_focal_logical
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (profile : BehavioralProfile graph) (focal : Player)
    (independent : PolicyIgnoresOwnHistory focal graph (profile focal))
    (site : Nat) (env : VEnv L Γ) (left right : History Player L)
    (agree : ∀ who, who ≠ focal → left who = right who)
    (histories : Player → List (Entry runtime)) (empty : histories focal = []) :
    continuation runtime graph profile site env left histories =
      continuation runtime graph profile site env right histories := by
  induction graph generalizing site left right with
  | ret output => rfl
  | sample name fresh law next ih =>
      simp only [continuation]
      apply FinDist.bind_congr
      intro value _
      exact ih runtime (afterSample profile) independent (site + 1)
        (VEnv.cons value env) left right agree histories empty
  | bind name owner fresh next ih =>
      by_cases owned : owner = focal
      · subst owner
        simp only [continuation, empty, preparedChoice_nil]
        have kernel := independent.1 rfl (observe focal env) (left focal) (right focal)
        change bindKernel profile (observe focal env, left focal) =
          bindKernel profile (observe focal env, right focal) at kernel
        rw [kernel]
        apply FinDist.bind_congr
        intro choice _
        exact ih runtime (afterBind profile) independent.2 (site + 1)
          (VEnv.cons ((R.valueEquiv _).symm choice) env) _ _
          (fun who different => by
            simp [Function.update, different, agree who different]) histories empty
      · simp only [continuation]
        rw [agree owner owned]
        split
        · exact ih runtime (afterBind profile) independent.2 (site + 1) _ _ _
            (fun who different => by
              by_cases same : who = owner
              · subst who; simp [Function.update]
              · simp [Function.update, same, agree who different]) histories empty
        · apply FinDist.bind_congr
          intro choice _
          exact ih runtime (afterBind profile) independent.2 (site + 1) _ _ _
            (fun who different => by
              by_cases same : who = owner
              · subst who; simp [Function.update]
              · simp [Function.update, same, agree who different]) histories empty
  | resolve output owner binding fresh source checks next ih =>
      by_cases owned : owner = focal
      · subst owner
        simp only [continuation, empty, rememberedDisclosure_nil]
        have kernel := independent.1 rfl (observe focal env) (left focal) (right focal)
        change resolveKernel profile (observe focal env, left focal) =
          resolveKernel profile (observe focal env, right focal) at kernel
        rw [kernel]
        apply FinDist.bind_congr
        intro disclose _
        exact ih runtime (afterResolve profile) independent.2 (site + 1)
          (VEnv.cons ((R.valueEquiv _).symm
            (acceptedResult source checks env disclose)) env) _ _
          (fun who different => by
            simp [Function.update, different, agree who different]) histories empty
      · simp only [continuation]
        rw [agree owner owned]
        split
        · exact ih runtime (afterResolve profile) independent.2 (site + 1) _ _ _
            (fun who different => by
              by_cases same : who = owner
              · subst who; simp [Function.update]
              · simp [Function.update, same, agree who different]) histories empty
        · apply FinDist.bind_congr
          intro disclose _
          exact ih runtime (afterResolve profile) independent.2 (site + 1) _ _ _
            (fun who different => by
              by_cases same : who = owner
              · subst who; simp [Function.update]
              · simp [Function.update, same, agree who different]) histories empty

/-- Initially, sanitizing the focal transcript changes nothing: the residual
law is the ordinary graph execution law. -/
theorem deviationContinuationAt_initial (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (input : VEnv L Γ) :
    deviationContinuationAt runtime whole profile focal
        (fun _ => ([] : List (Entry runtime)))
        (State.initial whole input) (State.initial_follows whole input) =
      Graph.run whole profile input := by
  have atInitial := runtime.deviationContinuationAt_running whole profile focal
    (MessageApplication.PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application (State.initial whole input)))
    (State.initial_follows whole input) whole 0 (.refl whole)
    input _ _ _ 0 0 rfl
  have atInitial' : deviationContinuationAt runtime whole profile focal
      (fun _ => ([] : List (Entry runtime)))
      (State.initial whole input) (State.initial_follows whole input) =
    continuation runtime whole profile 0 input
      (eraseFocalLogical focal (fun who => projectLogicalHistory (runtime := runtime) who
        (observe who input) [] whole 0 0)) (fun _ => []) := by
    have profileRefl : (Prefix.refl whole).profileTail profile = profile := by
      funext who
      rfl
    have historiesEmpty : eraseFocalHistory focal
        (fun _ => ([] : List (Entry runtime))) = fun _ => [] := by
      funext who
      simp [eraseFocalHistory]
    simp only [MessageApplication.PolicyExecution.initial,
      MessageApplication.State.initial] at atInitial
    rw [profileRefl, historiesEmpty] at atInitial
    exact atInitial
  have empty : eraseFocalLogical focal (fun who => projectLogicalHistory (runtime := runtime) who
      (observe who input) [] whole 0 0) = fun _ => [] := by
    funext who
    by_cases same : who = focal
    · simp [eraseFocalLogical, same]
    · simp only [eraseFocalLogical, same, ↓reduceIte]
      cases whole <;> rfl
  rw [empty] at atInitial'
  exact atInitial'.trans (runtime.continuation_initial_eq_run whole profile input)

/-- At termination, the sanitized residual law is the actual ideal outcome. -/
theorem deviationContinuationAt_terminal (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (profile : BehavioralProfile whole)
    (focal : Player) (histories : Player → List (Entry runtime))
    (state : State Player L Δ) (follows : state.Follows whole 0)
    (output : VEnv L Δ) (completed : state.outcome? = some output) :
    deviationContinuationAt runtime whole profile focal histories state follows =
      FinDist.pure output := by
  cases state with
  | running suffix ideal values bindings candidates site clock enteredAt =>
      cases suffix <;> simp only [State.outcome?] at completed <;> cases completed
      rfl

/-- info: 'Vegas.GraphRuntime.continuation_congr_focal_logical' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.continuation_congr_focal_logical

/-- info: 'Vegas.GraphRuntime.deviationContinuationAt_initial' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.GraphRuntime.deviationContinuationAt_initial

end Vegas.GraphRuntime
