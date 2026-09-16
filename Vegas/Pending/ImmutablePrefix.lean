/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PrefixComposition
import Vegas.Pending.Observation

/-! # Immutable graph environments along native execution

Every native action retains the ideal fields at every earlier graph cursor.
This includes rejected traffic, private preparation, and timeout resolution;
the statement requires no restriction on player or environment policies.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

namespace Prefix

/-- Remove the immutable fields appended along a typed graph prefix. -/
def restrictEnv : {start : VCtx Player L} →
    {whole : Graph Player L start Δ} → {target : VCtx Player L} →
    {suffix : Graph Player L target Δ} → {length : Nat} →
    Prefix Δ whole suffix length → VEnv L target → VEnv L start
  | _, _, _, _, _, .refl _, env => env
  | _, _, _, _, _, .sample walk, env => VEnv.tail (restrictEnv walk env)
  | _, _, _, _, _, .bind walk, env => VEnv.tail (restrictEnv walk env)
  | _, _, _, _, _, .resolve walk, env => VEnv.tail (restrictEnv walk env)

/-- A later focal observation determines the observation at every earlier
typed cursor, without revealing foreign sealed fields. -/
theorem observe_restrictEnv_eq {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (focal : Player)
    (left right : VEnv L Γ) (visible : observe focal left = observe focal right) :
    observe focal (walk.restrictEnv left) = observe focal (walk.restrictEnv right) := by
  induction walk with
  | refl => simpa [restrictEnv] using visible
  | sample walk ih | bind walk ih | resolve walk ih =>
      exact Graph.observe_tail_eq focal _ _ _ _ (ih left right visible)

theorem context_length {whole : Graph Player L Γ₀ Δ} {suffix : Graph Player L Γ Δ}
    {length : Nat} (walk : Prefix Δ whole suffix length) :
    Γ.length = Γ₀.length + length := by
  induction walk with
  | refl => omega
  | sample _ ih | bind _ ih | resolve _ ih =>
      simp only [List.length_cons] at ih ⊢
      omega

private theorem restrictEnv_mpr_length {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {n m : Nat} (same : n = m)
    (typeEq : Prefix Δ whole suffix n = Prefix Δ whole suffix m)
    (walk : Prefix Δ whole suffix m) (env : VEnv L Γ) :
    restrictEnv (Eq.mpr typeEq walk) env = restrictEnv walk env := by
  subst m
  rfl

private theorem restrictEnv_mp_length {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {n m : Nat} (same : n = m)
    (typeEq : Prefix Δ whole suffix n = Prefix Δ whole suffix m)
    (walk : Prefix Δ whole suffix n) (env : VEnv L Γ) :
    restrictEnv (Eq.mp typeEq walk) env = restrictEnv walk env := by
  subst m
  rfl

theorem restrictEnv_trans {whole : Graph Player L Γ₀ Δ} {middle : Graph Player L Γ Δ}
    {target : VCtx Player L} {suffix : Graph Player L target Δ} {n m : Nat}
    (left : Prefix Δ whole middle n) (right : Prefix Δ middle suffix m)
    (env : VEnv L target) :
    (left.trans right).restrictEnv env = left.restrictEnv (right.restrictEnv env) := by
  induction left with
  | refl =>
      simp only [trans, restrictEnv]
      rw [restrictEnv_mpr_length (by omega)]
  | sample _ ih | bind _ ih | resolve _ ih =>
      simp only [trans]
      rw [restrictEnv_mpr_length (by omega), restrictEnv_mp_length (by omega)]
      exact congrArg VEnv.tail (ih right)

end Prefix

/-- The current ideal environment retains a specified earlier environment
along a typed graph prefix. Clock, pool, and candidate details are irrelevant. -/
def State.Extends (whole : Graph Player L Γ Δ) (input : VEnv L Γ) :
    State Player L Δ → Prop
  | .running suffix ideal _ _ _ _ _ _ =>
      ∃ length, ∃ walk : Prefix Δ whole suffix length, walk.restrictEnv ideal = input

theorem State.running_extends (whole : Graph Player L Γ Δ) (input : VEnv L Γ)
    (values : PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat) :
    (State.running whole input values bindings candidates pc clock enteredAt).Extends
      whole input := ⟨0, .refl whole, rfl⟩

theorem State.initial_extends (whole : Graph Player L Γ Δ) (input : VEnv L Γ) :
    (State.initial whole input).Extends whole input := by
  exact State.running_extends whole input _ _ _ _ _ _

/-- Recover the original environment using any witness of the actual cursor. -/
theorem State.Extends.restrictEnv_eq {whole : Graph Player L Γ₀ Δ}
    {input : VEnv L Γ₀} {suffix : Graph Player L Γ Δ} {ideal : VEnv L Γ}
    {values : PublicValues Γ} {bindings : Bindings Player}
    {candidates : CommitmentCandidates Player Slot (Raw L)} {pc clock enteredAt length : Nat}
    (retention : (State.running suffix ideal values bindings candidates pc clock enteredAt).Extends
      whole input) (walk : Prefix Δ whole suffix length) :
    walk.restrictEnv ideal = input := by
  obtain ⟨otherLength, other, retained⟩ := retention
  have same : otherLength = length := by
    have left := other.context_length
    have right := walk.context_length
    omega
  subst otherLength
  rwa [Subsingleton.elim other walk] at retained

private theorem extends_after_cons {whole : Graph Player L Γ₀ Δ}
    {input : VEnv L Γ₀} {cursor : Graph Player L Γ Δ} {ideal : VEnv L Γ}
    {name : VarId} {binding : BindTy Player L}
    {next : Graph Player L ((name, binding) :: Γ) Δ}
    (step : Prefix Δ cursor next 1)
    (tailEq : ∀ env, step.restrictEnv env = VEnv.tail env)
    (retained : ∃ length, ∃ walk : Prefix Δ whole cursor length,
      walk.restrictEnv ideal = input) (value : L.Val binding.base)
    (values : PublicValues ((name, binding) :: Γ)) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat) :
    State.Extends whole input
      (.running next (VEnv.cons value ideal) values bindings candidates pc clock enteredAt) := by
  obtain ⟨length, walk, retained⟩ := retained
  refine ⟨length + 1, walk.trans step, ?_⟩
  simpa only [Prefix.restrictEnv_trans, tailEq, VEnv.tail_cons] using retained

theorem privateStep_extends (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (input : VEnv L Γ₀)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L)
    (retained : state.Extends whole input) :
    (runtime.privateStep state who command).Extends whole input := by
  cases state
  cases command <;> exact retained

theorem handle_extends (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (input : VEnv L Γ₀)
    (state nextState : State Player L Δ) (message : Message Player (Payload Player L))
    (retained : state.Extends whole input)
    (accepted : runtime.handle state message = some nextState) :
    nextState.Extends whole input := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => cases payload <;> simp [handle] at accepted
          | sample => cases payload <;> simp [handle] at accepted
          | bind name owner fresh next =>
              cases payload with
              | commitment site candidate =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  exact extends_after_cons (.bind (.refl next)) (fun _ => rfl)
                    retained _ _ _ _ _ _ _
              | opening | withhold | malformed => simp [handle] at accepted
          | resolve output owner binding fresh source checks next =>
              cases payload with
              | commitment | malformed => simp [handle] at accepted
              | opening site candidate raw =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? _ with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded =>
                      rw [typed] at accepted
                      cases accepted
                      exact extends_after_cons (.resolve (.refl next)) (fun _ => rfl)
                        retained _ _ _ _ _ _ _
              | withhold site =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  exact extends_after_cons (.resolve (.refl next)) (fun _ => rfl)
                    retained _ _ _ _ _ _ _

theorem environmentStep_extends (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (input : VEnv L Γ₀)
    (state nextState : State Player L Δ) (command : EnvironmentCommand)
    (retained : state.Extends whole input)
    (supported : nextState ∈ (runtime.environmentStep state command).support) :
    nextState.Extends whole input := by
  cases command
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret =>
          simp only [environmentStep, tick, FinDist.mem_support_pure] at supported
          subst nextState
          exact retained
      | sample name fresh law next =>
          simp only [environmentStep, tick, FinDist.support_map] at supported
          obtain ⟨value, _, rfl⟩ := supported
          exact extends_after_cons (.sample (.refl next)) (fun _ => rfl)
            retained _ _ _ _ _ _ _
      | bind name owner fresh next =>
          simp only [environmentStep, tick] at supported
          split at supported <;> rw [FinDist.mem_support_pure] at supported <;> subst nextState
          · exact extends_after_cons (.bind (.refl next)) (fun _ => rfl)
              retained _ _ _ _ _ _ _
          · exact retained
      | resolve output owner binding fresh source checks next =>
          simp only [environmentStep, tick] at supported
          split at supported <;> rw [FinDist.mem_support_pure] at supported <;> subst nextState
          · exact extends_after_cons (.resolve (.refl next)) (fun _ => rfl)
              retained _ _ _ _ _ _ _
          · exact retained

/-- All initialized policy executions retain their input, and more generally
retain the environment at any earlier reached cursor. -/
theorem runPolicies_extends (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ₀ Δ) (input : VEnv L Γ₀)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (retained : execution.native.application.Extends whole input)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    next.native.application.Extends whole input := by
  exact runtime.application.runPolicies_application_invariant (State.Extends whole input)
    (runtime.privateStep_extends whole input)
    (fun state message next => runtime.handle_extends whole input state next message)
    (fun state command next => runtime.environmentStep_extends whole input state next command)
    players environment schedule execution next retained supported

end Vegas.GraphRuntime
