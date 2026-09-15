/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceCompletion

/-! # Determinism at player-controlled graph phases -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- The current graph cursor is controlled by a player rather than a sample. -/
def State.PlayerControlled : State Player L Δ → Prop
  | .running graph _ _ _ _ _ _ _ =>
      match graph with
      | .bind _ _ _ _ => True
      | .resolve _ _ _ _ _ _ _ => True
      | _ => False

/-- At a bind or resolve cursor, every native action has a point-mass result.
In particular an environment tick cannot consume graph sampling randomness. -/
theorem application_step_eq_pure_of_bind_or_resolve
    (runtime : GraphRuntime Player L Δ) (state : runtime.application.State)
    (action : runtime.application.Action)
    (controlled : state.application.PlayerControlled) :
    ∃ next, runtime.application.step state action = FinDist.pure next := by
  rcases state with ⟨application, pool, receipts⟩
  cases application with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs => simp [State.PlayerControlled] at controlled
      | sample name fresh law next => simp [State.PlayerControlled] at controlled
      | bind name owner fresh next =>
        cases action with
        | environment command =>
            cases command
            by_cases expired : runtime.deadline pc ≤ clock + 1 - enteredAt <;>
              simp [Interaction.MessageApplication.step, GraphRuntime.application,
                GraphRuntime.environmentStep, GraphRuntime.tick, expired]
        | _ =>
            simp [Interaction.MessageApplication.step]
      | resolve outputName owner bindingName fresh source checks next =>
        cases action with
        | environment command =>
            cases command
            by_cases expired : runtime.deadline pc ≤ clock + 1 - enteredAt <;>
              simp [Interaction.MessageApplication.step, GraphRuntime.application,
                GraphRuntime.environmentStep, GraphRuntime.tick, expired]
        | _ =>
            simp [Interaction.MessageApplication.step]

/-- A compiled player who does not own the current bind emits `wait`, even
when the compiler is anchored at the original graph and has traversed a typed
prefix to the current suffix. -/
theorem compilePlayerPolicy_bind_nonowner_wait
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (suffix : Graph Player L Γ Δ) (length : Nat) (walk : Prefix Δ whole suffix length)
    (name : VarId) (owner who : Player) (payload : L.Ty)
    (fresh : name ∉ Γ.map Prod.fst)
    (next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ)
    (hsuffix : suffix = .bind name owner fresh next) (hne : owner ≠ who)
    (policy : BehavioralPolicy who whole) (history : List (Entry runtime))
    (view : runtime.application.View) (hpc : view.application.publicState.pc = length) :
    compilePlayerPolicy runtime whole who policy history view = FinDist.pure .wait := by
  rw [Prefix.compilePlayerPolicy_eq_suffix walk who policy history view hpc]
  subst hsuffix
  simp [compileAt, hpc, hne]

/-- The corresponding non-owner fact for a resolve cursor. -/
theorem compilePlayerPolicy_resolve_nonowner_wait
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (suffix : Graph Player L Γ Δ) (length : Nat) (walk : Prefix Δ whole suffix length)
    (outputName bindingName : VarId) (owner who : Player) (payload : L.Ty)
    (fresh : outputName ∉ Γ.map Prod.fst)
    (source : HasVar Γ bindingName (.sealed owner (R.result payload)))
    (checks : List (GuardCheck
      ((outputName, .pub (R.result payload)) :: Γ)))
    (next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ)
    (hsuffix : suffix = .resolve outputName owner bindingName fresh source checks next)
    (hne : owner ≠ who) (policy : BehavioralPolicy who whole)
    (history : List (Entry runtime)) (view : runtime.application.View)
    (hpc : view.application.publicState.pc = length) :
    compilePlayerPolicy runtime whole who policy history view = FinDist.pure .wait := by
  rw [Prefix.compilePlayerPolicy_eq_suffix walk who policy history view hpc]
  subst hsuffix
  simp [compileAt, hpc, hne]

/-- Once the selected policy kernel is pure, one invocation at a controlled
cursor is itself a point mass. No other player's policy and no chance kernel
is consulted by this invocation. -/
theorem invoke_eq_pure_of_bind_or_resolve
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (execution : runtime.application.PolicyExecution)
    (invocation : @Interaction.MessageApplication.Invocation Player)
    (controlled : execution.native.application.PlayerControlled)
    (purePolicy :
      match invocation with
      | .player who => ∃ command,
          players who (execution.principalHistory who)
              (Interaction.MessageApplication.State.observe runtime.application
                execution.native who) = FinDist.pure command
      | .environment => ∃ command,
          environment execution.environmentHistory
              (Interaction.MessageApplication.State.environmentView runtime.application
                execution.native) = FinDist.pure command) :
    ∃ next, runtime.application.invoke players environment execution invocation =
      FinDist.pure next := by
  cases invocation with
  | player who =>
      rcases purePolicy with ⟨command, hcommand⟩
      simp only [Interaction.MessageApplication.invoke, hcommand, FinDist.pure_bind]
      cases haction : Interaction.MessageApplication.PlayerCommand.toAction
          runtime.application who command with
      | none =>
          simp [Interaction.MessageApplication.playerStep,
            Interaction.MessageApplication.advance, haction]
      | some action =>
          rcases runtime.application_step_eq_pure_of_bind_or_resolve execution.native
            action controlled with ⟨state, hstate⟩
          simp [Interaction.MessageApplication.playerStep,
            Interaction.MessageApplication.advance, haction, hstate]
  | environment =>
      rcases purePolicy with ⟨command, hcommand⟩
      simp only [Interaction.MessageApplication.invoke, hcommand, FinDist.pure_bind]
      cases haction : Interaction.MessageApplication.EnvironmentPolicyCommand.toAction
          runtime.application command with
      | none =>
          simp [Interaction.MessageApplication.environmentPolicyStep,
            Interaction.MessageApplication.advance, haction]
      | some action =>
          rcases runtime.application_step_eq_pure_of_bind_or_resolve execution.native
            action controlled with ⟨state, hstate⟩
          simp [Interaction.MessageApplication.environmentPolicyStep,
            Interaction.MessageApplication.advance, haction, hstate]

end Vegas.GraphRuntime
