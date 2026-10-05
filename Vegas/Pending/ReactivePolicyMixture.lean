/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePolicyMixture
import Vegas.Pending.ReactiveServiceEvaluation

/-! # Policy mixtures through the actual reserved service

Behavioral realization commutes with every finite existing interaction plan,
including intervening observations, silence and adaptive network commands.
The law retains the complete runtime execution. No observation-obliviousness
or immediate-inclusion condition is imposed.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem runInteractionPlan_policyMixture (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Index : Type} (initial : PMF Index)
    (policies : Index → (runtime.reactiveApplication leaks).Policy)
    (who : Player) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution) :
    let mixture := (runtime.reactiveApplication leaks).policyMixture initial policies
    (mixture.posterior (execution.recall who)).bind (fun index =>
      runtime.runInteractionPlan leaks (Function.update players who (policies index))
        network plan execution) =
      runtime.runInteractionPlan leaks (Function.update players who mixture.policy)
        network plan execution := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let mixture := app.policyMixture initial policies
  change (mixture.posterior (execution.recall who)).bind _ = _
  induction plan generalizing execution with
  | nil => simp only [runInteractionPlan, PMF.bind_const]
  | cons instruction rest ih =>
      have resumed (current : app.Execution) (actor : Option Player) :
          (mixture.posterior (current.recall who)).bind (fun index =>
            (app.resume (Function.update players who (policies index)) actor current).bind
              (runtime.runInteractionPlan leaks
                (Function.update players who (policies index)) network rest)) =
            (app.resume (Function.update players who mixture.policy) actor current).bind
              (runtime.runInteractionPlan leaks
                (Function.update players who mixture.policy) network rest) := by
        cases actor with
        | none => simpa only [ReactiveApplication.resume, PMF.pure_bind] using ih current
        | some owner =>
            by_cases same : owner = who
            · subst owner
              have split := mixture.response_disintegrate current who (fun next index =>
                runtime.runInteractionPlan leaks
                  (Function.update players who (policies index)) network rest next)
              simp only [mixture, app, ReactiveApplication.policyMixture,
                PMF.bind_map] at split
              simp only [ReactiveApplication.resume, ReactiveApplication.invoke,
                Function.update_self, PMF.bind_map]
              refine split.trans ?_
              apply bind_congr_on_support _
              intro action _
              exact ih _
            · simp only [ReactiveApplication.resume, ReactiveApplication.invoke,
                Function.update_of_ne same, PMF.bind_map]
              rw [PMF.bind_comm]
              apply bind_congr_on_support _
              intro action _
              rw [← app.respond_recall_other current owner who (Ne.symm same) action]
              exact ih _
      simp only [runInteractionPlan, interactionStep, ReactiveApplication.dispatch,
        PMF.bind_bind]
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro command _
      rw [PMF.bind_comm]
      apply bind_congr_on_support _
      intro current reached
      rw [← app.environmentStep_recall execution current command reached]
      exact resumed current (command.actor? app)

/-- At an already activated information site, disintegrate the current response
and all later service steps using the posterior from actual own recall. The
current passive observation is retained; it is not sampled again. -/
theorem invoke_runInteractionPlan_policyMixture (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    {Index : Type} (initial : PMF Index)
    (policies : Index → (runtime.reactiveApplication leaks).Policy)
    (who : Player) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution) :
    let app := runtime.reactiveApplication leaks
    let mixture := app.policyMixture initial policies
    (mixture.posterior (execution.recall who)).bind (fun index =>
      (app.invoke (Function.update players who (policies index)) who execution).bind
        (runtime.runInteractionPlan leaks (Function.update players who (policies index))
          network plan)) =
      (app.invoke (Function.update players who mixture.policy) who execution).bind
        (runtime.runInteractionPlan leaks (Function.update players who mixture.policy)
          network plan) := by
  intro app mixture
  have split := mixture.response_disintegrate execution who (fun next index =>
    runtime.runInteractionPlan leaks (Function.update players who (policies index))
      network plan next)
  simp only [mixture, app, ReactiveApplication.policyMixture, PMF.bind_map] at split
  simp only [ReactiveApplication.invoke, Function.update_self, PMF.bind_map]
  refine split.trans ?_
  apply bind_congr_on_support _
  intro response _
  exact runtime.runInteractionPlan_policyMixture leaks initial policies who players network plan _

/-- A planned response slot, or never selecting that response, is realized
behaviorally in the existing runtime. The exact law includes all passive
samples and intervening responses. The family is dormant before `offset`, so
the formula applies at later phases with their actual earlier own recall. -/
theorem runInteractionPlan_scheduledMixture (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (probability : ℝ) (nonnegative : 0 ≤ probability) (bounded : probability ≤ 1)
    {slots : Nat} (timing : PMF (Fin slots)) (offset : Nat)
    (opening waiting : (runtime.reactiveApplication leaks).Policy)
    (who : Player) (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (before : (execution.recall who).length ≤ offset) :
    let app := runtime.reactiveApplication leaks
    let prior := mix probability nonnegative bounded
      (timing.map some) (PMF.pure none)
    let family := fun selected => app.scheduledPolicy offset selected opening waiting
    let mixture := app.policyMixture prior family
    runtime.runInteractionPlan leaks (Function.update players who mixture.policy)
      network plan execution =
        mix probability nonnegative bounded
          (timing.bind fun slot => runtime.runInteractionPlan leaks
            (Function.update players who (family (some slot))) network plan execution)
          (runtime.runInteractionPlan leaks (Function.update players who waiting)
            network plan execution) := by
  dsimp only
  let app := runtime.reactiveApplication leaks
  let prior := mix probability nonnegative bounded
    (timing.map some) (PMF.pure none)
  let family := fun selected : Option (Fin slots) =>
    app.scheduledPolicy offset selected opening waiting
  have posterior := app.policyMixture_posterior_dormant prior family waiting offset
    (fun selected past view earlier =>
      app.scheduledPolicy_before offset selected opening waiting past view earlier)
    (execution.recall who) before
  have actual := runtime.runInteractionPlan_policyMixture leaks prior family who players
    network plan execution
  dsimp only at actual
  rw [posterior] at actual
  have never : family none = waiting := by
    funext past view
    simp [family, ReactiveApplication.scheduledPolicy]
  dsimp only [prior] at actual
  rw [mix_bind, PMF.bind_map, PMF.pure_bind, never] at actual
  exact actual.symm

end Vegas.EventGraphRuntime
