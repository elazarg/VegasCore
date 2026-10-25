/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Interaction.ReactiveSchedulerImplementation
import Interaction.ReactiveEnvironmentMass
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Math.Probability.NestedPosterior
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import Mathlib.Tactic.Ring

/-! # Actual trace likelihood for an immutable scheduler seed -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} (app : ReactiveApplication Principal) {Seed : Type}
    (prior : PMF Seed) (family : Seed → app.Scheduler)

/-- The posterior command identity includes commands of zero marginal mass. -/
theorem schedulerMixture_command_density
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView)
    (command : app.Command) (seed : Seed) :
    (app.schedulerMixture prior family).scheduler past view command *
        (app.schedulerMixture prior family).posterior (past ++ [⟨view, command⟩]) seed =
      (app.schedulerMixture prior family).posterior past seed *
        family seed past view command := by
  let mixture := app.schedulerMixture prior family
  let joint := (mixture.posterior past).bind fun selected =>
    mixture.respond selected (past, view)
  have marginal : joint.map Prod.fst = mixture.scheduler past view := rfl
  have density := mul_fiberPosterior_map_snd_apply joint command seed
  rw [marginal] at density
  have atom : joint (command, seed) = mixture.posterior past seed *
      family seed past view command :=
    bind_map_tag_apply (mixture.posterior past)
      (fun selected => family selected past view) command seed
  change mixture.scheduler past view command *
    mixture.posterior (past ++ [⟨view, command⟩]) seed = _
  rw [SchedulerImplementation.posterior_snoc]
  exact density.trans atom

/-- The seed remains private and is conditioned only on the recorded environment word. -/
def schedulerSeedPosterior (state : app.ProtocolState) : PMF Seed :=
  match state with
  | none => prior
  | some control =>
      (app.schedulerMixture prior family).posterior control.execution.environmentRecall

variable [DecidableEq Principal] (menu : app.ResponseMenu)
    (initial : PMF app.State) (horizon : Nat)

private abbrev mixtureProtocol :=
  menu.protocol initial horizon (app.schedulerMixture prior family).scheduler

/-- The supplied fixed scheduler evaluates each actual recorded transition;
no supported fixed-seed trace is substituted for the recorded trace. -/
def fixedSchedulerTransitionMass (seed : Seed) :
    ∀ {state : (mixtureProtocol app prior family menu initial horizon).State},
      (mixtureProtocol app prior family menu initial horizon).Trace state → ℝ
  | _, .start => 1
  | after, @Trace.extend _ _ before _ past joint _ _ =>
      fixedSchedulerTransitionMass seed past *
        (app.transition initial horizon (family seed) before joint after).toReal

/-- One recorded transition disintegrates against the original immutable seed. -/
theorem schedulerMixture_step_density (seed : Seed)
    {before after : (mixtureProtocol app prior family menu initial horizon).State}
    (joint : Principal → Option app.Action)
    (legal : (mixtureProtocol app prior family menu initial horizon).Legal before joint)
    (moved : after ∈ ((mixtureProtocol app prior family menu initial horizon).step
      before ⟨joint, legal⟩).support) :
    (mixtureProtocol app prior family menu initial horizon).step before ⟨joint, legal⟩ after *
        app.schedulerSeedPosterior prior family after seed =
      app.schedulerSeedPosterior prior family before seed *
        app.transition initial horizon (family seed) before joint after := by
  cases before with
  | none =>
    change after ∈ (initial.map fun state =>
      some (⟨horizon, none, Execution.initial app state⟩ : app.Control)).support at moved
    obtain ⟨state, _supported, rfl⟩ := PMF.support_map .. ▸ moved
    change _ * prior seed = prior seed * _
    exact mul_comm _ _
  | some control =>
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some owner =>
      change after ∈ (PMF.pure (some (⟨remaining, none,
        execution.respond app owner ((joint owner).getD ⟨none⟩)⟩ : app.Control))).support at moved
      cases (PMF.mem_support_pure_iff ..).mp moved
      simp only [mixtureProtocol, ResponseMenu.protocol, transition, PMF.pure_apply, ↓reduceIte,
        schedulerSeedPosterior, respond_environmentRecall, one_mul, mul_one]
    | none =>
      cases remaining with
      | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
      | succ remaining =>
        change after ∈ (((app.schedulerMixture prior family).scheduler execution.environmentRecall
          (execution.observeEnvironment app)).bind fun command =>
            (execution.environmentStep app command).map fun next =>
              some (⟨remaining, command.actor? app, next⟩ : app.Control)).support at moved
        obtain ⟨command, _chosen, supported⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
        obtain ⟨next, advanced, rfl⟩ := PMF.support_map .. ▸ supported
        change app.transition initial horizon (app.schedulerMixture prior family).scheduler
          (some ⟨remaining + 1, none, execution⟩) joint
          (some ⟨remaining, command.actor? app, next⟩) * _ = _
        rw [app.transition_environment_apply initial horizon
            (app.schedulerMixture prior family).scheduler remaining execution next command
            advanced joint,
          app.transition_environment_apply initial horizon (family seed) remaining execution
            next command advanced joint]
        have recorded := app.environmentStep_environmentRecall execution next command advanced
        simp only [schedulerSeedPosterior, recorded]
        have density := app.schedulerMixture_command_density prior family
          execution.environmentRecall (execution.observeEnvironment app) command seed
        let mixture := app.schedulerMixture prior family
        calc
          _ = (mixture.scheduler execution.environmentRecall
              (execution.observeEnvironment app) command *
                mixture.posterior (execution.environmentRecall ++
                  [⟨execution.observeEnvironment app, command⟩]) seed) *
                    (execution.environmentStep app command) next := by ac_rfl
          _ = _ := by rw [density]; ac_rfl

/-- The original seed posterior telescopes along the same recorded trace. -/
theorem schedulerMixture_trace_density (seed : Seed)
    {state : (mixtureProtocol app prior family menu initial horizon).State}
    (trace : (mixtureProtocol app prior family menu initial horizon).Trace state) :
    trace.transitionMass * (app.schedulerSeedPosterior prior family state seed).toReal =
      (prior seed).toReal * app.fixedSchedulerTransitionMass prior family menu initial horizon
        seed trace := by
  induction trace with
  | start =>
    change 1 * (prior seed).toReal = (prior seed).toReal * 1
    ring
  | @extend before after past joint legal moved ih =>
    have density := congrArg ENNReal.toReal
      (app.schedulerMixture_step_density prior family menu initial horizon seed joint legal moved)
    simp only [ENNReal.toReal_mul] at density
    rw [Trace.transitionMass_extend, fixedSchedulerTransitionMass]
    calc
      _ = past.transitionMass * _ := by ring
      _ = past.transitionMass *
          ((app.schedulerSeedPosterior prior family before seed).toReal * _) :=
            congrArg (past.transitionMass * ·) density
      _ = _ := by rw [← mul_assoc, ih]; ring

end Interaction.ReactiveApplication
