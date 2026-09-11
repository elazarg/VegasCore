/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.ConditionalResolutionService
import VegasTests.ConditionalSourcePolicies
import GameTheory.Core.Approximate

/-! # Owner deviation simulation under a generated resolving service

This comparison starts at the checked source and uses its emitted windowed
application, actual public message policies, and finite resolving service.
Completion is derived, not assumed or conditioned upon. The source fragment
has a single decision-making player and no chance, so every public terminal
environment has a deterministic source-owner realization. This argument does
not establish deviation simulation for arbitrary generated programs.
-/

noncomputable section

namespace VegasTests.ConditionalResolutionDeviation

open Vegas Interaction GameTheory GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourcePolicies
  (PublicEnv publicEnv publicEnv_get sourceStrategy sourceStrategy_law)

def observation (execution : runtime.application.PolicyExecution) : Bool × Option PublicEnv :=
  (execution.native.application.base.memory.finished compiled.graph.nodeCount,
    compiled.readPublicTerminal? execution.native.application.base.memory)

def deviatedPlayers (profile : SourceBehavioralProfile core)
    (replacement : runtime.application.PlayerPolicy) : Fin 2 → runtime.application.PlayerPolicy :=
  Profile.update (sig := MessageApplication.policySignature (Fin 2) runtime.application)
    (resolvingPlayers profile) 0 replacement

def serviceGame : GameForm (Fin 2) :=
  runtime.application.policyGame resolvingEnvironment resolvingSchedule
    initialPolicyExecution.native

/-- Every raw owner replacement, against the same unchanged relay and service,
has exactly a finite mixture of source-owner deviation laws. The observation
retains completion as well as the source public terminal environment. -/
theorem owner_deviation_law (profile : SourceBehavioralProfile core)
    (replacement : runtime.application.PlayerPolicy) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy core (0 : Fin 2)),
      ((runtime.application.runPolicies (deviatedPlayers profile replacement)
        resolvingEnvironment resolvingSchedule initialPolicyExecution).map observation) =
        alternatives.bind fun alternative =>
          (denoteSource core
            (Profile.update (sig := sourceGameSignature core) profile 0 alternative)
            source.env).map (fun terminal => (true, some terminal.erasePubEnv)) := by
  let law := runtime.application.runPolicies (deviatedPlayers profile replacement)
    resolvingEnvironment resolvingSchedule initialPolicyExecution
  have hrelay : deviatedPlayers profile replacement 1 = runtime.expiryRelay := by
    simp only [deviatedPlayers, Profile.update_of_ne _ _ (show (1 : Fin 2) ≠ 0 by decide),
      resolvingPlayers, Profile.update_same]
  refine ⟨law.map (fun execution => sourceStrategy
    (((observation execution).2.getD (publicEnv none)).get .here)), ?_⟩
  change law.map observation = _
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro execution hexecution
  have hfinished := resolving_service_complete (deviatedPlayers profile replacement)
    hrelay execution hexecution
  obtain ⟨terminal, _, hpublic⟩ := applicationPlan.windowed_runPolicies_source_public_outcome
    checked (fun _ => 0) bindingSelector (fun _ => none) (fun _ => 10)
    (deviatedPlayers profile replacement) resolvingEnvironment resolvingSchedule
    execution hexecution hfinished
  change compiled.readPublicTerminal? execution.native.application.base.memory =
    some terminal.erasePubEnv at hpublic
  rw [sourceStrategy_law]
  change FinDist.pure (observation execution) = _
  simp only [observation, hfinished, hpublic, Option.getD_some]
  exact congrArg (fun env : PublicEnv => FinDist.pure (true, some env))
    (publicEnv_get terminal.erasePubEnv).symm

/-- A source lower bound for any public-outcome valuation survives arbitrary
owner deviations. No condition on the deviator's utility is needed. -/
theorem owner_guarantee (profile : SourceBehavioralProfile core)
    (replacement : runtime.application.PlayerPolicy)
    (value : Bool × Option PublicEnv → ℝ) (bound : ℝ)
    (hbound : ∀ alternative : SourceBehavioralPolicy core (0 : Fin 2),
      bound ≤ ((denoteSource core
        (Profile.update (sig := sourceGameSignature core) profile 0 alternative) source.env).map
          (fun terminal => (true, some terminal.erasePubEnv))).expect value) :
    bound ≤ ((runtime.application.runPolicies (deviatedPlayers profile replacement)
      resolvingEnvironment resolvingSchedule initialPolicyExecution).map
        observation).expect value := by
  obtain ⟨alternatives, hlaw⟩ := owner_deviation_law profile replacement
  rw [hlaw, FinDist.expect_bind]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => hbound alternative

/-- The owner's source epsilon-best response is preserved against every raw
runtime deviation, with the same error and the same resolving service. This
statement concerns the owner's incentives; it is not a two-player Nash theorem. -/
theorem owner_bestResponse (profile : SourceBehavioralProfile core)
    (utility : Bool × Option PublicEnv → Fin 2 → ℝ) (epsilon : ℝ)
    (hsource : IsεBestResponse (sourceGameForm core source.env)
      (fun terminal => utility (true, some terminal.erasePubEnv)) epsilon 0 profile (profile 0)) :
    IsεBestResponse serviceGame (fun execution => utility (observation execution))
      epsilon 0 (resolvingPlayers profile) (resolvingPlayers profile 0) := by
  intro replacement
  obtain ⟨alternatives, hdeviation⟩ := owner_deviation_law profile replacement
  have hreference := resolving_source_law profile
  let value := fun outcome => utility outcome 0
  have hbound : ∀ alternative : SourceBehavioralPolicy core (0 : Fin 2),
      ((denoteSource core
        (Profile.update (sig := sourceGameSignature core) profile 0 alternative) source.env).map
          (fun terminal => (true, some terminal.erasePubEnv))).expect value ≤
        ((denoteSource core profile source.env).map
          (fun terminal => (true, some terminal.erasePubEnv))).expect value + epsilon := by
    intro alternative
    have h := hsource alternative
    simp only [euPreferenceWithin, expectedUtility, Profile.update_eq_self,
      sourceGameForm_play] at h
    simp only [FinDist.expect_map, value]
    convert h using 1 <;> rfl
  have haverage := FinDist.expect_mono (μ := alternatives)
    (fun alternative _ => hbound alternative)
  rw [FinDist.expect_const] at haverage
  have hdeviationUtility := congrArg (fun law => law.expect value) hdeviation
  have hreferenceUtility := congrArg (fun law => law.expect value) hreference
  rw [FinDist.expect_bind] at hdeviationUtility
  have htarget := hdeviationUtility.le.trans
    (haverage.trans_eq (congrArg (fun amount => amount + epsilon) hreferenceUtility.symm))
  simp only [euPreferenceWithin, expectedUtility, Profile.update_eq_self]
  simp only [FinDist.expect_map, value, serviceGame, MessageApplication.policyGame,
    deviatedPlayers, observation, initialPolicyExecution,
    MessageApplication.PolicyExecution.initial] at htarget ⊢
  convert htarget using 1 <;> rfl

end VegasTests.ConditionalResolutionDeviation

/-- info: 'VegasTests.ConditionalResolutionDeviation.owner_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalResolutionDeviation.owner_deviation_law

/-- info: 'VegasTests.ConditionalResolutionDeviation.owner_guarantee' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalResolutionDeviation.owner_guarantee

/-- info: 'VegasTests.ConditionalResolutionDeviation.owner_bestResponse' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalResolutionDeviation.owner_bestResponse
