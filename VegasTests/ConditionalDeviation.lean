/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.ConditionalApplicationImage
import Vegas.Compile.ApplicationPlanOutcome
import Vegas.Core.Strategy
import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationWithholding

/-! # Owner deviations in a generated, chance-free disclosure program

The source owner controls both binding and final disclosure. Every completed
public outcome is realized by a legal source policy of that same owner. The
comparison retains completion and uses the actual generated message runner.
Completion is an explicit operational premise; no settlement or other-player
deviation theorem is asserted. There is no randomized hidden source prefix or
subsequent response in this fragment.
-/

noncomputable section

namespace VegasTests.ConditionalDeviation

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage

abbrev PublicEnv := Env simpleExpr.Val [(2, .option .bool)]

def publicEnv (value : Option Bool) : PublicEnv :=
  Env.cons value (Env.empty simpleExpr.Val)

theorem publicEnv_get (env : PublicEnv) : publicEnv (env.get .here) = env := by
  funext name ty member
  cases member with
  | here => rfl
  | there member => cases member

/-- A pure source policy chooses its binding and later reads that own binding
when publishing. It is legal at every source-visible environment. -/
def sourceStrategy (outcome : Option Bool) : SourceBehavioralPolicy core (0 : Fin 2) := by
  intro context name ty guard site visible
  cases site with
  | here => exact FinDist.pure ⟨outcome.getD false, rfl⟩
  | commit site =>
      cases site with
      | here =>
          exact if outcome.isSome then
            FinDist.pure ⟨some (visible.get .here), by
              change decide (some (visible.get .here) = some (visible.get .here)) = true
              simp⟩
          else FinDist.pure ⟨none, rfl⟩
      | commit site =>
          cases site with
          | reveal site => cases site

/-- The other player's original source policy is retained verbatim. -/
theorem sourceStrategy_law (profile : SourceBehavioralProfile core)
    (outcome : Option Bool) :
    (denoteSource core
      (Profile.update (sig := sourceGameSignature core) profile 0 (sourceStrategy outcome))
      source.env).map (fun terminal => (true, some terminal.erasePubEnv)) =
      FinDist.pure (true, some (publicEnv outcome)) := by
  cases outcome with
  | none =>
      simp [core, tail, denoteSource, sourceStrategy, Profile.update,
        SourceBehavioralProfile.afterCommit,
        publicEnv, source, VEnv.erasePubEnv]
  | some value =>
      simp [core, tail, denoteSource, sourceStrategy, Profile.update,
        SourceBehavioralProfile.afterCommit,
        publicEnv, source, VEnv.erasePubEnv]
      rfl

def observation (execution : (image 10).application.PolicyExecution) :
    Bool × Option PublicEnv :=
  (execution.native.application.memory.finished compiled.graph.nodeCount,
    compiled.readPublicTerminal? execution.native.application.memory)

/-- Every completed law of the generated native application is an exact
finite mixture of source-owner deviations, with the other source policy
unchanged. The service, raw policies, and finite schedule are arbitrary.

This fragment has no chance and no decisions by the other source player.
Consequently each possible public terminal environment has a deterministic
owner realization. This argument does not generalize to hidden random prefixes
or games with an unchanged opponent's decisions. Completion is a premise, not
a conclusion or conditioning operation on the runtime distribution. -/
private theorem completed_law_representable (profile : SourceBehavioralProfile core)
    (players : Fin 2 → (image 10).application.PlayerPolicy)
    (environment : (image 10).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation (Fin 2)))
    (hcomplete : ∀ execution ∈ ((image 10).application.runPolicies players environment
        schedule (MessageApplication.PolicyExecution.initial (image 10).application
          (initialExecution 10))).support,
      execution.native.application.memory.finished compiled.graph.nodeCount = true) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy core (0 : Fin 2)),
      (((image 10).application.runPolicies players environment schedule
        (MessageApplication.PolicyExecution.initial (image 10).application
          (initialExecution 10))).map observation) =
        alternatives.bind fun replacement =>
          (denoteSource core
            (Profile.update (sig := sourceGameSignature core) profile 0 replacement)
            source.env).map (fun terminal => (true, some terminal.erasePubEnv)) := by
  let law := (image 10).application.runPolicies players environment schedule
    (MessageApplication.PolicyExecution.initial (image 10).application (initialExecution 10))
  refine ⟨law.map (fun execution => sourceStrategy
    (((observation execution).2.getD (publicEnv none)).get .here)), ?_⟩
  change law.map observation = _
  rw [FinDist.bind_map, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro execution hexecution
  have hfinished := hcomplete execution hexecution
  obtain ⟨terminal, _, hpublic⟩ := applicationPlan.runPolicies_source_public_outcome
    checked (fun _ => 10) (fun _ => none) players environment schedule execution
    hexecution hfinished
  change compiled.readPublicTerminal? execution.native.application.memory =
    some terminal.erasePubEnv at hpublic
  rw [sourceStrategy_law]
  change FinDist.pure (observation execution) = _
  simp only [observation, hfinished, hpublic, Option.getD_some]
  exact congrArg (fun env : PublicEnv => FinDist.pure (true, some env))
    (publicEnv_get terminal.erasePubEnv).symm

def deviatedPlayers (profile : SourceBehavioralProfile core)
    (replacement : (image 10).application.PlayerPolicy) :
    Fin 2 → (image 10).application.PlayerPolicy :=
  Profile.update (sig := MessageApplication.policySignature (Fin 2) (image 10).application)
    (applicationPlan.liftProfile (fun _ => 10) profile) 0 replacement

/-- Replace only the owner's native policy, leaving the lifted opponent
unchanged. Every completed deviation has the law of a finite mixture of legal
source-owner replacements. The decoder retains the completion flag. -/
theorem completed_owner_deviation_law (profile : SourceBehavioralProfile core)
    (replacement : (image 10).application.PlayerPolicy)
    (environment : (image 10).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation (Fin 2)))
    (hcomplete : ∀ execution ∈ ((image 10).application.runPolicies
        (deviatedPlayers profile replacement) environment schedule
        (applicationPlan.initialExecution (fun _ => 10))).support,
      execution.native.application.memory.finished compiled.graph.nodeCount = true) :
    ∃ alternatives : FinDist (SourceBehavioralPolicy core (0 : Fin 2)),
      (((image 10).application.runPolicies (deviatedPlayers profile replacement)
        environment schedule (applicationPlan.initialExecution (fun _ => 10))).map observation) =
        alternatives.bind fun alternative =>
          (denoteSource core
            (Profile.update (sig := sourceGameSignature core) profile 0 alternative)
            source.env).map (fun terminal => (true, some terminal.erasePubEnv)) :=
  completed_law_representable profile (deviatedPlayers profile replacement)
    environment schedule hcomplete

/-- The generated reference profile and service give a nonempty completed
law for every source profile, on exactly this native application. -/
theorem reference_law (profile : SourceBehavioralProfile core) :
    (((image 10).application.runPolicies (applicationPlan.liftProfile (fun _ => 10) profile)
      (image 10).serialService (image 10).serviceInvocations
      (applicationPlan.initialExecution (fun _ => 10))).map observation) =
      (denoteSource core profile source.env).map
        (fun terminal => (true, some terminal.erasePubEnv)) := by
  have hinitial : applicationPlan.InitialControllerReadsPublic := by
    apply applicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
    apply compiled.allInitialFieldsPublic_of_owners
    intro field hfield
    change field ∈ [] at hfield
    cases hfield
  have horigins : (image 10).HasBindingOrigins := by decide
  exact applicationPlan.service_source_public_law checked (fun _ => 10) profile
    hinitial horigins

theorem reference_complete (profile : SourceBehavioralProfile core)
    (execution : (image 10).application.PolicyExecution)
    (hsupport : execution ∈ ((image 10).application.runPolicies
      (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
      (image 10).serviceInvocations (applicationPlan.initialExecution (fun _ => 10))).support) :
    execution.native.application.memory.finished compiled.graph.nodeCount = true := by
  have hmap : observation execution ∈ (((image 10).application.runPolicies
      (applicationPlan.liftProfile (fun _ => 10) profile) (image 10).serialService
      (image 10).serviceInvocations (applicationPlan.initialExecution (fun _ => 10))).map
        observation).support := by
    rw [FinDist.support_map]
    exact ⟨execution, hsupport, rfl⟩
  rw [reference_law, FinDist.support_map] at hmap
  obtain ⟨terminal, _, heq⟩ := hmap
  exact (congrArg Prod.fst heq).symm

/-- Source lower bounds for any public-outcome valuation survive every
completed runtime owner deviation covered above; adversary utility is irrelevant. -/
theorem completed_owner_guarantee (profile : SourceBehavioralProfile core)
    (replacement : (image 10).application.PlayerPolicy)
    (environment : (image 10).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation (Fin 2)))
    (hcomplete : ∀ execution ∈ ((image 10).application.runPolicies
        (deviatedPlayers profile replacement) environment
        schedule (applicationPlan.initialExecution (fun _ => 10))).support,
      execution.native.application.memory.finished compiled.graph.nodeCount = true)
    (value : Bool × Option PublicEnv → ℝ) (bound : ℝ)
    (hbound : ∀ replacement : SourceBehavioralPolicy core (0 : Fin 2),
      bound ≤ ((denoteSource core
        (Profile.update (sig := sourceGameSignature core) profile 0 replacement) source.env).map
          (fun terminal => (true, some terminal.erasePubEnv))).expect value) :
    bound ≤ (((image 10).application.runPolicies
      (deviatedPlayers profile replacement) environment schedule
      (applicationPlan.initialExecution (fun _ => 10))).map observation).expect value := by
  obtain ⟨alternatives, hlaw⟩ := completed_owner_deviation_law profile replacement environment
    schedule hcomplete
  rw [hlaw, FinDist.expect_bind]
  calc
    bound = alternatives.expect (fun _ => bound) := (FinDist.expect_const _ _).symm
    _ ≤ _ := FinDist.expect_mono fun alternative _ => hbound alternative

/-- The completion premise cannot be omitted for this emitted artifact.
Its undecorated initial binding has no permissionless fallback. Permanent
owner silence defeats every finite mixture of source deviations, for every
environment and finite schedule, including services that include all traffic. -/
theorem withholding_no_deviation_mixture (profile : SourceBehavioralProfile core)
    (environment : (image 10).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation (Fin 2)))
    (alternatives : FinDist (SourceBehavioralPolicy core (0 : Fin 2))) :
    (((image 10).application.runPolicies
      (deviatedPlayers profile (fun _ _ => FinDist.pure .wait)) environment schedule
      (applicationPlan.initialExecution (fun _ => 10))).map observation) ≠
        alternatives.bind (fun alternative =>
          (denoteSource core
            (Profile.update (sig := sourceGameSignature core) profile 0 alternative)
            source.env).map (fun terminal => (true, some terminal.erasePubEnv))) := by
  have hrequired : (image 10).RequiresSubmission 0 0 := by
    exact applicationPlan.requiresSubmission (fun _ => 10) (.bind bindingCode)
      (by
        change _ ∈ [_, _]
        exact List.mem_cons_self)
      0 (by decide) 0 rfl
  have hwaiting := applicationPlan.withholding_finished_law checked
    (fun _ => 10) 0 0 hrequired (by decide)
    (applicationPlan.liftProfile (fun _ => 10) profile) environment schedule
  intro hlaw
  have hcompletion := congrArg (fun law => law.map Prod.fst) hlaw
  simp only [FinDist.map_bind, FinDist.map_comp, Function.comp_def,
    FinDist.map_const, FinDist.bind_const] at hcompletion
  change _ = FinDist.pure true at hcompletion
  change (((image 10).application.runPolicies
    (deviatedPlayers profile (fun _ _ => FinDist.pure .wait)) environment schedule
    (applicationPlan.initialExecution (fun _ => 10))).map
      (fun out => (observation out).1)) = FinDist.pure false at hwaiting
  rw [hwaiting] at hcompletion
  have hfalse : false ∈ (FinDist.pure true).support := by
    rw [← hcompletion]
    exact FinDist.mem_support_pure.mpr rfl
  simp only [FinDist.mem_support_pure, Bool.false_eq_true] at hfalse

end VegasTests.ConditionalDeviation

/-- info: 'VegasTests.ConditionalDeviation.completed_owner_deviation_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDeviation.completed_owner_deviation_law

/-- info: 'VegasTests.ConditionalDeviation.reference_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDeviation.reference_law

/-- info: 'VegasTests.ConditionalDeviation.completed_owner_guarantee' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDeviation.completed_owner_guarantee

/-- info: 'VegasTests.ConditionalDeviation.withholding_no_deviation_mixture' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalDeviation.withholding_no_deviation_mixture
