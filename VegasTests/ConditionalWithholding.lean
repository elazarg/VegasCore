/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.ConditionalSourcePolicies
import Vegas.Compile.ApplicationWithholding

/-! # Withholding in the undecorated conditional fragment

The generated artifact without a source-certified binding fallback cannot be
completed by a finite service when its owner remains silent.
-/

noncomputable section

namespace VegasTests.ConditionalWithholding

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  GameTheory GameTheory.Math.Probability
open VegasTests.ConditionalApplicationImage
open VegasTests.ConditionalSourcePolicies

def observation (execution : (image 10).application.PolicyExecution) :
    Bool × Option PublicEnv :=
  (execution.native.application.memory.finished compiled.graph.nodeCount,
    compiled.readPublicTerminal? execution.native.application.memory)

def deviatedPlayers (profile : SourceBehavioralProfile core)
    (replacement : (image 10).application.PlayerPolicy) :
    Fin 2 → (image 10).application.PlayerPolicy :=
  Profile.update (sig := MessageApplication.policySignature (Fin 2) (image 10).application)
    (applicationPlan.liftProfile (fun _ => 10) profile) 0 replacement

/-- The undecorated initial binding has no permissionless fallback. Permanent
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

end VegasTests.ConditionalWithholding

/-- info: 'VegasTests.ConditionalWithholding.withholding_no_deviation_mixture' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalWithholding.withholding_no_deviation_mixture
