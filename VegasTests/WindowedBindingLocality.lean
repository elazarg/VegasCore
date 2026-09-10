/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingLocality
import Vegas.Compile.WindowedSourceSafety
import VegasTests.GeneratedBindingPolicy

/-! # Hidden randomized binding on a compiled windowed application -/

noncomputable section

namespace VegasTests.WindowedBindingLocality

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
  VegasTests.GeneratedBindingPolicy

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed (fun _ => 10) (fun code => code.timeout)
    (fun code => code.timeout) (fun _ => 10)

def initial : runtime.application.PolicyExecution :=
  PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application
      (runtime.initial initialExecution.application))

def players (law : FinDist Bool) : TestPlayer → runtime.application.PlayerPolicy :=
  fun actor => runtime.blockPlayer actor
    (runtime.liftPlayerPolicy (GeneratedBindingPolicy.players law actor))

def environment : runtime.application.EnvironmentPolicy := fun _ _ => FinDist.pure .wait

/-- All local prerequisites hold at the real initialized compiled image. -/
theorem initial_ready : site.WindowedBindingPollsReady source.fresh compilerInitial image
    runtime (.bind code) initial source.env := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl⟩
  exact initial_readout

/-- The emitted two-poll policy has the exact arbitrary source sampling law;
the result includes its native preparation, pool, and histories. -/
theorem source_law (law : FinDist Bool) :
    runtime.application.runPolicies (players law) environment [.player 0, .player 0] initial =
      law.bind fun secret =>
        (runtime.application.playerStep 0 initial
          (.privateCommand (.register 0 ⟨.bool, secret⟩))).bind fun registered =>
            runtime.application.playerStep 0 registered (.submit (.binding 0 (0, 0))) := by
  have h := site.windowedBinding_two_invocations_source_law source.fresh compilerInitial image
    runtime (sourcePolicy law) (GeneratedBindingPolicy.players law 0)
    (players law) environment rfl (.bind code) initial source.env
    (by intro history; simp [GeneratedBindingPolicy.players]) initial_ready
  simpa only [sourcePolicy, FinDist.bind_map,
    show site.compiledField source.fresh compilerInitial = 0 from rfl,
    show (site.bindingCode source.fresh compilerInitial 0).node = 0 from rfl] using h

/-- Every pair of supported hidden draws has identical observer input after
both actual owner polls. This uses the concrete controller laws, not assumed
agreement of its sampled values or commands. -/
theorem observer_agreement (law : FinDist Bool)
    (left right : runtime.application.PolicyExecution)
    (hleft : left ∈ (runtime.application.runPolicies (players law) environment
      [.player 0, .player 0] initial).support)
    (hright : right ∈ (runtime.application.runPolicies (players law) environment
      [.player 0, .player 0] initial).support) :
    WindowedApplication.PolicyAgreement runtime 1 left right := by
  have hagree : WindowedApplication.PolicyAgreement runtime 1 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  apply hagree.binding_twoPolls_of_ready (by decide) site source.fresh compilerInitial image
    (sourcePolicy law) (GeneratedBindingPolicy.players law 0) (players law) environment rfl
    (.bind code) source.env source.env initial_ready initial_ready _ _ left right hleft hright
  all_goals intro history; simp [GeneratedBindingPolicy.players]

end VegasTests.WindowedBindingLocality

/-- info: 'VegasTests.WindowedBindingLocality.source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingLocality.source_law

/-- info: 'VegasTests.WindowedBindingLocality.observer_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingLocality.observer_agreement
