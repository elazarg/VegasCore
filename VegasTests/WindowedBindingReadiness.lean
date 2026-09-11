/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingReadiness
import VegasTests.GeneratedApplicationSourceLaw
import VegasTests.GeneratedBindingPolicy

/-! # Binding from the original compiled source profile

The persistent-disclosure program starts with an opaque binding. These tests
use its whole source profile and canonical initial checkpoint, with an
arbitrary raw replacement for the other player. No binding-specific policy,
dispatch equation, or readout witness is supplied to the compiler theorem.
-/

noncomputable section

namespace VegasTests.WindowedBindingReadiness

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure

def runtime : WindowedApplication TestPlayer simpleExpr :=
  applicationPlan.windowed (fun _ => 10) (fun code => code.timeout)
    (fun code => code.timeout) (fun _ => 10)

def initial : runtime.application.PolicyExecution :=
  applicationPlan.windowedInitialExecution (fun _ => 10) (fun code => code.timeout)
    (fun code => code.timeout) (fun _ => 10)

def players (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile (fun _ => 10) (fun code => code.timeout)
    (fun code => code.timeout) (fun _ => 10) 1 replacement

/-- The compiled dispatcher samples exactly the head source kernel and then
submits its generated opaque handle, for every whole source profile. -/
theorem source_law (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) :
    runtime.application.runPolicies (players profile replacement) environment
      [.player 0, .player 0] initial =
      (profile 0 GeneratedBindingPolicy.site ((source.env.toView 0).eraseEnv)).bind
        fun chosen =>
          (runtime.application.playerStep 0 initial
            (.privateCommand (.register 0 ⟨.bool, chosen.1⟩))).bind fun registered =>
              runtime.application.playerStep 0 registered (.submit (.binding 0 (0, 0))) := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    (fun code => code.timeout) (fun code => code.timeout) (fun _ => 10)
    [0, 1] 1 replacement
  exact checkpoint.binding_polls_source_law GeneratedApplicationSourceLaw.initial_reads_public
    (by decide) (by simp) (checkpoint.referenceOwner_of_ne 0 (by decide)) environment

/-- Arbitrarily many polls of the raw replacement may precede the binding.
Its complete native prefix is retained, and the subsequent unchanged-owner
draw still has the original source distribution. -/
theorem source_law_after_raw_polls (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy) (count : Nat) :
    runtime.application.runPolicies (players profile replacement) environment
      (List.replicate count (.player 1) ++ [.player 0, .player 0]) initial =
      (runtime.application.runPolicies (players profile replacement) environment
        (List.replicate count (.player 1)) initial).bind fun middle =>
          (profile 0 GeneratedBindingPolicy.site ((source.env.toView 0).eraseEnv)).bind
            fun chosen =>
              (runtime.application.playerStep 0 middle
                (.privateCommand (.register 0 ⟨.bool, chosen.1⟩))).bind fun registered =>
                  runtime.application.playerStep 0 registered (.submit (.binding 0 (0, 0))) := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    (fun code => code.timeout) (fun code => code.timeout) (fun _ => 10)
    [0, 1] 1 replacement
  exact checkpoint.binding_polls_source_law_after_others
    GeneratedApplicationSourceLaw.initial_reads_public (by decide) (by simp)
    (checkpoint.referenceOwner_of_ne 0 (by decide))
    environment (List.replicate count (.player 1)) (by simp) (by simp)

/-- Hidden sampling preserves the other player's complete policy input even
after the real pending packet is included and produces a public receipt. -/
theorem included_observer_agreement (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (left right : runtime.application.PolicyExecution)
    (hleft : left ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.application.includeLatestFrom 0)
      [.player 0, .player 0, .environment] initial).support)
    (hright : right ∈ (runtime.application.runPolicies (players profile replacement)
      (runtime.application.includeLatestFrom 0)
      [.player 0, .player 0, .environment] initial).support) :
    WindowedApplication.PolicyAgreement runtime 1 left right := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    (fun code => code.timeout) (fun code => code.timeout) (fun _ => 10)
    [0, 1] 1 replacement
  have agreement : WindowedApplication.PolicyAgreement runtime 1 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  exact checkpoint.binding_inclusion_agreement _ _ checkpoint agreement
    GeneratedApplicationSourceLaw.initial_reads_public
    (by decide) (by simp) (by decide) left right hleft hright

/-- The inclusion succeeds and retains the exact original source distribution
in its accepted private snapshot; privacy is not obtained by rejecting it. -/
theorem included_source_law (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy) :
    (runtime.application.runPolicies (players profile replacement)
      (runtime.application.includeLatestFrom 0)
      [.player 0, .player 0, .environment] initial).map (fun execution =>
        (execution.native.application.base.frozen 0, execution.native.receipts)) =
      (profile 0 GeneratedBindingPolicy.site ((source.env.toView 0).eraseEnv)).map
        (fun chosen =>
          (some (⟨.bool, chosen.1⟩ : TypedValue simpleExpr), [((0, 0), true)])) := by
  change (runtime.application.runPolicies (players profile replacement)
    (runtime.application.includeLatestFrom 0)
    ([.player 0, .player 0] ++ [.environment]) initial).map _ = _
  rw [MessageApplication.runPolicies_append, source_law]
  simp only [FinDist.bind_bind, FinDist.map_bind]
  simp only [MessageApplication.playerStep, MessageApplication.advance, PlayerCommand.toAction,
    MessageApplication.step, FinDist.pure_bind, MessageApplication.runPolicies,
    MessageApplication.invoke, MessageApplication.includeLatestFrom, FinDist.bind_pure]
  conv_rhs => rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro chosen _
  change (runtime.application.environmentPolicyStep _ (.include (0, 0))).map _ = _
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.map_pure]
  rfl

end VegasTests.WindowedBindingReadiness

/-- info: 'VegasTests.WindowedBindingReadiness.source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingReadiness.source_law

/-- info: 'VegasTests.WindowedBindingReadiness.source_law_after_raw_polls' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingReadiness.source_law_after_raw_polls

/-- info: 'VegasTests.WindowedBindingReadiness.included_observer_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingReadiness.included_observer_agreement

/-- info: 'VegasTests.WindowedBindingReadiness.included_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingReadiness.included_source_law
