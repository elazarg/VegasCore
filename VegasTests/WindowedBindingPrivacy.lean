/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingPrivacy
import VegasTests.WindowedSourceCoverage
import VegasTests.GeneratedApplicationSourceLaw

/-! # Privacy of the initial generated binding block -/

noncomputable section

namespace VegasTests.WindowedBindingPrivacy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

def replacement
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) : runtime.application.PlayerPolicy :=
  fun history view => FinDist.pure (command history view)

def players (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) :
    TestPlayer → runtime.application.PlayerPolicy :=
  applicationPlan.windowedPlayers profile (fun _ => 10) bindingSelector choiceSelector
    (fun _ => 10) 1 (replacement command)

/-- Different private draws made by the unchanged binding owner remain
indistinguishable to an arbitrary pure raw focal policy after the complete
actual generated block. No readiness, acceptance, or settlement premise is
supplied by the test. -/
theorem initial_binding_block_agreement
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (left right : runtime.application.PolicyExecution)
    (hleft : left ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support)
    (hright : right ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    WindowedApplication.PolicyAgreement runtime 1 left right := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [0, 1] 1 (replacement command)
  have agreement : WindowedApplication.PolicyAgreement runtime 1 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  exact ApplicationPlan.WindowedCheckpoint.binding_block_agreement _ _ profile _ _
    initial initial checkpoint checkpoint agreement
    GeneratedApplicationSourceLaw.initial_reads_public command rfl
    (by decide) (by simp) (by decide) left right hleft hright

end VegasTests.WindowedBindingPrivacy

/-- info: 'VegasTests.WindowedBindingPrivacy.initial_binding_block_agreement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingPrivacy.initial_binding_block_agreement
