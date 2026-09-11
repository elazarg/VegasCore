/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingAction
import Vegas.Compile.WindowedSourcePolicy
import VegasTests.GeneratedApplicationSourceLaw
import VegasTests.WindowedSourceCoverage

/-! # Canonical source actions of raw focal binding blocks -/

noncomputable section

namespace VegasTests.WindowedBindingAction

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage

/-- Actual complete binding blocks extract the same source action for the
same initial information and pure raw replacement. The policy may commit
malformed data or withhold; the installed source fallback handles either. -/
theorem initial_binding_action_eq
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (left right : runtime.application.PolicyExecution)
    (hleft : left ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support)
    (hright : right ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    GeneratedBindingPolicy.code.resolvedValue (ty := .bool) false left.native.application.base =
      GeneratedBindingPolicy.code.resolvedValue (ty := .bool) false
        right.native.application.base := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [0, 1] 0
    (fun history view => FinDist.pure (command history view))
  have agreement : WindowedApplication.PolicyAgreement runtime 0 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  exact checkpoint.binding_block_action_eq checkpoint agreement command rfl
    bindingFallback bindingFallback 10 10 rfl rfl
    (by decide) 1 (by simp) (by decide) left right hleft hright

/-- An actual supported initial binding block inhabits the recursively assembled
checkpoint family, so the extracted source policy is the point mass at that
block's canonical resolved Boolean. -/
theorem initial_extractedSourcePolicy_at_binding
    (profile : SourceBehavioralProfile source.prog)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies
      (players profile (fun history view => FinDist.pure (command history view)))
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    ApplicationPlan.extractedSourcePolicy applicationPlan profile (fun _ => 10)
      bindingSelector choiceSelector (fun _ => 10) [0, 1] 0
      (fun history view => FinDist.pure (command history view))
      (compiledInitialCoupled source)
      GeneratedApplicationSourceLaw.initial_reads_public
      ApplicationBindingOrigins.persistent_image_has_binding_origins
      (by decide) (by
        intro _ _ owner _
        fin_cases owner <;> simp)
      command rfl 1 (by simp) (by decide) GeneratedBindingPolicy.site
      ((source.env.toView 0).eraseEnv) =
        FinDist.pure ⟨GeneratedBindingPolicy.code.resolvedValue (ty := .bool) false
          final.native.application.base, rfl⟩ := by
  let replacement : runtime.application.PlayerPolicy :=
    fun history view => FinDist.pure (command history view)
  let coupled := compiledInitialCoupled source
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
    bindingSelector choiceSelector (fun _ => 10) [0, 1] 0 replacement
  have sourcePrefix : ApplicationPlan.WindowedSourcePrefix applicationPlan profile
      (fun _ => 10) bindingSelector choiceSelector (fun _ => 10) [0, 1] 0 replacement coupled
      0 applicationPlan profile coupled initial :=
    .initial checkpoint
  let checkpoints : SourcePolicyCheckpoints source.prog (0 : TestPlayer) :=
    ApplicationPlan.sourcePolicyCheckpoints applicationPlan profile
    (fun _ => 10) bindingSelector choiceSelector (fun _ => 10) [0, 1] 0 replacement coupled
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins
    (by decide) (by
      intro _ _ owner _
      fin_cases owner <;> simp)
    command rfl 1 (by simp) (by decide)
  let witness : (checkpoints GeneratedBindingPolicy.site).Carrier := by
    exact
      { current := coupled
        execution := initial
        final := final
        sourcePrefix := sourcePrefix
        fallback := bindingFallback
        deadline := 10
        selected := rfl
        block := hfinal }
  have hat := ApplicationPlan.extractedSourcePolicy_at_checkpoint applicationPlan profile
    (fun _ => 10) bindingSelector choiceSelector (fun _ => 10) [0, 1] 0 replacement coupled
    GeneratedApplicationSourceLaw.initial_reads_public
    ApplicationBindingOrigins.persistent_image_has_binding_origins
    (by decide) (by
      intro _ _ owner _
      fin_cases owner <;> simp)
    command rfl 1 (by simp) (by decide) GeneratedBindingPolicy.site witness
  exact hat

end VegasTests.WindowedBindingAction

/-- info: 'VegasTests.WindowedBindingAction.initial_binding_action_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingAction.initial_binding_action_eq

/-- info: 'VegasTests.WindowedBindingAction.initial_extractedSourcePolicy_at_binding'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingAction.initial_extractedSourcePolicy_at_binding
