/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingAction
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
  exact checkpoint.binding_block_action_eq checkpoint agreement rfl command rfl
    bindingFallback 10 rfl (by decide) 1 (by simp) (by decide) left right hleft hright

end VegasTests.WindowedBindingAction

/-- info: 'VegasTests.WindowedBindingAction.initial_binding_action_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedBindingAction.initial_binding_action_eq
