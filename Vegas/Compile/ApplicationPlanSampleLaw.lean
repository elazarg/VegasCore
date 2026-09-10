/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSampleLaw
import Vegas.Compile.WindowedSourceSafety

/-! # Fixed chance preservation for generated application plans

Compiler allocation discharges all frame conditions. Both optional timeout
families and activation-relative scheduling retain the selected sample and its
law. Resolution remains an operational premise on the unconditioned run; the
theorem does not give an environment the power to supply or choose entropy.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

/-- Every fixed-distribution sample in a generated plan retains its emitted
law under arbitrary public-message policies, relative windows, and optional
source fallbacks. Only resolution of the selected sample is required; the
rest of the program need not finish. -/
theorem windowed_runPolicies_sample_law (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (code : SampleCode L) (hcode : .sample code ∈ (plan.image deadlineOf).instructions)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hnotDone : execution.native.application.base.memory.done code.node = false)
    (hresolved : ∀ next ∈
      ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
        players environment schedule execution).support,
      next.native.application.base.memory.done code.node = true) :
    ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule execution).map
        (fun next => code.read? next.native.application.base.memory) = law.map some := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  have hmem : .sample code ∈ runtime.image.instructions :=
    List.mem_map.mpr ⟨.sample code, List.mem_map.mpr ⟨.sample code, hcode, rfl⟩, rfl⟩
  have hnodes : (runtime.image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup := by
    change ((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).instructions.flatMap ApplicationInstruction.coveredNodes).Nodup
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    exact plan.coveredNodes_nodup deadlineOf
  have hfields :
      (runtime.image.instructions.flatMap ApplicationInstruction.allocatedFields).Nodup := by
    change ((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
      choice).instructions.flatMap ApplicationInstruction.allocatedFields).Nodup
    rw [ApplicationImage.allocatedFields_withChoiceTimeouts,
      ApplicationImage.allocatedFields_withBindingTimeouts]
    exact plan.allocatedFields_nodup deadlineOf
  exact runtime.runPolicies_sample_law code hmem hnodes hfields law hfixed
    players environment schedule execution hnotDone hresolved

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_runPolicies_sample_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_runPolicies_sample_law
