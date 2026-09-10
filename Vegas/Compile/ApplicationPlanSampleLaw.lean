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
Accepted opaque snapshots also retain their full joint law and are jointly
independent of a later fixed sample, including when the snapshots are missing
or ill-typed. Their interpretation as source choices is a separate obligation.
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

/-- A fixed sample is jointly independent of earlier accepted opaque snapshots.
The prefix law may contain arbitrary correlations, private state, malformed
bindings, and policy histories. All of that state is retained by the suffix
runner. Both coordinates are read from the final execution, using snapshot
stability. The snapshot coordinate is an analysis readout, not a public
observation. Public-default values are not covered by the opaque premise.

The sample must be unresolved throughout the prefix and resolved throughout
the unconditioned final law. No independence premise is imposed on the prefix
or on the history-dependent suffix policies. -/
theorem windowed_runPolicies_snapshots_sample_law (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (code : SampleCode L) (hcode : .sample code ∈ (plan.image deadlineOf).instructions)
    (law : FinDist (L.Val code.dist.ty)) (hfixed : ∀ reads, code.dist.eval reads = law)
    (fields : List Nat)
    (initialLaw : FinDist
      (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (players : P → (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (hbound : ∀ execution ∈ initialLaw.support, ∀ field ∈ fields, ∃ handle,
      execution.native.application.base.memory.accepted field = some (.opaque handle))
    (hnotDone : ∀ execution ∈ initialLaw.support,
      execution.native.application.base.memory.done code.node = false)
    (hresolved : ∀ next ∈ (initialLaw.bind
      ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
        players environment schedule)).support,
      next.native.application.base.memory.done code.node = true) :
    (initialLaw.bind ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      players environment schedule)).map (fun next =>
        (fields.map next.native.application.base.frozen,
          code.read? next.native.application.base.memory)) =
      FinDist.product
        (initialLaw.map (fun execution => fields.map execution.native.application.base.frozen))
        (law.map some) := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  rw [FinDist.map_bind, FinDist.product, FinDist.bind_map]
  apply FinDist.bind_congr
  intro execution hexecution
  have hstable : ∀ next ∈ (runtime.application.runPolicies
      players environment schedule execution).support,
      fields.map next.native.application.base.frozen =
        fields.map execution.native.application.base.frozen := by
    intro next hnext
    apply List.map_congr_left
    intro field hfield
    obtain ⟨handle, haccepted⟩ := hbound execution hexecution field hfield
    exact (runtime.runPolicies_acceptedSnapshot field handle
      (execution.native.application.base.frozen field) players environment schedule
      execution next ⟨haccepted, rfl⟩ hnext).2
  have hsample := plan.windowed_runPolicies_sample_law deadlineOf binding choice windowOf
    code hcode law hfixed players environment schedule execution (hnotDone execution hexecution)
    (fun next hnext => hresolved next (by
      rw [FinDist.support_bind]
      exact Set.mem_iUnion.mpr ⟨execution, Set.mem_iUnion.mpr ⟨hexecution, hnext⟩⟩))
  calc
    _ = (runtime.application.runPolicies players environment schedule execution).map
        (fun next => (fields.map execution.native.application.base.frozen,
          code.read? next.native.application.base.memory)) := by
      apply FinDist.bind_congr
      intro next hnext
      exact congrArg (fun snapshot => FinDist.pure
        (snapshot, code.read? next.native.application.base.memory)) (hstable next hnext)
    _ = ((runtime.application.runPolicies players environment schedule execution).map
        (fun next => code.read? next.native.application.base.memory)).map
          (fun value => (fields.map execution.native.application.base.frozen, value)) := by
      rw [FinDist.map_comp]
      rfl
    _ = _ := congrArg (FinDist.map
      (fun value => (fields.map execution.native.application.base.frozen, value))) hsample

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_runPolicies_snapshots_sample_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_runPolicies_snapshots_sample_law

/-- info: 'Vegas.ApplicationPlan.windowed_runPolicies_sample_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_runPolicies_sample_law
