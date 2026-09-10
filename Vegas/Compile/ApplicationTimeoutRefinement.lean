/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationChoiceTimeouts
import Vegas.Compile.ApplicationPlanRefinement

/-! # Refinement safety for public-choice timeout decoration

Decorating a generated application image with optional public-choice timeout
code preserves its graph-reachability invariant. An accepted timeout has the
same application-state effect as a proof-only accepted ordinary request in the
undecorated image; it does not add that request to the actual execution history.
The shared native and policy runners then lift this local fact to arbitrary
supported schedules. No progress or strategy correspondence is asserted.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

/-- Every accepted packet in a timeout-decorated image retains a reachable
configuration of the original generated graph. -/
theorem withChoiceTimeouts_handle_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicChoiceTimeout L code.guard.ty))
    (initial : VEnv L Γ) (legal : Legal prog) (native next : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph) (hrefines : native.Refines cfg)
    (message : Message P (ApplicationImage.Payload P L))
    (hnext : ((plan.image deadlineOf).withChoiceTimeouts select).handle native message =
      some next) :
    ∃ cfg' : Config (compileCore prog fresh build).graph, next.Refines cfg' := by
  obtain ⟨original, horiginal⟩ :=
    (plan.image deadlineOf).handle_withChoiceTimeouts_source select native message next hnext
  exact plan.handle_refines deadlineOf initial legal native cfg hrefines original next horiginal

private theorem timeout_private_preserves
    (image : ApplicationImage P L) (graph : Graph P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicChoiceTimeout L code.guard.ty))
    (native : ApplicationImage.State P L) (who : P)
    (command : (image.withChoiceTimeouts select).application.PrivateCommand)
    (hstate : ∃ cfg : Config graph, native.Refines cfg) :
    ∃ cfg : Config graph,
      (((image.withChoiceTimeouts select).application.privateStep native who command)
        : ApplicationImage.State P L).Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  cases command with
  | register slot value => exact ⟨cfg, hrefines.register who slot value⟩

private theorem timeout_environment_preserves
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicChoiceTimeout L code.guard.ty))
    (native : ApplicationImage.State P L)
    (command : ((plan.image deadlineOf).withChoiceTimeouts select).application.EnvironmentCommand)
    (next : ApplicationImage.State P L)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withChoiceTimeouts select).application.environmentStep
        native command).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.Refines cfg := by
  apply plan.environment_refines deadlineOf native command next hstate
  cases command with
  | advance clock => exact hnext
  | sample address =>
      change next ∈ (((plan.image deadlineOf).withChoiceTimeouts select).sample
        native address).support at hnext
      change next ∈ ((plan.image deadlineOf).sample native address).support
      rwa [(plan.image deadlineOf).sample_withChoiceTimeouts select native address] at hnext

/-- Arbitrary shared native action lists preserve graph refinement after
public-choice timeout decoration. -/
theorem withChoiceTimeouts_run_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicChoiceTimeout L code.guard.ty))
    (initial : VEnv L Γ) (legal : Legal prog)
    (state next : ((plan.image deadlineOf).withChoiceTimeouts select).application.State)
    (actions : List
      ((plan.image deadlineOf).withChoiceTimeouts select).application.Action)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      state.application.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withChoiceTimeouts select).application.run actions state).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.application.Refines cfg := by
  let image := (plan.image deadlineOf).withChoiceTimeouts select
  apply image.application.run_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (timeout_private_preserves (plan.image deadlineOf)
      (compileCore prog fresh build).graph select) _
    (timeout_environment_preserves plan deadlineOf select)
    state next actions hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.withChoiceTimeouts_handle_refines deadlineOf select initial legal native updated
    cfg hrefines message hupdated

/-- Arbitrary randomized player and environment policies preserve graph
refinement after public-choice timeout decoration. -/
theorem withChoiceTimeouts_runPolicies_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicChoiceTimeout L code.guard.ty))
    (initial : VEnv L Γ) (legal : Legal prog)
    (players : P →
      ((plan.image deadlineOf).withChoiceTimeouts select).application.PlayerPolicy)
    (environment :
      ((plan.image deadlineOf).withChoiceTimeouts select).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution next :
      ((plan.image deadlineOf).withChoiceTimeouts select).application.PolicyExecution)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      execution.native.application.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withChoiceTimeouts select).application.runPolicies
        players environment schedule execution).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph,
      next.native.application.Refines cfg := by
  let image := (plan.image deadlineOf).withChoiceTimeouts select
  apply image.application.runPolicies_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (timeout_private_preserves (plan.image deadlineOf)
      (compileCore prog fresh build).graph select) _
    (timeout_environment_preserves plan deadlineOf select)
    players environment schedule execution next hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.withChoiceTimeouts_handle_refines deadlineOf select initial legal native updated
    cfg hrefines message hupdated

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.withChoiceTimeouts_run_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withChoiceTimeouts_run_refines

/-- info: 'Vegas.ApplicationPlan.withChoiceTimeouts_runPolicies_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withChoiceTimeouts_runPolicies_refines
