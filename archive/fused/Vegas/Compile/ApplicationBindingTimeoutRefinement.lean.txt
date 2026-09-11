/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationBindingTimeouts
import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.BindingResolution

/-! # Refinement safety for binding-timeout decoration

An accepted binding expiry installs its evaluated typed public fallback.  At
the generated unrestricted source commitment that value is an ordinary legal
commit step.  This is support-level safety for arbitrary raw traffic; it does
not promise expiry submission, inclusion, later conditional progress, or a
strategy correspondence.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

/-- Every packet accepted by a binding-timeout-decorated image retains a
reachable configuration of the original generated graph.  The expiry branch
uses the actual evaluated fallback value, not a fabricated binding packet or
commitment handle. -/
theorem withBindingTimeouts_handle_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : BindingCode P L) →
      Option (PublicFallbackCode L code.ty))
    (initial : VEnv L Γ) (legal : Legal prog)
    (native next : ApplicationImage.State P L)
    (cfg : Config (compileCore prog fresh build).graph)
    (hrefines : native.Refines cfg)
    (message : Message P (ApplicationImage.Payload P L))
    (hnext : ((plan.image deadlineOf).withBindingTimeouts select).handle native message =
      some next) :
    ∃ cfg' : Config (compileCore prog fresh build).graph, next.Refines cfg' := by
  let image := plan.image deadlineOf
  cases message with
  | mk id payload =>
      by_cases hordinary : payload.NotBindingExpiry
      · rw [image.handle_withBindingTimeouts select native ⟨id, payload⟩ hordinary] at hnext
        exact plan.handle_refines deadlineOf initial legal native cfg hrefines
          ⟨id, payload⟩ next hnext
      cases payload with
      | expireBinding address =>
          have hdispatch := hnext
          change (image.withBindingTimeouts select).handle native
            ⟨id, .expireBinding address⟩ = some next at hdispatch
          simp only [ApplicationImage.handle,
            ApplicationImage.lookup_withBindingTimeouts] at hdispatch
          cases hlookup : image.lookup address with
          | none => simp [hlookup] at hdispatch
          | some instruction =>
              cases instruction with
              | sample code | publicChoice code | conditional code =>
                  simp [hlookup, ApplicationInstruction.withBindingTimeouts] at hdispatch
              | bind code =>
                  let timed : BindingCode P L := { code with timeout := select code }
                  simp only [hlookup, Option.map_some,
                    ApplicationInstruction.withBindingTimeouts] at hdispatch
                  change (timed.resolveTimeout? native.memory).map
                      (fun value => native.defaultBind timed ⟨timed.ty, value⟩) =
                    some next at hdispatch
                  cases hvalue : timed.resolveTimeout? native.memory with
                  | none => simp [hvalue] at hdispatch
                  | some value =>
                      simp only [hvalue, Option.map_some] at hdispatch
                      cases hdispatch
                      cases plan.origin_of_lookup deadlineOf address (.bind code) hlookup with
                      | binding site unrestricted =>
                          obtain ⟨hunbound, hnotDone, hrequires, _⟩ :=
                            timed.resolveTimeout?_some native.memory value hvalue
                          obtain ⟨step⟩ := site.binding_value_step fresh build initial legal
                            unrestricted native cfg hrefines.memory hrefines.reachable
                            (decisionSiteState site fresh build).nextField hnotDone hrequires value
                          exact ⟨_, hrefines.defaultBind
                            (compileCore prog fresh build).graphWF timed
                            (site.compiledNode fresh build) rfl rfl ⟨timed.ty, value⟩ step⟩
      | malformed data => exact False.elim (hordinary trivial)
      | choice address typed => exact False.elim (hordinary trivial)
      | expireChoice address => exact False.elim (hordinary trivial)
      | binding address handle => exact False.elim (hordinary trivial)
      | conditional address payload => exact False.elim (hordinary trivial)

private theorem bindingTimeout_private_preserves
    (image : ApplicationImage P L) (graph : Graph P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (native : ApplicationImage.State P L) (who : P)
    (command : (image.withBindingTimeouts select).application.PrivateCommand)
    (hstate : ∃ cfg : Config graph, native.Refines cfg) :
    ∃ cfg : Config graph,
      (((image.withBindingTimeouts select).application.privateStep native who command) :
        ApplicationImage.State P L).Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  cases command with
  | register slot value => exact ⟨cfg, hrefines.register who slot value⟩

private theorem bindingTimeout_environment_preserves
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (native : ApplicationImage.State P L)
    (command : ((plan.image deadlineOf).withBindingTimeouts select).application.EnvironmentCommand)
    (next : ApplicationImage.State P L)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withBindingTimeouts select).application.environmentStep
        native command).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.Refines cfg := by
  apply plan.environment_refines deadlineOf native command next hstate
  cases command with
  | advance clock => exact hnext
  | sample address =>
      change next ∈ (((plan.image deadlineOf).withBindingTimeouts select).sample
        native address).support at hnext
      change next ∈ ((plan.image deadlineOf).sample native address).support
      rwa [(plan.image deadlineOf).sample_withBindingTimeouts select native address] at hnext

/-- Arbitrary shared native action lists retain graph refinement under binding
timeouts. Rejected, delivered, and replayed raw traffic require no fairness or
honesty premise. -/
theorem withBindingTimeouts_run_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (initial : VEnv L Γ) (legal : Legal prog)
    (state next : ((plan.image deadlineOf).withBindingTimeouts select).application.State)
    (actions : List
      ((plan.image deadlineOf).withBindingTimeouts select).application.Action)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      state.application.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withBindingTimeouts select).application.run
        actions state).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph,
      next.application.Refines cfg := by
  let image := (plan.image deadlineOf).withBindingTimeouts select
  apply image.application.run_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (bindingTimeout_private_preserves (plan.image deadlineOf)
      (compileCore prog fresh build).graph select) _
    (bindingTimeout_environment_preserves plan deadlineOf select)
    state next actions hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.withBindingTimeouts_handle_refines deadlineOf select initial legal native updated
    cfg hrefines message hupdated

/-- Arbitrary randomized policies and invocation schedules retain graph
refinement under binding-timeout decoration. This is a safety invariant, not a
progress or source-policy simulation theorem. -/
theorem withBindingTimeouts_runPolicies_refines
    (plan : ApplicationPlan accounted fresh build) (deadlineOf : Nat → Nat)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (initial : VEnv L Γ) (legal : Legal prog)
    (players : P →
      ((plan.image deadlineOf).withBindingTimeouts select).application.PlayerPolicy)
    (environment :
      ((plan.image deadlineOf).withBindingTimeouts select).application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution next :
      ((plan.image deadlineOf).withBindingTimeouts select).application.PolicyExecution)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      execution.native.application.Refines cfg)
    (hnext : next ∈
      (((plan.image deadlineOf).withBindingTimeouts select).application.runPolicies
        players environment schedule execution).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph,
      next.native.application.Refines cfg := by
  let image := (plan.image deadlineOf).withBindingTimeouts select
  apply image.application.runPolicies_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (bindingTimeout_private_preserves (plan.image deadlineOf)
      (compileCore prog fresh build).graph select) _
    (bindingTimeout_environment_preserves plan deadlineOf select)
    players environment schedule execution next hstate hnext
  rintro native message updated ⟨cfg, hrefines⟩ hupdated
  exact plan.withBindingTimeouts_handle_refines deadlineOf select initial legal native updated
    cfg hrefines message hupdated

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.withBindingTimeouts_handle_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withBindingTimeouts_handle_refines

/-- info: 'Vegas.ApplicationPlan.withBindingTimeouts_run_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withBindingTimeouts_run_refines

/-- info: 'Vegas.ApplicationPlan.withBindingTimeouts_runPolicies_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.withBindingTimeouts_runPolicies_refines
