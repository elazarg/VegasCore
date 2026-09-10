/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationPlanRefinement
import Vegas.Compile.ApplicationSourceOutcome

/-! # Source safety of ordered application execution

The admission rule removes handler effects and disables out-of-order chance
requests. It preserves the generated application's graph invariant under all
raw commands and randomized policies. Rejected traffic is still present in
the native observations. These are support guarantees, not equality of laws
or a simulation of deviations.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {build : BuildState P L Γ}

private theorem ordered_private_refines (image : ApplicationImage P L) (graph : Graph P L)
    (state : ApplicationImage.State P L) (who : P)
    (command : image.orderedApplication.PrivateCommand)
    (hstate : ∃ cfg : Config graph, state.Refines cfg) :
    ∃ cfg : Config graph, (image.orderedApplication.privateStep state who command).Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  cases command with
  | register slot value => exact ⟨cfg, hrefines.register who slot value⟩

private theorem ordered_handle_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (state : ApplicationImage.State P L)
    (message : Message P (ApplicationImage.Payload P L)) (next : ApplicationImage.State P L)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, state.Refines cfg)
    (hnext : (plan.image deadlineOf).orderedApplication.handle state message = some next) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.Refines cfg := by
  obtain ⟨cfg, hrefines⟩ := hstate
  apply plan.handle_refines deadlineOf initial legal state cfg hrefines message next
  exact (plan.image deadlineOf).application.withAdmission_handle_some
    (plan.image deadlineOf).admitsMessage (plan.image deadlineOf).admitsEnvironment
    state next message hnext

private theorem ordered_environment_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (state : ApplicationImage.State P L)
    (command : (plan.image deadlineOf).orderedApplication.EnvironmentCommand)
    (next : ApplicationImage.State P L)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, state.Refines cfg)
    (hnext : next ∈
      ((plan.image deadlineOf).orderedApplication.environmentStep state command).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.Refines cfg := by
  rcases (plan.image deadlineOf).application.withAdmission_environment_support
    (plan.image deadlineOf).admitsMessage (plan.image deadlineOf).admitsEnvironment
    state next command hnext with rfl | horiginal
  · exact hstate
  · exact plan.environment_refines deadlineOf state command next hstate horiginal

/-- Ordered admission retains a reachable graph witness under every supported
native action list, including premature traffic and rejection. -/
theorem ordered_run_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (state next : (plan.image deadlineOf).orderedApplication.State)
    (actions : List (plan.image deadlineOf).orderedApplication.Action)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph, state.application.Refines cfg)
    (hnext : next ∈ ((plan.image deadlineOf).orderedApplication.run actions state).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.application.Refines cfg := by
  exact (plan.image deadlineOf).orderedApplication.run_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (ordered_private_refines _ _) (ordered_handle_refines plan deadlineOf initial legal)
    (ordered_environment_refines plan deadlineOf) state next actions hstate hnext

/-- The same invariant holds for arbitrary player and environment policies;
admission restricts successful effects, not the policies' command space. -/
theorem ordered_runPolicies_refines (plan : ApplicationPlan accounted fresh build)
    (deadlineOf : Nat → Nat) (initial : VEnv L Γ) (legal : Legal prog)
    (players : P → (plan.image deadlineOf).orderedApplication.PlayerPolicy)
    (environment : (plan.image deadlineOf).orderedApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (execution next : (plan.image deadlineOf).orderedApplication.PolicyExecution)
    (hstate : ∃ cfg : Config (compileCore prog fresh build).graph,
      execution.native.application.Refines cfg)
    (hnext : next ∈ ((plan.image deadlineOf).orderedApplication.runPolicies
      players environment schedule execution).support) :
    ∃ cfg : Config (compileCore prog fresh build).graph, next.native.application.Refines cfg := by
  exact (plan.image deadlineOf).orderedApplication.runPolicies_application_invariant
    (fun native => ∃ cfg : Config (compileCore prog fresh build).graph, native.Refines cfg)
    (ordered_private_refines _ _) (ordered_handle_refines plan deadlineOf initial legal)
    (ordered_environment_refines plan deadlineOf)
    players environment schedule execution next hstate hnext

/-- Every completed ordered policy run from generated initialization has the
public outcome of an actual written-order source execution. No successful-run
or progress assumption is hidden in the initialization. -/
theorem ordered_runPolicies_source_public_outcome (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (players : P → (plan.image deadlineOf).orderedApplication.PlayerPolicy)
    (environment : (plan.image deadlineOf).orderedApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation P))
    (next : (plan.image deadlineOf).orderedApplication.PolicyExecution)
    (hnext : next ∈ ((plan.image deadlineOf).orderedApplication.runPolicies
      players environment schedule
      (MessageApplication.PolicyExecution.initial (plan.image deadlineOf).orderedApplication
        (MessageApplication.State.initial (plan.image deadlineOf).orderedApplication
          (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial (compile source.core).graph))))).support)
    (hfinished : next.native.application.memory.finished (compile source.core).graph.nodeCount =
      true) :
    ∃ terminalEnv : VEnv L (compile source.core).terminalCtx,
      SmallStep.Star
        { ctx := source.core.Γ, env := source.core.env, cont := source.core.prog }
        { ctx := (compile source.core).terminalCtx, env := terminalEnv,
          cont := .ret (compile source.core).sourcePayoffs } ∧
      (compile source.core).readPublicTerminal? next.native.application.memory =
        some terminalEnv.erasePubEnv := by
  obtain ⟨cfg, hrefines⟩ := plan.ordered_runPolicies_refines deadlineOf
    source.core.env source.legal players environment schedule _ next
    ⟨_, ApplicationImage.State.initial_refines (compile source.core).graph⟩ hnext
  exact source_public_outcome_of_refines source.core next.native.application cfg hrefines hfinished

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.ordered_runPolicies_refines' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ordered_runPolicies_refines

/-- info: 'Vegas.ApplicationPlan.ordered_runPolicies_source_public_outcome' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ordered_runPolicies_source_public_outcome
