/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.ApplicationDeadlinePolicies
import Vegas.Compile.ApplicationTimeoutForwardLaw
import Vegas.Compile.WindowedPolicyProjection
import Vegas.Compile.WindowedSourceSafety

/-! # Source law of the activation-relative reference execution -/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- The compiler-constructed windowed runtime has the original source law under
the observation-erased reference profile and serial service, for every window
policy. This does not restrict window-aware runtime strategies. -/
theorem windowed_service_source_public_law (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    let runtime := plan.windowed deadlineOf binding choice windowOf
    let players := plan.liftProfile deadlineOf profile
    let environment := (plan.image deadlineOf).serialService
    let execution := PolicyExecution.initial runtime.application
      (MessageApplication.State.initial runtime.application
        (runtime.initial (ApplicationImage.State.initial
          (ApplicationImage.Memory.initial (compile source.core).graph))))
    (runtime.application.runPolicies
      (fun who => runtime.liftPlayerPolicy (players who))
      (runtime.liftEnvironmentPolicy environment)
      (plan.image deadlineOf).serviceInvocations execution).map (fun out =>
        (out.native.application.base.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  dsimp only
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let players := plan.liftProfile deadlineOf profile
  let environment := (plan.image deadlineOf).serialService
  let execution := PolicyExecution.initial runtime.application
    (MessageApplication.State.initial runtime.application
      (runtime.initial (ApplicationImage.State.initial
        (ApplicationImage.Memory.initial (compile source.core).graph))))
  have herase := runtime.runPolicies_erase players environment (by
    intro current who payload hsubmit
    exact plan.liftProfile_deadlineIndependent deadlineOf profile who
      (current.principalHistory who)
      (MessageApplication.State.observe (plan.image deadlineOf).application
        current.native who) payload hsubmit)
    (plan.image deadlineOf).serviceInvocations execution
    (runtime.initial_consistent _) MessagePool.Satisfies.empty
  let observeBase := fun out : runtime.image.orderedApplication.PolicyExecution =>
    (out.native.application.memory.finished (compile source.core).graph.nodeCount,
      (compile source.core).readPublicTerminal? out.native.application.memory)
  calc
    _ = ((runtime.application.runPolicies
        (fun who => runtime.liftPlayerPolicy (players who))
        (runtime.liftEnvironmentPolicy environment)
        (plan.image deadlineOf).serviceInvocations execution).map
          runtime.eraseExecution).map observeBase := by
      rw [FinDist.map_comp]
      rfl
    _ = (runtime.image.orderedApplication.runPolicies players environment
        (plan.image deadlineOf).serviceInvocations
        (runtime.eraseExecution execution)).map observeBase := by rw [herase]
    _ = _ := by
      change (((((plan.image deadlineOf).withBindingTimeouts binding).withChoiceTimeouts
        choice).orderedApplication.runPolicies players environment
        (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
          observeBase) = _
      exact plan.ordered_timeout_service_source_public_law source deadlineOf binding choice
        profile hinitial horigins

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.windowed_service_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.windowed_service_source_public_law
