/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationForwardLaw
import Vegas.Compile.ApplicationPolicyTimeouts
import Interaction.MessageApplicationHandlerExtension

/-! # Reference execution with optional public-choice timeouts

Enabling extra handler code leaves the reference execution law unchanged when
the reference players never submit its new request. This compares complete
executions of the same public-message interpreter, including message pools,
receipts, command histories, and native traces. Arbitrary other strategies may
use expiry, so it is not a deviation-preservation theorem.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- The full execution law is identical for policies that never submit the
new expiry request and start without retained expiry traffic. Delivery, replay,
clock advancement, and other environment decisions are unrestricted. -/
theorem runPolicies_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicChoiceTimeout L code.guard.ty))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hsubmit : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireChoice address) ∉
        (players who (execution.principalHistory who)
          (State.observe image.application execution.native who)).support)
    (schedule : List (@Invocation P)) (execution : image.application.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies (fun message => message.payload.NotChoiceExpiry)) :
    (image.withChoiceTimeouts select).application.runPolicies players environment schedule
        execution = image.application.runPolicies players environment schedule execution := by
  have hsubmitSafe : ∀ (current : image.application.PolicyExecution) (who : P)
      (payload : Payload P L),
      .submit payload ∈ (players who (current.principalHistory who)
        (State.observe image.application current.native who)).support →
        ∀ serial, (⟨(who, serial), payload⟩ : Message P (Payload P L)).payload.NotChoiceExpiry := by
    intro current who payload hsupported serial
    cases payload with
    | expireChoice address => exact False.elim (hsubmit current who address hsupported)
    | _ => trivial
  have hlaw := image.application.runPolicies_eq_of_handler_agrees
    (image.withChoiceTimeouts select).handle
    (fun message => message.payload.NotChoiceExpiry)
    (fun state message hmessage => image.handle_withChoiceTimeouts select state message hmessage)
    players environment hsubmitSafe schedule execution hsafe
  have hsample : (image.withChoiceTimeouts select).sample = image.sample := by
    funext state address
    exact image.sample_withChoiceTimeouts select state address
  simp only [application, MessageApplication.withHandler] at hlaw ⊢
  rw [hsample]
  exact hlaw

end ApplicationImage

namespace ApplicationPlan

/-- The independently interpreted source public-outcome law holds with any
optional public-choice timeout code enabled, for the original lifted profile
under its generated serial reference service. No timeout request is generated
in this reference run; arbitrary deviations remain outside this law. -/
theorem timeout_service_source_public_law (source : WFProgram P L)
    (plan : ApplicationPlan source.accounted source.core.fresh
      (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)))
    (deadlineOf : Nat → Nat)
    (select : (code : PublicChoiceCode P L) → Option (PublicChoiceTimeout L code.guard.ty))
    (profile : SourceBehavioralProfile source.core.prog)
    (hinitial : plan.InitialControllerReadsPublic)
    (horigins : (plan.image deadlineOf).HasBindingOrigins) :
    (((plan.image deadlineOf).withChoiceTimeouts select).application.runPolicies
      (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
      (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)).map
        (fun out => (out.native.application.memory.finished (compile source.core).graph.nodeCount,
          (compile source.core).readPublicTerminal? out.native.application.memory)) =
      (denoteSource source.core.prog profile source.core.env).map fun terminal =>
        (true, some (cast (congrArg (VEnv L)
          (compileCore_terminalCtx_eq_sourceTerminalCtx source.core.prog source.core.fresh
            (BuildState.fromInitial
              (initialState source.core.Γ source.core.env source.core.wctx))).symm)
            terminal).erasePubEnv) := by
  rw [(plan.image deadlineOf).runPolicies_withChoiceTimeouts select
    (plan.liftProfile deadlineOf profile) (plan.image deadlineOf).serialService
    (fun execution who address => plan.liftProfileIn_not_expireChoice_supported
      (plan.image deadlineOf) deadlineOf profile who (execution.principalHistory who)
      (State.observe (plan.image deadlineOf).application execution.native who) address)
    (plan.image deadlineOf).serviceInvocations (plan.initialExecution deadlineOf)
    MessagePool.Satisfies.empty]
  exact plan.service_source_public_law source deadlineOf profile hinitial horigins

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationPlan.timeout_service_source_public_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.timeout_service_source_public_law
