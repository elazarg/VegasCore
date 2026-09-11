/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryBindingCheckpoint
import VegasTests.WindowedDeliveryCheckpoint

/-! # Complete delivery binding checkpoint regression

The first binding of the checked persistent-disclosure program advances through
an actual delivery block. Player zero may use an arbitrary randomized raw
replacement, while unchanged player one supplies the relay that makes the
block unconditional.
-/

noncomputable section

namespace VegasTests.WindowedDeliveryBindingCheckpoint

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.PersistentDisclosure VegasTests.GeneratedPersistentDisclosure
open VegasTests.WindowedSourceCoverage VegasTests.WindowedDeliveryCheckpoint

private def bindingContinuation :=
  match applicationPlan with
  | .binding _ next => next

/-- Every supported complete delivery block produces the real source step and
the next delivery-service checkpoint, without assuming final inactivity or any
other runtime-success premise. -/
theorem binding_block_source_successor
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies
      (service.players (applicationPlan.liftProfile (fun _ => 10) profile) 0 replacement)
      (runtime.deliveryBlockEnvironment [0, 1] [1])
      (WindowedApplication.deliveryBlockInvocations [0, 1] [1]) initial).support) :
    ∃ (chosen : Bool)
      (sourceNext : CoupledAt (compileCore source.prog source.fresh compilerInitial).graph
        (compilerInitial.addCommitEvent 0 0 (.constBool true) source.fresh.1).1),
      sourceNext.current.source = source.env.cons chosen ∧
      ApplicationPlan.WindowedCheckpoint applicationPlan profile (fun _ => 10)
        bindingSelector choiceSelector (fun _ => 10) service 0 replacement 1
        bindingContinuation profile.afterCommit sourceNext final ∧
      chosen = (bindingFallback.bindingTimeoutCode source.fresh compilerInitial 10).resolvedValue
        (simpleExpr.eval bindingFallback.expr source.env.erasePubEnv)
          final.native.application.base := by
  let checkpoint := initial_checkpoint profile replacement
  obtain ⟨chosen, sourceNext, hsource, hcheckpoint, hchosen, _⟩ :=
    checkpoint.delivery_binding_block _ _ profile bindingFallback 10 rfl
    (compiledInitialCoupled source) initial final (by decide) 1 (by simp)
    (checkpoint.referenceOwner_of_ne 1 (by decide)).policy hfinal
  exact ⟨chosen, sourceNext, hsource, hcheckpoint, hchosen⟩

/-- The same successor is forced when recipient player one is the arbitrary
replacement and polls after receiving the unchanged relay's pending message. -/
theorem binding_block_recipient_replacement_source_successor
    (profile : SourceBehavioralProfile source.prog)
    (replacement : runtime.application.PlayerPolicy)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies
      (service.players (applicationPlan.liftProfile (fun _ => 10) profile) 1 replacement)
      (runtime.deliveryBlockEnvironment [0, 1] [1])
      (WindowedApplication.deliveryBlockInvocations [0, 1] [1]) initial).support) :
    ∃ (chosen : Bool)
      (sourceNext : CoupledAt (compileCore source.prog source.fresh compilerInitial).graph
        (compilerInitial.addCommitEvent 0 0 (.constBool true) source.fresh.1).1),
      sourceNext.current.source = source.env.cons chosen ∧
      ApplicationPlan.WindowedCheckpoint applicationPlan profile (fun _ => 10)
        bindingSelector choiceSelector (fun _ => 10) service 1 replacement 1
        bindingContinuation profile.afterCommit sourceNext final ∧
      chosen = (bindingFallback.bindingTimeoutCode source.fresh compilerInitial 10).resolvedValue
        (simpleExpr.eval bindingFallback.expr source.env.erasePubEnv)
          final.native.application.base := by
  let checkpoint := ApplicationPlan.WindowedCheckpoint.initial
    DisclosureAccounting.persistentChecked applicationPlan profile (fun _ => 10)
      bindingSelector choiceSelector (fun _ => 10) service 1 replacement
  obtain ⟨chosen, sourceNext, hsource, hcheckpoint, hchosen, _⟩ :=
    checkpoint.delivery_binding_block _ _ profile bindingFallback 10 rfl
      (compiledInitialCoupled source) initial final (by decide) 0 (by simp)
      (checkpoint.referenceOwner_of_ne 0 (by decide)).policy hfinal
  exact ⟨chosen, sourceNext, hsource, hcheckpoint, hchosen⟩

end VegasTests.WindowedDeliveryBindingCheckpoint

/-- info: 'VegasTests.WindowedDeliveryBindingCheckpoint.binding_block_source_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliveryBindingCheckpoint.binding_block_source_successor

/-- info:
'VegasTests.WindowedDeliveryBindingCheckpoint.binding_block_recipient_replacement_source_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedDeliveryBindingCheckpoint.binding_block_recipient_replacement_source_successor
