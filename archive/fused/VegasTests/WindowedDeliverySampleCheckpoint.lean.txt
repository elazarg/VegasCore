/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliverySampleCheckpoint
import VegasTests.WindowedSamplePrivacy

/-! # Delivery-service sample checkpoint regression

The standalone checked coin-flip fixture instantiates the complete
delivery-service sample successor with an unrestricted focal player policy.
-/

noncomputable section

namespace VegasTests.WindowedDeliverySampleCheckpoint

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage
open VegasTests.WindowedSamplePrivacy

def deliveryService : runtime.Service := runtime.deliveryService [0, 1] [0, 1]

/-- Every supported complete delivery block from the initialized sample
checkpoint produces the corresponding source step and the initialized
continuation checkpoint. The focal command is otherwise arbitrary. -/
theorem initialized_delivery_sample_successor
    (profile : SourceBehavioralProfile sampleCore)
    (replacement : runtime.application.PlayerPolicy)
    (final : runtime.application.PolicyExecution)
    (hfinal : final ∈ (runtime.application.runPolicies
      (deliveryService.players (plan.liftProfile deadlineOf profile) 0 replacement)
      deliveryService.environment deliveryService.invocations initial).support) :
    ∃ (value : Bool)
      (next : CoupledAt (compileCore sampleCore sampleFresh sampleState).graph nextState),
      value ∈ fairCoin.denote.support ∧
      next.current.source =
        (compiledInitialCoupled WindowedSamplePrivacy.source).current.source.cons value ∧
      ApplicationPlan.WindowedCheckpoint plan profile deadlineOf noBinding noChoice windowOf
        deliveryService 0 replacement 1 nextPlan profile.afterSample next final ∧
      SmallStep
        ⟨[], (compiledInitialCoupled WindowedSamplePrivacy.source).current.source, sampleCore⟩
        ⟨[(0, .pub .bool)], next.current.source, .ret []⟩ := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial WindowedSamplePrivacy.checked
    plan profile deadlineOf
    noBinding noChoice windowOf deliveryService 0 replacement
  exact ApplicationPlan.WindowedCheckpoint.delivery_sample_block_successor nextPlan profile
    (compiledInitialCoupled WindowedSamplePrivacy.source) initial final checkpoint
      (by decide) hfinal

/-- Any continuation depending only on the initialized successor checkpoint
factors through the fair-coin source environment, even for a randomized raw
replacement policy. -/
theorem initialized_delivery_sample_bind
    (profile : SourceBehavioralProfile sampleCore)
    (replacement : runtime.application.PlayerPolicy)
    {Omega : Type*}
    (after : runtime.application.PolicyExecution → FinDist Omega)
    (sourceAfter : VEnv simpleExpr [(0, .pub .bool)] → FinDist Omega)
    (hafter : ∀ next native,
      ApplicationPlan.WindowedCheckpoint plan profile deadlineOf noBinding noChoice windowOf
        deliveryService 0 replacement 1 nextPlan profile.afterSample next native →
      after native = sourceAfter next.current.source) :
    ((runtime.application.runPolicies
      (deliveryService.players (plan.liftProfile deadlineOf profile) 0 replacement)
      deliveryService.environment deliveryService.invocations initial).bind after) =
      fairCoin.denote.bind (fun value => sourceAfter
        ((compiledInitialCoupled WindowedSamplePrivacy.source).current.source.cons value)) := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial WindowedSamplePrivacy.checked
    plan profile deadlineOf
    noBinding noChoice windowOf deliveryService 0 replacement
  exact ApplicationPlan.WindowedCheckpoint.delivery_sample_bind nextPlan profile
    (compiledInitialCoupled WindowedSamplePrivacy.source) initial checkpoint (by decide)
      after sourceAfter hafter

/-- The complete checked coin-flip program terminates with exactly its source
public-result law under every randomized raw replacement. Both players are
polled, including the reaction turn; no continuation-law premise is assumed. -/
theorem initialized_delivery_sample_public_law
    (profile : SourceBehavioralProfile sampleCore)
    (replacement : runtime.application.PlayerPolicy) :
    ((runtime.application.runPolicies
      (deliveryService.players (plan.liftProfile deadlineOf profile) 0 replacement)
      deliveryService.environment deliveryService.invocations initial).map fun out =>
        (out.native.application.base.memory.finished
          (compileCore sampleCore sampleFresh sampleState).graph.nodeCount,
          (compileCore sampleCore sampleFresh sampleState).readPublicTerminal?
            out.native.application.base.memory)) =
      fairCoin.denote.map (fun value =>
        (true, some (((compiledInitialCoupled WindowedSamplePrivacy.source).current.source.cons
          (L := simpleExpr) (x := 0) (τ := .pub .bool) value).erasePubEnv))) := by
  simp only [FinDist.map_eq_bind]
  apply initialized_delivery_sample_bind profile replacement _
    (fun env => FinDist.pure (true, some env.erasePubEnv))
  intro next native checkpoint
  exact congrArg FinDist.pure (Prod.ext
    (next.finished_public_readout (compileCore sampleCore sampleFresh sampleState)
      native.native.application.base checkpoint.refines).1
    (next.finished_public_readout (compileCore sampleCore sampleFresh sampleState)
      native.native.application.base checkpoint.refines).2)

end VegasTests.WindowedDeliverySampleCheckpoint

/-- info: 'VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_successor

/-- info: 'VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_bind

/-- info: 'VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_public_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedDeliverySampleCheckpoint.initialized_delivery_sample_public_law
