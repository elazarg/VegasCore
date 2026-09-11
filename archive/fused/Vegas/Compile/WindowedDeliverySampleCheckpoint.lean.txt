/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedDeliverySample
import Vegas.Compile.WindowedDeliverySampleCaches
import Vegas.Compile.WindowedService

/-! # Source chance at delivery-service checkpoints -/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster recipients : List P} {who : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {dist : L.DistExpr (erasePubVCtx Γ) ty}
variable {tail : VegasCore P L ((name, .pub ty) :: Γ)}
variable {accounted : CommitmentAccounting pending tail}
variable {fresh : FreshBindings (.sample name dist tail)} {state : BuildState P L Γ}

/-- The actual delivery-service block at a source sample checkpoint has the
source chance kernel exactly. Every supported completed suffix refines the
source successor corresponding to its actual draw, with a fresh activation
window for the next instruction. -/
theorem delivery_sample_block
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let service := runtime.deliveryService roster recipients
    let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
    let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
      recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
    let suffix := Invocation.environment ::
      roster.flatMap (fun actor => [.player actor, .environment])
    (runtime.application.runPolicies players service.environment service.invocations execution =
      (runtime.application.runPolicies players service.environment before execution).bind
        fun middle => (L.evalDist dist current.current.source.eraseSampleEnv).bind fun value =>
          runtime.application.runPolicies players service.environment suffix
            (runtime.sampleExecution middle (headSampleCode fresh state) value)) ∧
    ∀ middle ∈ (runtime.application.runPolicies players service.environment before
        execution).support,
      ∀ value, value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support →
        ∃ next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
            (state.addSampleEvent name dist fresh.1).1,
          next.current.source = current.current.source.cons value ∧
          ∀ final, final ∈ (runtime.application.runPolicies players service.environment suffix
              (runtime.sampleExecution middle (headSampleCode fresh state) value)).support →
            final.native.application.base.Refines next.current.graph.1 ∧
              final.native.application.FreshActivation := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
  let code := headSampleCode fresh state
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.sample code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.sample code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup state.nodes.length = some (.sample code)
    at hlookupOriginal
  have hlookup : runtime.image.lookup state.nodes.length = some (.sample code) := by
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hlength : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2) := by
    have hrun := runtime.application.runPolicies_environmentHistory_length players
      service.environment
      (List.replicate blockIndex service.invocations).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
      checkpoint.reached
    simpa only [runtime, service, players, WindowedApplication.deliveryService,
      windowedInitialExecution, PolicyExecution.initial, List.length_nil, Nat.zero_add,
      WindowedApplication.repeatedDeliveryBlockInvocations_environment_count] using hrun
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some (.sample code) := by
    have hquotient : execution.environmentHistory.length /
        (recipients.length + roster.length + 2) = blockIndex := by
      rw [hlength, Nat.mul_div_cancel]
      omega
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have hactive := checkpoint.activeAddress?_head (.sample code) _ hhead
  simpa only [runtime, service, players, WindowedApplication.deliveryService] using
    runtime.runPolicies_full_delivery_block_sample_source_coupling roster recipients dist tail
      fresh state current players execution hlookup hindex
      (by rw [hlength]; exact Nat.mul_mod_left _ _) hactive checkpoint.refines
      checkpoint.consistent

/-- A completed delivery sample block retains initialized reachability, future
unchanged-player caches, and the activation window at its source successor. -/
theorem delivery_sample_successor
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    (next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
      (state.addSampleEvent name dist fresh.1).1)
    (final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.players (root.liftProfile deadlineOf rootProfile) who replacement)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.environment)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.invocations) execution).support)
    (hrefines : final.native.application.base.Refines next.current.graph.1)
    (hactivation : final.native.application.FreshActivation) :
    WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement (blockIndex + 1) nextPlan profile.afterSample next final := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
  let code := headSampleCode fresh state
  have hhead : (ApplicationPlan.sample (fresh := fresh) nextPlan).instructions deadlineOf =
      .sample code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.sample code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.sample code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup state.nodes.length = some (.sample code)
    at hlookupOriginal
  have hlookup : runtime.image.lookup code.node = some (.sample code) := by
    change runtime.image.lookup state.nodes.length = some (.sample code)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts, ApplicationInstruction.withChoiceTimeouts]
  have hindex : runtime.image.instructions[blockIndex]? = some (.sample code) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  refine ⟨.sample checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hactivation⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · have hfresh : RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan who
        (runtime.eraseExecution execution) :=
      (List.forall_cons _ _ _).mp checkpoint.unchangedCaches |>.2
    exact runPolicies_full_delivery_sample_block_preserves_unchangedCaches runtime
      (root.image deadlineOf) deadlineOf nextPlan roster recipients hroster who
      (fun actor => runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor))
      players
      (fun actor hactor => by
        simp only [players, WindowedApplication.Service.players, Function.update_of_ne hactor,
          WindowedApplication.Service.referencePlayers, service,
          WindowedApplication.deliveryService])
      blockIndex code execution final hlookup hindex
      (fun actor hactor => (runtime.runPolicies_repeatedDeliveryBlocks_history_alignment
        roster recipients hroster actor hactor players service.environment blockIndex _
        execution checkpoint.reached).1) hfresh hfinal

/-- Every supported complete delivery sample block identifies its actual
source draw, source step, and complete successor checkpoint. The focal policy
may submit or register arbitrary commands at every scheduled focal invocation,
including reaction slots. -/
theorem delivery_sample_block_successor
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.players (root.liftProfile deadlineOf rootProfile) who replacement)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.environment)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.invocations) execution).support) :
    ∃ (value : L.Val ty)
      (next : CoupledAt (compileCore (.sample name dist tail) fresh state).graph
        (state.addSampleEvent name dist fresh.1).1),
      value ∈ (L.evalDist dist current.current.source.eraseSampleEnv).support ∧
      next.current.source = current.current.source.cons value ∧
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
        ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        who replacement (blockIndex + 1) nextPlan profile.afterSample next final ∧
      SmallStep ⟨Γ, current.current.source, .sample name dist tail⟩
        ⟨(name, .pub ty) :: Γ, next.current.source, tail⟩ := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
  let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
    recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [.player actor, .environment])
  have hlaw := delivery_sample_block nextPlan profile current execution checkpoint
  have hwhole := hfinal
  change final ∈ (runtime.application.runPolicies players service.environment
    service.invocations execution).support at hfinal
  rw [hlaw.1] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨middle, hmiddle, value, hvalue, hsuffix⟩ := hfinal
  obtain ⟨next, hsource, hrefines⟩ := hlaw.2 middle hmiddle value hvalue
  refine ⟨value, next, hvalue, hsource,
    delivery_sample_successor nextPlan profile current execution checkpoint hroster next final
      hwhole (hrefines final hsuffix).1 (hrefines final hsuffix).2, ?_⟩
  rw [hsource]
  exact .sample dist tail value hvalue

/-- Source chance composes with any continuation that agrees at genuine
delivery successor checkpoints. Traffic through the delivery and reaction
slots is marginalized in the exact law; the successor invariants are
derived from the block rather than required as extra hypotheses. -/
theorem delivery_sample_bind
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
    (hroster : roster.Nodup)
    {Ω : Type*}
    (after : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution →
      FinDist Ω)
    (sourceAfter : VEnv L ((name, .pub ty) :: Γ) → FinDist Ω)
    (hafter : ∀ next native,
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
        ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        who replacement (blockIndex + 1) nextPlan profile.afterSample next native →
        after native = sourceAfter next.current.source) :
    (((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.players (root.liftProfile deadlineOf rootProfile) who replacement)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.environment)
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.invocations) execution).bind after) =
      (L.evalDist dist current.current.source.eraseSampleEnv).bind
        (fun value => sourceAfter (current.current.source.cons value)) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
  let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
    recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [.player actor, .environment])
  obtain ⟨hrun, hcoupling⟩ := delivery_sample_block nextPlan profile current execution checkpoint
  rw [hrun, FinDist.bind_bind]
  calc
    _ = (runtime.application.runPolicies players service.environment before execution).bind
        (fun _ => (L.evalDist dist current.current.source.eraseSampleEnv).bind
          (fun value => sourceAfter (current.current.source.cons value))) := by
      apply FinDist.bind_congr
      intro middle hmiddle
      rw [FinDist.bind_bind]
      apply FinDist.bind_congr
      intro value hvalue
      obtain ⟨next, hsource, hrefines⟩ := hcoupling middle hmiddle value hvalue
      calc
        _ = (runtime.application.runPolicies players service.environment suffix
            (runtime.sampleExecution middle (headSampleCode fresh state) value)).bind
              (fun _ => sourceAfter (current.current.source.cons value)) := by
          apply FinDist.bind_congr
          intro final hfinal
          have hwhole : final ∈ (runtime.application.runPolicies players service.environment
              service.invocations execution).support := by
            apply (congrArg (fun law => final ∈ law.support) hrun).mpr
            simp only [FinDist.support_bind, Set.mem_iUnion]
            exact ⟨middle, hmiddle, value, hvalue, hfinal⟩
          have hnext := delivery_sample_successor nextPlan profile current execution checkpoint
            hroster next final hwhole (hrefines final hfinal).1 (hrefines final hfinal).2
          rw [hafter next final hnext, hsource]
        _ = _ := FinDist.bind_const _ _
    _ = _ := FinDist.bind_const _ _

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_sample_block_successor'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_sample_block_successor

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_sample_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_sample_bind
