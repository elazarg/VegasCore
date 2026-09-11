/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedDeliverySample
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
source successor corresponding to its actual draw. -/
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
            final.native.application.base.Refines next.current.graph.1 := by
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

/-- Every supported completed delivery sample block identifies an actual
source draw and a source-coupled successor refined by the final public state. -/
theorem delivery_sample_block_successor_refines
    (nextPlan : ApplicationPlan accounted fresh.2 (state.addSampleEvent name dist fresh.1).1)
    (profile : SourceBehavioralProfile (.sample name dist tail))
    (current : CoupledAt (compileCore (.sample name dist tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      who replacement blockIndex (.sample (fresh := fresh) nextPlan) profile current execution)
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
      final.native.application.base.Refines next.current.graph.1 := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) who replacement
  let before := roster.flatMap (fun actor => [.player actor, .player actor]) ++
    recipients.map (fun _ => Invocation.environment) ++ roster.map Invocation.player
  let suffix := Invocation.environment ::
    roster.flatMap (fun actor => [.player actor, .environment])
  have hlaw := delivery_sample_block nextPlan profile current execution checkpoint
  change final ∈ (runtime.application.runPolicies players service.environment
    service.invocations execution).support at hfinal
  rw [hlaw.1] at hfinal
  simp only [FinDist.support_bind, Set.mem_iUnion] at hfinal
  obtain ⟨middle, hmiddle, value, hvalue, hsuffix⟩ := hfinal
  obtain ⟨next, hsource, hrefines⟩ := hlaw.2 middle hmiddle value hvalue
  exact ⟨value, next, hvalue, hsource, hrefines final hsuffix⟩

end Vegas.ApplicationPlan.WindowedCheckpoint
