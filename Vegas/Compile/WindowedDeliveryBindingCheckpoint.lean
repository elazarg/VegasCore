/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedDeliveryBinding
import Vegas.Compile.WindowedDeliveryCaches
import Vegas.Compile.WindowedDeliverySettlement

/-! # Delivery-service binding successors at source checkpoints -/

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
variable {windowOf : Nat → Nat} {roster recipients : List P} {focal : P}
variable {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name : VarId} {owner : P} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {fresh : FreshBindings (.commit name owner guard tail)}
variable {state : BuildState P L Γ} {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}

/-- Once a complete delivery block has made its binding head inactive, its
actual disposition determines a legal source successor and a fully initialized
delivery-service checkpoint. No final refinement or activation invariant is
assumed. -/
theorem delivery_binding_block_of_inactive
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hroster : roster.Nodup)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
          |>.players (root.liftProfile deadlineOf rootProfile) focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).deliveryBlockEnvironment
          roster recipients)
        (WindowedApplication.deliveryBlockInvocations roster recipients) execution).support)
    (hinactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      final.native.application.base.memory ≠ some state.nodes.length) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
        ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        focal replacement (blockIndex + 1) nextPlan profile.afterCommit sourceNext final ∧
      chosen = (fallback.bindingTimeoutCode fresh state deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv) final.native.application.base ∧
      SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
        ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed := fallback.bindingTimeoutCode fresh state deadline
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.bind code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.node = some (.bind code) at hlookupOriginal
  have hlookup : runtime.image.lookup timed.node = some (.bind timed) := by
    change runtime.image.lookup code.node = some (.bind timed)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hlookupOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts, hselect]
    rfl
  have hlength : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2) := by
    have hrun := runtime.application.runPolicies_environmentHistory_length players
      service.environment (List.replicate blockIndex service.invocations).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
      checkpoint.reached
    simpa only [windowedInitialExecution, PolicyExecution.initial, List.length_nil,
      Nat.zero_add, service, WindowedApplication.deliveryService,
      WindowedApplication.repeatedDeliveryBlockInvocations_environment_count] using hrun
  have hquotient : execution.environmentHistory.length /
      (recipients.length + roster.length + 2) = blockIndex := by
    rw [hlength, Nat.mul_div_cancel]
    omega
  have hindex : runtime.image.instructions[execution.environmentHistory.length /
      (recipients.length + roster.length + 2)]? = some (.bind timed) := by
    simp only [hquotient, runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hselect]
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (WindowedApplication.deliveryBlockInvocations roster recipients).countP
          Invocation.isEnvironment →
      runtime.image.instructions[index / (recipients.length + roster.length + 2)]? =
        some (.bind timed) := by
    intro index hlo hhi
    have hcount := WindowedApplication.deliveryBlockInvocations_environment_count
      roster recipients
    rw [hcount] at hhi
    have hsame : index / (recipients.length + roster.length + 2) =
        execution.environmentHistory.length / (recipients.length + roster.length + 2) := by
      have hmod : execution.environmentHistory.length %
          (recipients.length + roster.length + 2) = 0 := by
        rw [hlength]
        exact Nat.mul_mod_left _ _
      have hbase := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hmod)
      apply Nat.div_eq_of_lt_le
      · rw [hbase]
        exact hlo
      · rw [Nat.add_mul, hbase]
        omega
    rw [hsame]
    exact hindex
  have hactive := checkpoint.activeAddress?_head (.bind code) _ hhead
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock (.bind code) _ hhead
  obtain ⟨chosen, sourceNext, hsource, hrefines, hfresh, hchosen⟩ :=
    runtime.runPolicies_delivery_binding_source_coupling roster recipients players
      (WindowedApplication.deliveryBlockInvocations roster recipients) guard tail fallback fresh
      state current unrestricted deadline execution final activation hindexRange hlookup hactive
      hactivation hkey checkpoint.refines hinactive hfinal
  have hstep : SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
      ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ := by
    rw [hsource]
    exact .commit guard tail chosen (unrestricted current.current.source chosen)
  refine ⟨chosen, sourceNext, hsource, ?_, hchosen, hstep⟩
  refine ⟨.binding checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · exact delivery_block_caches
      (.binding (newName := newName) (fresh := fresh) unrestricted nextPlan) nextPlan profile
      deadlineOf _ hhead binding choice windowOf roster recipients hroster focal replacement
      blockIndex current execution final checkpoint hfinal

/-- A complete delivery-service binding block always reaches the source
successor when one duplicate-free roster member uses the unchanged relay
policy. The focal replacement remains an arbitrary raw policy. -/
theorem delivery_binding_block
    (unrestricted : UnrestrictedBinding guard)
    (nextPlan : ApplicationPlan accounted fresh.2
      (state.addCommitEvent name owner guard fresh.1).1)
    (profile : SourceBehavioralProfile (.commit name owner guard tail))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (deadline : Nat)
    (hselect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨deadline, fallback.compiled fresh state⟩)
    (current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile current execution)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster)
    (hreference :
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.players (root.liftProfile deadlineOf rootProfile) focal replacement) relay =
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.referencePlayers (root.liftProfile deadlineOf rootProfile)) relay)
    (hfinal : final ∈ ((root.windowed deadlineOf binding choice windowOf).application
      |>.runPolicies
        (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
          |>.players (root.liftProfile deadlineOf rootProfile) focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).deliveryBlockEnvironment
          roster recipients)
        (WindowedApplication.deliveryBlockInvocations roster recipients) execution).support) :
    ∃ (chosen : L.Val ty)
      (sourceNext : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph
        (state.addCommitEvent name owner guard fresh.1).1),
      sourceNext.current.source = current.current.source.cons chosen ∧
      WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
        ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        focal replacement (blockIndex + 1) nextPlan profile.afterCommit sourceNext final ∧
      chosen = (fallback.bindingTimeoutCode fresh state deadline).resolvedValue
        (L.eval fallback.expr current.current.source.erasePubEnv) final.native.application.base ∧
      SmallStep ⟨Γ, current.current.source, .commit name owner guard tail⟩
        ⟨(name, .sealed owner ty) :: Γ, sourceNext.current.source, tail⟩ := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed := fallback.bindingTimeoutCode fresh state deadline
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted nextPlan).instructions deadlineOf =
        .bind code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.bind code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.node = some (.bind code) at hlookupOriginal
  have hlookup : runtime.image.lookup timed.node = some (.bind timed) := by
    change runtime.image.lookup code.node = some (.bind timed)
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hlookupOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts, hselect]
    rfl
  have hindex : runtime.image.instructions[blockIndex]? = some (.bind timed) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, timed,
      SourceDecisionSite.PublicFallback.bindingTimeoutCode]
    rw [hselect]
  have henvironment : execution.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2) := by
    have hrun := runtime.application.runPolicies_environmentHistory_length players
      service.environment (List.replicate blockIndex service.invocations).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
      checkpoint.reached
    simpa only [windowedInitialExecution, PolicyExecution.initial, List.length_nil,
      Nat.zero_add, service, WindowedApplication.deliveryService,
      WindowedApplication.repeatedDeliveryBlockInvocations_environment_count] using hrun
  have hprincipal : (execution.principalHistory relay).length = 4 * blockIndex := by
    have hrun := runtime.application.runPolicies_principalHistory_length relay players
      service.environment (List.replicate blockIndex service.invocations).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) execution
      checkpoint.reached
    have hcount := WindowedApplication.repeatedDeliveryBlockInvocations_player_count
      roster recipients hroster relay hrelay blockIndex
    rw [hrun]
    simp only [windowedInitialExecution, PolicyExecution.initial, List.length_nil,
      Nat.zero_add, service, WindowedApplication.deliveryService]
    exact hcount
  have hactive := checkpoint.activeAddress?_head (.bind code) _ hhead
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock (.bind code) _ hhead
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
  have hsettled : runtime.image.activeAddress? final.native.application.base.memory ≠
      some timed.node := by
    subst roster
    apply runtime.runPolicies_delivery_block_resolves beforeRoster afterRoster recipients relay
      owner hroster players
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) hreference
      (.bind timed) rfl current.current.graph.1 blockIndex execution final activation
      henvironment hprincipal hindex hactive hactivation hkey checkpoint.refines
      checkpoint.activationFresh checkpoint.consistent checkpoint.serialsBeforeNext
    · intro observed hobservedConsistent hobservedRefines hobservedActivation hoverdue
        hobservedSerial
      have hobservedCode : runtime.image.lookup activation.key = some (.bind timed) := by
        rw [hkey]
        exact hlookup
      obtain ⟨payload, resolved, hdue, _, hhandle, _⟩ :=
        runtime.binding_source_relay_eligibility guard tail fallback fresh state deadline current
          observed activation relay hobservedConsistent hobservedActivation hobservedCode
          hobservedRefines (by
            have htimedNode : timed.node = code.node := rfl
            change activation.since + runtime.windowOf activation.key <
              observed.native.application.base.memory.clock
            rw [hkey]
            simpa only [ApplicationInstruction.address, htimedNode] using hoverdue)
          hobservedSerial
      exact ⟨payload, resolved, hdue, hhandle⟩
    · exact hfinal
  exact delivery_binding_block_of_inactive unrestricted nextPlan profile fallback deadline hselect
    current execution final checkpoint hroster hfinal hsettled

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_block_of_inactive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_block_of_inactive

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_block' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_block
