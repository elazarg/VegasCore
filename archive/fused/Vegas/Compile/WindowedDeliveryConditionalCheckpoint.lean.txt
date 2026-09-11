/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedDeliveryConditional
import Vegas.Compile.WindowedDeliveryCaches
import Vegas.Compile.WindowedDeliverySettlement

/-! # Delivery-service conditional successors at source checkpoints -/

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
variable {blockIndex : Nat} {name publicName : VarId} {owner : P} {ty : L.Ty}
variable {newName : name ∉ pending}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L
  ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {spec : ConditionalOpening guard}
variable {unresolved : spec.source ∈ pending}
variable {fresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- A complete delivery block at a conditional head yields the legal optional
source result and the next delivery-service checkpoint. The unchanged relay
is the only progress witness; the focal replacement and all delivery choices
remain arbitrary. -/
theorem delivery_conditional_block_common
    {headPending : Finset VarId}
    {headAccounted : CommitmentAccounting headPending
      (.commit name owner guard (.reveal publicName owner name .here tail))}
    {nextPending : Finset VarId}
    {nextAccounted : CommitmentAccounting nextPending tail}
    (headPlan : ApplicationPlan headAccounted fresh state)
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan nextAccounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (hhead : headPlan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (nextContinuation : ProfileContinuation root rootProfile nextPlan
      profile.afterCommit.afterReveal)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh state).graph
      state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex
      headPlan profile current execution)
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
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
          ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
          focal replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
  let site := ConditionalPublicationSite.atHead name publicName owner guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let code := site.code fresh state sourceSlot deadline
  let instruction : ApplicationInstruction P L := .conditional code
  have hindexOriginal := checkpoint.instruction_at instruction _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some instruction := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf instruction
    (List.mem_of_getElem? hindexOriginal)
  have hlookup : runtime.image.lookup instruction.address = some instruction := by
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some,
      ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
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
  have hindexRange : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (WindowedApplication.deliveryBlockInvocations roster recipients).countP
          Invocation.isEnvironment →
      runtime.image.instructions[index / (recipients.length + roster.length + 2)]? =
        some instruction := by
    intro index hlo hhi
    have hcount := WindowedApplication.deliveryBlockInvocations_environment_count
      roster recipients
    have hhi' : index < execution.environmentHistory.length +
        (recipients.length + roster.length + 2) := by
      simpa only [hcount] using hhi
    have hsame : index / (recipients.length + roster.length + 2) = blockIndex := by
      rw [henvironment] at hlo hhi'
      have hwidth : 0 < recipients.length + roster.length + 2 := by omega
      apply Nat.div_eq_of_lt_le
      · exact hlo
      · simpa [Nat.add_mul, Nat.one_mul] using hhi'
    rw [hsame]
    exact hindex
  have hactive := checkpoint.activeAddress?_head instruction _ hhead
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock instruction _ hhead
  have hnodup : (runtime.image.instructions.flatMap
      ApplicationInstruction.coveredNodes).Nodup := by
    dsimp only [runtime, windowed]
    rw [ApplicationImage.coveredNodes_withChoiceTimeouts,
      ApplicationImage.coveredNodes_withBindingTimeouts]
    exact root.coveredNodes_nodup deadlineOf
  have hallocated : ∀ candidate ∈ runtime.image.instructions,
      candidate.AllocatedAt rootState.initialFields.length := by
    apply ApplicationImage.instructions_allocated_withChoiceTimeouts
    apply ApplicationImage.instructions_allocated_withBindingTimeouts
    exact root.instructions_allocated deadlineOf
  have hresolved := checkpoint.resolvedBindings
  have horiginsRuntime : runtime.image.HasBindingOrigins :=
    (horigins.withBindingTimeouts binding).withChoiceTimeouts choice
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
  have hsettled : runtime.image.activeAddress? final.native.application.base.memory ≠
      some instruction.address := by
    subst roster
    apply runtime.runPolicies_delivery_block_resolves beforeRoster afterRoster recipients relay
      owner hroster players
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile relay)) hreference
      instruction rfl current.current.graph.1 blockIndex execution final activation
      henvironment hprincipal hindex hlookup hactive hactivation hkey checkpoint.refines
      checkpoint.activationFresh checkpoint.consistent checkpoint.serialsBeforeNext
      rootState.initialFields.length hnodup hallocated hresolved
    · intro observed hobservedConsistent hobservedRefines hobservedActivation hoverdue
        hobservedSerial hobservedResolved hindexAt hlookupAt
      have hobservedCode : runtime.image.lookup activation.key = some instruction := by
        rw [hkey]
        exact hlookupAt
      have hoverdue' : activation.since + runtime.windowOf activation.key <
          observed.native.application.base.memory.clock := by
        rw [hkey]
        exact hoverdue
      obtain ⟨payload, resolved, hdue, hhandle⟩ :=
        runtime.conditional_expiry_eligible_at_state guard tail spec fresh state
          current sourceSlot deadline
          (recipients.length + (beforeRoster ++ relay :: afterRoster).length + 2)
          relay observed activation hindexAt hobservedCode hobservedConsistent
          hobservedActivation hoverdue' hobservedRefines hobservedResolved horiginsRuntime
      exact ⟨payload, resolved, hdue, hhandle⟩
    · exact hfinal
  obtain ⟨result, sourceNext, hresult, hlegal, hsource, hrefines, hfresh⟩ :=
    runtime.runPolicies_delivery_conditional_source_coupling roster recipients players
      (WindowedApplication.deliveryBlockInvocations roster recipients) guard tail spec fresh state
      current publicGuard sourceSlot deadline execution final activation hindexRange
      hlookup hactive hactivation hkey checkpoint.refines hsettled hfinal
  have hsteps := spec.commit_reveal_steps publicName tail current.current.source
    (spec.encoding.symm result) hlegal
  rw [← hsource] at hsteps
  refine ⟨result, sourceNext, hresult, hsource, hlegal, hsteps, ?_, hsettled⟩
  refine ⟨nextContinuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · exact delivery_block_caches
      headPlan nextPlan profile deadlineOf _ hhead binding choice windowOf
      roster recipients hroster focal replacement blockIndex current execution final checkpoint
      hfinal

/-- The ordinary conditional accounting constructor instantiates the common
delivery proof with its source-level continuation certificate. -/
theorem delivery_conditional_block
    {pending : Finset VarId} {unresolved : spec.source ∈ pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting (pending.erase spec.source) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh state).graph
      state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex
        (.conditional (unresolved := unresolved) (newName := newName)
          (fresh := fresh) publicGuard nextPlan) profile current execution)
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
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
          ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
          focal replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let plan := ApplicationPlan.conditional (newName := newName)
    (unresolved := unresolved) (fresh := fresh) publicGuard nextPlan
  have hhead : plan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf := rfl
  exact delivery_conditional_block_common plan publicGuard nextPlan hhead
    profile (.conditional checkpoint.continuation) horigins current execution final checkpoint
    hroster relay hrelay hreference hfinal

/-- The copied-conditional accounting constructor has the same delivery
semantics; only its source-accounting certificate and continuation constructor
are different. -/
theorem delivery_conditionalCopy_block
    {pending : Finset VarId} {unresolved : name ∈ insert name pending}
    {newName : name ∉ pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    (publicGuard : (ConditionalPublicationSite.atHead name publicName owner guard tail spec)
      |>.PubliclyValidatable fresh state)
    (nextPlan : ApplicationPlan accounted fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) fresh state).graph
      state)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex
        (.conditionalCopy (newName := newName) (unresolved := unresolved)
          (fresh := fresh) spec publicGuard nextPlan) profile current execution)
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
    ∃ (result : Option (L.Val spec.secretTy))
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) fresh state).graph
        (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
          publicName owner .here fresh.2.1).1),
      (result = none ∨ result = some (current.current.source.get spec.binding)) ∧
        sourceNext.current.source =
          (current.current.source.cons (spec.encoding.symm result)).cons
            (spec.encoding.symm result) ∧
        evalGuard guard (spec.encoding.symm result)
          ((current.current.source.toView owner).eraseEnv) = true ∧
        SmallStep.Star
          ⟨Γ, current.current.source,
            .commit name owner guard (.reveal publicName owner name .here tail)⟩
          ⟨(publicName, .pub ty) :: (name, .sealed owner ty) :: Γ,
            sourceNext.current.source, tail⟩ ∧
        WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
          ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
          focal replacement (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final ∧
        (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
          final.native.application.base.memory ≠
            some ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
              |>.choice.publicationNode fresh state) := by
  let plan := ApplicationPlan.conditionalCopy (newName := newName)
    (unresolved := unresolved) (fresh := fresh) spec publicGuard nextPlan
  have hhead : plan.instructions deadlineOf =
      .conditional ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
        |>.code fresh state
          ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.sourceField fresh state)
          (deadlineOf ((ConditionalPublicationSite.atHead name publicName owner guard tail spec)
            |>.choice.publicationNode fresh state))) :: nextPlan.instructions deadlineOf := rfl
  have hnext : ProfileContinuation root rootProfile nextPlan profile.afterCommit.afterReveal :=
    .conditionalCopy checkpoint.continuation
  exact delivery_conditional_block_common (headPlan := plan)
    (publicGuard := publicGuard) (nextPlan := nextPlan) (hhead := hhead)
    (profile := profile) (nextContinuation := hnext) (horigins := horigins)
    (current := current) (execution := execution) (final := final)
    (checkpoint := checkpoint) hroster relay hrelay hreference hfinal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_block_common'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_block_common

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_block

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditionalCopy_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditionalCopy_block
