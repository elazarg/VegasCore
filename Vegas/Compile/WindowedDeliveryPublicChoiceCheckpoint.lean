/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedDeliveryPublicChoice
import Vegas.Compile.WindowedDeliveryCaches
import Vegas.Compile.WindowedDeliverySettlement
import Vegas.Compile.WindowedPublicChoiceCheckpoint

/-! # Delivery-service public-choice successors at source checkpoints -/

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
variable {publicUnresolved : name ∈ insert name pending}
variable {publicAccounted : CommitmentAccounting ((insert name pending).erase name) tail}
variable {publicFresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {publicState : BuildState P L Γ}
variable {publicGuard :
  (PublicChoiceSite.atHead name publicName owner guard tail).PubliclyValidatable
    publicFresh publicState}

/-- A complete delivery block at a public-choice head yields the typed source
choice or certified timeout value, its two source steps, and the next delivery
checkpoint. Progress is obtained from an unchanged relay; the focal policy is
otherwise arbitrary. -/
theorem delivery_publicChoice_block
    (nextPlan : ApplicationPlan publicAccounted publicFresh.2.2
      (((publicState.addCommitEvent name owner guard publicFresh.1).1).addRevealEvent
        publicName owner .here publicFresh.2.1).1)
    (profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail)))
    (fallback : SourceDecisionSite.PublicFallback
      (PublicChoiceSite.atHead name publicName owner guard tail).decision)
    (deadline : Nat)
    (hselect : choice ((PublicChoiceSite.atHead name publicName owner guard tail).code
      publicFresh publicState) = some ⟨deadline, fallback.compiled publicFresh publicState⟩)
    (current : CoupledAt
      (compileCore (.commit name owner guard
        (.reveal publicName owner name .here tail)) publicFresh publicState).graph
      publicState)
    (execution final :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex
      (.publicChoice (newName := newName) (unresolved := publicUnresolved)
        publicGuard nextPlan) profile current execution)
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
      (sourceNext : CoupledAt
        (compileCore (.commit name owner guard
          (.reveal publicName owner name .here tail)) publicFresh publicState).graph
        (((publicState.addCommitEvent name owner guard publicFresh.1).1).addRevealEvent
          publicName owner .here publicFresh.2.1).1),
      sourceNext.current.source = (current.current.source.cons chosen).cons chosen ∧
      evalGuard guard chosen ((current.current.source.toView owner).eraseEnv) = true ∧
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
          some ((PublicChoiceSite.atHead name publicName owner guard tail).code
            publicFresh publicState).endpoint.publicationNode := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
  let site := PublicChoiceSite.atHead name publicName owner guard tail
  let code := site.code publicFresh publicState
  let timed := site.timeoutCode fallback publicFresh publicState deadline
  have hhead : (ApplicationPlan.publicChoice (newName := newName)
      (unresolved := publicUnresolved) (fresh := publicFresh) publicGuard nextPlan).instructions
      deadlineOf = .publicChoice code :: nextPlan.instructions deadlineOf := rfl
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf (.publicChoice code)
    (List.mem_of_getElem? hindexOriginal)
  change (root.image deadlineOf).lookup code.endpoint.publicationNode =
    some (.publicChoice code) at hlookupOriginal
  have hlookup : runtime.image.lookup code.endpoint.publicationNode =
      some (.publicChoice timed) := by
    simp only [runtime, windowed, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, timed]
    rw [hlookupOriginal]
    simp only [Option.map_some, ApplicationInstruction.withChoiceTimeouts,
      ApplicationInstruction.withBindingTimeouts]
    have hchoice : choice code = some (site.timeout fallback publicFresh publicState deadline) := by
      simpa only [code, site, PublicChoiceSite.timeout] using hselect
    rw [hchoice]
    have htimeout : site.timeout fallback publicFresh publicState deadline =
        ⟨deadline, fallback.compiled publicFresh publicState⟩ := rfl
    rw [htimeout]
    dsimp [code, site, timed, PublicChoiceSite.timeoutCode, PublicChoiceSite.timeout]
  have hindex : runtime.image.instructions[blockIndex]? = some (.publicChoice timed) := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, timed]
    have hselect' : choice code =
        some (site.timeout fallback publicFresh publicState deadline) := by
      simpa only [code, site, PublicChoiceSite.timeout] using hselect
    rw [hselect']
    rfl
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
        some (.publicChoice timed) := by
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
  have hactive := checkpoint.activeAddress?_head (.publicChoice code) _ hhead
  obtain ⟨activation, hactivation, hkey, _⟩ :=
    checkpoint.active_origin_clock (.publicChoice code) _ hhead
  obtain ⟨beforeRoster, afterRoster, hsplit⟩ := List.mem_iff_append.mp hrelay
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
  have hsettled : runtime.image.activeAddress? final.native.application.base.memory ≠
      some timed.endpoint.publicationNode := by
    subst roster
    apply runtime.runPolicies_delivery_block_resolves beforeRoster afterRoster recipients relay
      owner hroster players (runtime.liftPlayerPolicy
        (root.liftProfile deadlineOf rootProfile relay)) hreference
      (.publicChoice timed) rfl current.current.graph.1 blockIndex execution final activation
      henvironment hprincipal
      hindex hlookup hactive hactivation hkey
      checkpoint.refines checkpoint.activationFresh checkpoint.consistent
      checkpoint.serialsBeforeNext rootState.initialFields.length hnodup hallocated hresolved
    · intro observed hobservedConsistent hobservedRefines hobservedActivation hoverdue
        hobservedSerial _ _ _
      have hobservedCode : runtime.image.lookup activation.key = some (.publicChoice timed) := by
        rw [hkey]
        exact hlookup
      obtain ⟨payload, resolved, hdue, _, hhandle, _⟩ :=
        runtime.publicChoice_source_relay_eligibility guard tail fallback publicFresh
          publicState deadline current observed activation relay hobservedConsistent
          hobservedActivation hobservedCode hobservedRefines publicGuard (by
            rw [hkey]
            have htimedEndpoint : timed.endpoint.publicationNode =
                code.endpoint.publicationNode := rfl
            simpa [htimedEndpoint, ApplicationInstruction.address] using hoverdue)
            hobservedSerial
      exact ⟨payload, resolved, hdue, hhandle⟩
    · exact hfinal
  obtain ⟨chosen, sourceNext, hlegal, hsource, hrefines, hfresh⟩ :=
    runtime.runPolicies_delivery_publicChoice_source_coupling roster recipients players
      (WindowedApplication.deliveryBlockInvocations roster recipients) guard tail fallback
      publicFresh publicState current publicGuard deadline execution final activation
      hindexRange hlookup hactive hactivation hkey
      checkpoint.refines hsettled hfinal
  have hsteps := site.completePublication_source_steps current.current.source chosen hlegal
  rw [← hsource] at hsteps
  refine ⟨chosen, sourceNext, hsource, hlegal, hsteps, ?_, hsettled⟩
  refine ⟨.publicChoice checkpoint.continuation, ?_, hrefines,
    checkpoint.reached_after_block final hfinal, ?_, hfresh⟩
  · have hcount := checkpoint.blockCount
    rw [hhead, List.length_cons] at hcount
    omega
  · exact delivery_block_caches
      (.publicChoice (newName := newName) (unresolved := publicUnresolved)
        publicGuard nextPlan) nextPlan profile deadlineOf _ rfl binding choice windowOf
      roster recipients hroster focal replacement blockIndex current execution final checkpoint
      hfinal

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_publicChoice_block'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.delivery_publicChoice_block
