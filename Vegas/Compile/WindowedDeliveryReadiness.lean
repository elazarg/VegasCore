/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBindingReadiness
import Vegas.Compile.WindowedPublicChoiceOwner
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedConditionalReadiness

/-! # Source kernels at delivery-service checkpoints

The delivery service has the same two ordinary head polls as the basic block
service.  These lemmas derive their source kernels from an actual delivery
checkpoint; later delivery and reaction turns remain an arbitrary continuation.
-/

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
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}
variable {unrestricted : UnrestrictedBinding guard}
variable {nextPlan : ApplicationPlan accounted fresh.2
  (state.addCommitEvent name owner guard fresh.1).1}
variable {profile : SourceBehavioralProfile (.commit name owner guard tail)}
variable {current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state}
variable {execution :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- The first binding poll under the delivery service samples the source value
once and retains it jointly with every subsequent native continuation. -/
theorem delivery_binding_first_poll_source_law
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
      profile current execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := runtime.deliveryService roster recipients |>.players
      (root.liftProfile deadlineOf rootProfile) focal replacement
    let encoding := (ApplicationImage.registrationEncoding state.nextField).privateCommand
      runtime.application
    let choices := profile owner (.here guard tail)
      ((current.current.source.toView owner).eraseEnv)
    (players owner (execution.principalHistory owner)
        (State.observe runtime.application execution.native owner) =
      choices.map fun chosen =>
        .privateCommand (.register state.nextField ⟨ty, chosen.1⟩)) ∧
    ∀ environment schedule,
      (runtime.application.runPolicies players environment (.player owner :: schedule)
        execution).map (fun next =>
          (encoding.cachedValue runtime.application (next.principalHistory owner), next)) =
        choices.bind fun chosen =>
          ((runtime.application.playerStep owner execution
            (.privateCommand (.register state.nextField ⟨ty, chosen.1⟩))).bind
              (runtime.application.runPolicies players environment schedule)).map
                (fun next => (some ⟨ty, chosen.1⟩, next)) := by
  intro runtime players encoding choices
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  have hcache := reference.head_cacheEmpty (.bind code) _ rfl rfl
  have hregistration : (root.image deadlineOf).registrationCache state.nextField
      ((execution.principalHistory owner).map runtime.erasePlayerEntry) = none := by
    exact hcache.1
  have halign := runtime.runPolicies_repeatedDeliveryBlocks_history_alignment roster recipients
    hroster owner howner players (runtime.deliveryService roster recipients).environment
      blockIndex _ execution
    checkpoint.reached
  have hindexOriginal := checkpoint.instruction_at (.bind code) _ rfl
  have hindex : runtime.image.instructions[(execution.principalHistory owner).length / 4]? =
      some (.bind { code with timeout := binding code }) := by
    rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have hpolicy : players owner = runtime.deliveryBlockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) :=
    reference.policy
  have hordinary : players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
        runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)
          (execution.principalHistory owner)
          (State.observe runtime.application execution.native owner) := by
    rw [hpolicy]
    exact runtime.deliveryBlockPlayer_ordinary owner _ _ _ _ hindex
      (checkpoint.activeAddress?_head (.bind code) _ rfl) (Or.inl (by rw [halign.1]; omega)) rfl
  exact checkpoint.continuation.windowedBinding_sample_of_unchanged_owner deadlineOf binding choice
    windowOf players (fun history view command hcommand => by
      rw [hpolicy] at hcommand
      exact (runtime.deliveryService roster recipients).reference_supported owner
        (root.liftProfile deadlineOf rootProfile owner) history view command hcommand)
    (runtime.deliveryService roster recipients).environment
    (List.replicate blockIndex
      (runtime.deliveryService roster recipients).invocations).flatten execution
    checkpoint.reached current checkpoint.refines
    (checkpoint.continuation.initialControllerReadsPublic hinitial).1 hregistration hordinary

section PublicChoice

variable {publicName : VarId}
variable {publicTail : VegasCore P L
  ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {publicUnresolved : name ∈ insert name pending}
variable {publicAccounted : CommitmentAccounting ((insert name pending).erase name) publicTail}
variable {publicFresh : FreshBindings
  (.commit name owner guard (.reveal publicName owner name .here publicTail))}
variable {publicState : BuildState P L Γ}
variable {publicGuard :
  (PublicChoiceSite.atHead name publicName owner guard publicTail).PubliclyValidatable
    publicFresh publicState}
variable {publicNext : ApplicationPlan publicAccounted publicFresh.2.2
  (((publicState.addCommitEvent name owner guard publicFresh.1).1).addRevealEvent
    publicName owner .here publicFresh.2.1).1}
variable {publicProfile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here publicTail))}
variable {publicCurrent : CoupledAt
  (compileCore (.commit name owner guard (.reveal publicName owner name .here publicTail))
    publicFresh publicState).graph publicState}

/-- The first delivery-service public-choice poll has exactly the source
choice law. Subsequent delivery and reaction slots are not restricted here. -/
theorem delivery_publicChoice_first_poll_source_law
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex (.publicChoice (newName := newName)
        (unresolved := publicUnresolved) publicGuard publicNext)
      publicProfile publicCurrent execution)
    (hinitial : root.InitialControllerReadsPublic)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := runtime.deliveryService roster recipients |>.players
      (root.liftProfile deadlineOf rootProfile) focal replacement
    let encoding := ApplicationImage.choiceEncoding (P := P)
      (publicState.nodes.length + 1) ty
    players owner (execution.principalHistory owner)
        (State.observe runtime.application execution.native owner) =
      (publicProfile owner (.here guard
        (.reveal publicName owner name .here publicTail))
        ((publicCurrent.current.source.toView owner).eraseEnv)).map fun chosen =>
          .submit (encoding.encode chosen.1) := by
  intro runtime players encoding
  let site := PublicChoiceSite.atHead name publicName owner guard publicTail
  let code := site.code publicFresh publicState
  let instruction : ApplicationInstruction P L :=
    .publicChoice { code with timeout := choice code }
  have hhead : (ApplicationPlan.publicChoice (newName := newName)
      (unresolved := publicUnresolved) (fresh := publicFresh) publicGuard publicNext).instructions
        deadlineOf = .publicChoice code :: publicNext.instructions deadlineOf := rfl
  have hcacheInstruction := reference.head_cacheEmpty (.publicChoice code) _ hhead rfl
  have hcache : (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none :=
    (runtime.cachedValue_erasePlayerEntry (root.image deadlineOf) encoding
      (execution.principalHistory owner)).trans hcacheInstruction
  have halign := runtime.runPolicies_repeatedDeliveryBlocks_history_alignment roster recipients
    hroster owner howner players (runtime.deliveryService roster recipients).environment
      blockIndex _ execution checkpoint.reached
  have hindexOriginal := checkpoint.instruction_at (.publicChoice code) _ hhead
  have hindex : runtime.image.instructions[(execution.principalHistory owner).length / 4]? =
      some instruction := by
    rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts, instruction]
  have hpolicy : players owner = runtime.deliveryBlockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) :=
    reference.policy
  have hordinary : players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
        runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)
          (execution.principalHistory owner)
          (State.observe runtime.application execution.native owner) := by
    rw [hpolicy]
    exact runtime.deliveryBlockPlayer_ordinary owner _ _ _ instruction hindex
      (checkpoint.activeAddress?_head (.publicChoice code) _ hhead)
      (Or.inl (by rw [halign.1]; omega)) rfl
  have hsource := checkpoint.continuation.windowedPublicChoice_sample_of_unchanged_owner
    deadlineOf binding choice windowOf players (fun history view command hcommand => by
      rw [hpolicy] at hcommand
      exact (runtime.deliveryService roster recipients).reference_supported owner
        (root.liftProfile deadlineOf rootProfile owner) history view command hcommand)
    (runtime.deliveryService roster recipients).environment
    (List.replicate blockIndex
      (runtime.deliveryService roster recipients).invocations).flatten execution
    checkpoint.reached publicCurrent checkpoint.refines
    (checkpoint.continuation.initialControllerReadsPublic hinitial).1 hcache hordinary
  exact hsource.1

end PublicChoice

section Conditional

variable {conditionalName conditionalPublicName : VarId} {conditionalTy : L.Ty}
variable {conditionalGuard : L.Expr
  ((conditionalName, conditionalTy) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {conditionalTail : VegasCore P L
  ((conditionalPublicName, .pub conditionalTy) ::
    (conditionalName, .sealed owner conditionalTy) :: Γ)}
variable {spec : ConditionalOpening conditionalGuard}
variable {conditionalAccounted : CommitmentAccounting pending
  (.commit conditionalName owner conditionalGuard
    (.reveal conditionalPublicName owner conditionalName .here conditionalTail))}
variable {conditionalFresh : FreshBindings
  (.commit conditionalName owner conditionalGuard
    (.reveal conditionalPublicName owner conditionalName .here conditionalTail))}
variable {conditionalState : BuildState P L Γ}
variable {conditionalPlan : ApplicationPlan conditionalAccounted conditionalFresh conditionalState}
variable {conditionalProfile : SourceBehavioralProfile
  (.commit conditionalName owner conditionalGuard
    (.reveal conditionalPublicName owner conditionalName .here conditionalTail))}
variable {conditionalCurrent : CoupledAt
  (compileCore (.commit conditionalName owner conditionalGuard
    (.reveal conditionalPublicName owner conditionalName .here conditionalTail))
      conditionalFresh conditionalState).graph conditionalState}

/-- Both conditional accounting forms have the same disposition-indexed
source law at their first delivery-service poll. -/
theorem delivery_conditional_first_poll_source_law
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex conditionalPlan conditionalProfile conditionalCurrent execution)
    (head : ConditionalHead spec conditionalPlan)
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup) (howner : owner ∈ roster)
    (reference : checkpoint.ReferenceOwner owner)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding :
      let site := ConditionalPublicationSite.atHead
        conditionalName conditionalPublicName owner conditionalGuard conditionalTail spec
      (site.code conditionalFresh conditionalState
        (site.sourceField conditionalFresh conditionalState)
        (deadlineOf (site.choice.publicationNode conditionalFresh conditionalState))).binding?
          execution.native.application.base.memory = some disposition) :
    let runtime := root.windowed deadlineOf binding choice windowOf
    let players := runtime.deliveryService roster recipients |>.players
      (root.liftProfile deadlineOf rootProfile) focal replacement
    let site := ConditionalPublicationSite.atHead conditionalName conditionalPublicName owner
      conditionalGuard conditionalTail spec
    let encoding := site.choiceEncodingFor conditionalFresh conditionalState
      (site.sourceField conditionalFresh conditionalState)
      (deadlineOf (site.choice.publicationNode conditionalFresh conditionalState)) disposition
      (ApplicationImage.conditionalTransport spec.secretTy)
    players owner (execution.principalHistory owner)
        (State.observe runtime.application execution.native owner) =
      (conditionalProfile owner site.choice.decision
        ((conditionalCurrent.current.source.toView owner).eraseEnv)).map fun chosen =>
          .submit (encoding.encode chosen.1) := by
  intro runtime players site encoding
  let code := site.code conditionalFresh conditionalState
    (site.sourceField conditionalFresh conditionalState)
    (deadlineOf (site.choice.publicationNode conditionalFresh conditionalState))
  obtain ⟨actual, hactual, hcanonical⟩ :=
    checkpoint.conditional_binding_disposition head horigins
  have heq : actual = disposition := Option.some.inj (hactual.symm.trans hbinding)
  subst actual
  obtain ⟨rest, hhead⟩ := head.instructions deadlineOf
  have hcacheInstruction := reference.head_cacheEmpty (.conditional code) rest hhead rfl
  have hcacheOriginal : (encoding.submission (root.image deadlineOf).application).cachedValue
      (root.image deadlineOf).application
      ((execution.principalHistory owner).map runtime.erasePlayerEntry) = none := by
    convert hcacheInstruction disposition using 1
    · rfl
    · cases disposition <;> rfl
  have hcache : (encoding.submission runtime.application).cachedValue runtime.application
      (execution.principalHistory owner) = none :=
    (runtime.cachedValue_erasePlayerEntry (root.image deadlineOf) encoding
      (execution.principalHistory owner)).trans hcacheOriginal
  have halign := runtime.runPolicies_repeatedDeliveryBlocks_history_alignment roster recipients
    hroster owner howner players (runtime.deliveryService roster recipients).environment
      blockIndex _ execution checkpoint.reached
  have hindexOriginal := checkpoint.instruction_at (.conditional code) rest hhead
  have hindex : runtime.image.instructions[(execution.principalHistory owner).length / 4]? =
      some (.conditional code) := by
    rw [halign.2.2.1]
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, ApplicationInstruction.withBindingTimeouts,
      ApplicationInstruction.withChoiceTimeouts]
  have hpolicy : players owner = runtime.deliveryBlockPlayer owner
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)) :=
    reference.policy
  have hordinary : players owner (execution.principalHistory owner)
      (State.observe runtime.application execution.native owner) =
        runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile owner)
          (execution.principalHistory owner)
          (State.observe runtime.application execution.native owner) := by
    rw [hpolicy]
    exact runtime.deliveryBlockPlayer_ordinary owner _ _ _ (.conditional code) hindex
      (checkpoint.activeAddress?_head (.conditional code) rest hhead)
      (Or.inl (by rw [halign.1]; omega)) rfl
  have hsource := ProfileContinuation.windowedConditional_sample_of_unchanged_owner spec head
    checkpoint.continuation deadlineOf binding choice windowOf players
    (fun history view command hcommand => by
      rw [hpolicy] at hcommand
      exact (runtime.deliveryService roster recipients).reference_supported owner
        (root.liftProfile deadlineOf rootProfile owner) history view command hcommand)
    (runtime.deliveryService roster recipients).environment
    (List.replicate blockIndex
      (runtime.deliveryService roster recipients).invocations).flatten execution
    checkpoint.reached conditionalCurrent checkpoint.refines
    (head.initialReadsPublic (checkpoint.continuation.initialControllerReadsPublic hinitial))
    disposition hbinding hcanonical hcache hordinary
  exact hsource.1

end Conditional

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_first_poll_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.delivery_binding_first_poll_source_law

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_publicChoice_first_poll_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.delivery_publicChoice_first_poll_source_law

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_first_poll_source_law'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.WindowedCheckpoint.delivery_conditional_first_poll_source_law
