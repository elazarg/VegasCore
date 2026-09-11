/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedConditionalOwner

/-! # Cached generated conditional choices do not retry -/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Once the canonical conditional submission cache contains a value, the
unchanged owner's next ordinary poll waits. This applies uniformly to a
conditional discharge and a conditional copy. -/
theorem windowedConditional_wait_of_cached
    {rootContext Γ : VCtx P L} {rootPending headPending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    (spec : ConditionalOpening guard)
    {headAccounted : CommitmentAccounting headPending
      (.commit name who guard (.reveal publicName who name .here tail))}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {state : BuildState P L Γ}
    {headPlan : ApplicationPlan headAccounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail))}
    (head : ConditionalHead spec headPlan)
    (continuation : ProfileContinuation root rootProfile headPlan profile)
    (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (howner : players who =
      (root.windowed deadlineOf binding choice windowOf).blockPlayer who
        ((root.windowed deadlineOf binding choice windowOf).liftPlayerPolicy
          (root.liftProfile deadlineOf rootProfile who)))
    (execution : (root.windowed deadlineOf binding choice
      windowOf).application.PolicyExecution)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh state).graph state)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (disposition : BindingDisposition (CommitmentHandle P Nat) (L.Val spec.secretTy))
    (hbinding : let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      (site.code fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state))).binding?
          execution.native.application.base.memory = some disposition)
    (value : L.Val ty)
    (hcache : let runtime := root.windowed deadlineOf binding choice windowOf
      let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
      let encoding := site.choiceEncodingFor fresh state (site.sourceField fresh state)
        (deadlineOf (site.choice.publicationNode fresh state)) disposition
        (ApplicationImage.conditionalTransport spec.secretTy)
      ChoiceEncoding.cachedValue runtime.application
        (encoding.submission runtime.application) (execution.principalHistory who) = some value)
    (instruction : ApplicationInstruction P L)
    (hindex : getElem? (root.windowed deadlineOf binding choice windowOf).image.instructions
      ((execution.principalHistory who).length / 3) = some instruction)
    (hactive : (root.windowed deadlineOf binding choice windowOf).image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hslot : (execution.principalHistory who).length % 3 < 2)
    (hsubmitter : instruction.submitter = some who) :
    players who (execution.principalHistory who)
      (State.observe (root.windowed deadlineOf binding choice windowOf).application
        execution.native who) = FinDist.pure .wait := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let original := root.image deadlineOf
  let site := ConditionalPublicationSite.atHead name publicName who guard tail spec
  let sourceSlot := site.sourceField fresh state
  let deadline := deadlineOf (site.choice.publicationNode fresh state)
  let encoding := site.choiceEncodingFor fresh state sourceSlot deadline disposition
    (ApplicationImage.conditionalTransport spec.secretTy)
  have hready := PublicChoiceSite.ready_at_source_prefix guard tail fresh state current
    execution.native.application.base.memory.done hrefines.memory.completed
  have hunresolved : execution.native.application.base.memory.done
      (site.choice.publicationNode fresh state) = false := by
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hready
    exact hready.1.2
  have hbase : root.liftProfile deadlineOf rootProfile who
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (runtime.eraseView (State.observe runtime.application execution.native who)) =
        FinDist.pure .wait := by
    unfold ApplicationPlan.liftProfile
    let projected : original.application.State :=
      ⟨execution.native.application.base, execution.native.pool, execution.native.receipts⟩
    change root.liftProfileIn original deadlineOf rootProfile who
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe original.application projected who) = _
    rw [continuation.liftProfileIn_eq_of_refines original deadlineOf current projected
      hrefines who ((execution.principalHistory who).map runtime.erasePlayerEntry)]
    rw [head.liftProfileIn original deadlineOf profile
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe original.application projected who) hunresolved]
    have hbindingOriginal : (site.code fresh state sourceSlot deadline).binding?
        (State.observe original.application projected who).application = some disposition := by
      exact hbinding
    let controller := site.imageController fresh state sourceSlot deadline original disposition
      (original.ownerReadout? who (site.choice.compiledGuard fresh state).choiceReads)
      (profile who site.choice.decision) (fun _ _ => false)
    have hcacheOriginal : (encoding.submission original.application).cachedValue
        original.application ((execution.principalHistory who).map runtime.erasePlayerEntry) =
          some value := by
      exact (runtime.cachedValue_erasePlayerEntry original encoding
        (execution.principalHistory who)).symm.trans hcache
    have hpolicy := controller.policy_of_cached original.application
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe original.application projected who) value hunresolved hcacheOriginal
    dsimp only [ConditionalPublicationSite.imagePolicy]
    rw [hbindingOriginal]
    change controller.policy original.application
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe original.application projected who) = _
    rw [hpolicy]
    simp [controller, ConditionalPublicationSite.imageController,
      ConditionalPublicationSite.controllerFor]
  rw [howner, runtime.blockPlayer_normal who _ _ _ instruction hindex hactive hslot hsubmitter]
  unfold WindowedApplication.liftPlayerPolicy
  rw [hbase]
  simp [WindowedApplication.liftPlayerCommand]

end Vegas.ApplicationPlan.ProfileContinuation

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.windowedConditional_wait_of_cached'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.windowedConditional_wait_of_cached
