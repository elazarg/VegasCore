/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPublicChoiceOwner

/-! # Cached generated public choices do not retry -/

noncomputable section

namespace Vegas.ApplicationPlan.ProfileContinuation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Once the generated public-choice submission cache contains a value, the
unchanged owner's next ordinary poll waits. Generated source policies disable
retry, so this is derived behavior rather than a command hypothesis. -/
theorem windowedPublicChoice_wait_of_cached
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg}
    {name publicName : VarId} {who : P} {ty : L.Ty}
    {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx who Γ)) L.bool}
    {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed who ty) :: Γ)}
    {newName : name ∉ pending} {unresolved : name ∈ insert name pending}
    {accounted : CommitmentAccounting ((insert name pending).erase name) tail}
    {fresh : FreshBindings (.commit name who guard (.reveal publicName who name .here tail))}
    {build : BuildState P L Γ}
    {publicGuard : (PublicChoiceSite.atHead name publicName who guard tail).PubliclyValidatable
      fresh build}
    {nextPlan : ApplicationPlan accounted fresh.2.2
      (((build.addCommitEvent name who guard fresh.1).1).addRevealEvent
        publicName who .here fresh.2.1).1}
    {profile : SourceBehavioralProfile
      (.commit name who guard (.reveal publicName who name .here tail))}
    (continuation : ProfileContinuation root rootProfile
      (.publicChoice (newName := newName) (unresolved := unresolved)
        (fresh := fresh) publicGuard nextPlan) profile)
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
    (execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (current : CoupledAt
      (compileCore (.commit name who guard (.reveal publicName who name .here tail))
        fresh build).graph build)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (value : L.Val ty)
    (hcache : let runtime := root.windowed deadlineOf binding choice windowOf
      ((ApplicationImage.choiceEncoding (P := P) (build.nodes.length + 1) ty).submission
        runtime.application).cachedValue runtime.application
          (execution.principalHistory who) = some value)
    (instruction : ApplicationInstruction P L)
    (hindex : getElem?
      (root.windowed deadlineOf binding choice windowOf).image.instructions
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
  let site := PublicChoiceSite.atHead name publicName who guard tail
  let encoding := ApplicationImage.choiceEncoding (P := P) (build.nodes.length + 1) ty
  have hreadyNative := PublicChoiceSite.ready_at_source_prefix guard tail fresh build current
    execution.native.application.base.memory.done hrefines.memory.completed
  have hunresolved : execution.native.application.base.memory.done (build.nodes.length + 1) =
      false := by
    simp only [PublicChoice.ready, Bool.and_eq_true, Bool.not_eq_true'] at hreadyNative
    exact hreadyNative.1.2
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
    have hdone : (State.observe original.application projected who).application.done
        (build.nodes.length + 1) = false := hunresolved
    simp only [ApplicationPlan.liftProfileIn, hdone, Bool.false_eq_true, ↓reduceIte]
    let readout := original.ownerReadout? who (site.compiledGuard fresh build).choiceReads
    let controller := site.imageController fresh build original readout
      (profile who site.decision) (fun _ _ => false)
    have hcacheOriginal : (encoding.submission original.application).cachedValue
        original.application ((execution.principalHistory who).map runtime.erasePlayerEntry) =
          some value := by
      exact (runtime.cachedValue_erasePlayerEntry original encoding
        (execution.principalHistory who)).symm.trans hcache
    have hpolicy := controller.policy_of_cached original.application
      ((execution.principalHistory who).map runtime.erasePlayerEntry)
      (State.observe original.application projected who) value hdone hcacheOriginal
    rw [hpolicy]
    simp [controller, PublicChoiceSite.imageController, PublicChoiceSite.controller]
  rw [howner, runtime.blockPlayer_normal who _ _ _ instruction hindex hactive hslot hsubmitter]
  unfold WindowedApplication.liftPlayerPolicy
  rw [hbase]
  simp [WindowedApplication.liftPlayerCommand]

end Vegas.ApplicationPlan.ProfileContinuation

/-- info: 'Vegas.ApplicationPlan.ProfileContinuation.windowedPublicChoice_wait_of_cached'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.ProfileContinuation.windowedPublicChoice_wait_of_cached
