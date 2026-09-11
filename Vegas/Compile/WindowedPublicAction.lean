/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationSourcePublicAgreement
import Vegas.Compile.SourceAdequacy
import Vegas.Compile.WindowedOwnedCheckpoint

/-! # Locality of focal public source actions

An owned complete block determines the same public source value in two related
executions.  The theorem is shared by ordinary public choice and both
conditional-publication accounting cases; their plans differ, but all three
compile the selected value into the same two-field commit/reveal source shape.
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
variable {windowOf : Nat → Nat} {roster : List P} {owner : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {fresh : FreshBindings (.commit name owner guard
  (.reveal publicName owner name .here tail))}
variable {state : BuildState P L Γ}

/-- Two supported focal-owned blocks that represent source successors of the
same generated commit/reveal head select the same public source value.  The
result is read from final public memory; no equality of successor source views
or constructor-specific submission branch is assumed. -/
theorem public_block_action_eq
    {accounted : CommitmentAccounting pending
      (.commit name owner guard (.reveal publicName owner name .here tail))}
    {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile
      (.commit name owner guard (.reveal publicName owner name .here tail))}
    {leftCurrent rightCurrent : CoupledAt
      (compileCore (.commit name owner guard (.reveal publicName owner name .here tail))
        fresh state).graph state}
    {left right :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      owner replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      owner replacement blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) owner left right)
    (command :
      List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
        (root.windowed deadlineOf binding choice windowOf).application.View →
          (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (howner : instruction.submitter = some owner) (hroster : roster.Nodup)
    (finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : finalLeft ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) left).support)
    (hright : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support)
    (leftValue rightValue : L.Val ty)
    (leftNext rightNext : CoupledAt (compileCore tail fresh.2.2
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1).graph
      (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
        publicName owner .here fresh.2.1).1)
    (hleftSource : leftNext.current.source =
      (leftCurrent.current.source.cons leftValue).cons leftValue)
    (hrightSource : rightNext.current.source =
      (rightCurrent.current.source.cons rightValue).cons rightValue)
    (hleftRefines : finalLeft.native.application.base.Refines leftNext.current.graph.1)
    (hrightRefines : finalRight.native.application.base.Refines rightNext.current.graph.1) :
    leftValue = rightValue := by
  have hfinalAgreement := leftCheckpoint.owned_block_agreement rightCheckpoint agreement
    command hpure instruction rest hhead howner hroster finalLeft finalRight hleft hright
  let added := ((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
    publicName owner .here fresh.2.1
  obtain ⟨fieldSpec, hfield, htype, hfieldOwner⟩ :=
    compileCore_fieldOf_spec tail fresh.2.2 added.1 (VHasVar.here)
  have hpublic : (compileCore tail fresh.2.2 added.1).graph.fieldRefPublic
      ⟨added.1.fieldOf VHasVar.here, ty⟩ :=
    ⟨fieldSpec, hfield, htype, hfieldOwner⟩
  have hvalue := ApplicationImage.State.publicSourceValue_eq_of_memory_eq
    hleftRefines hrightRefines hfinalAgreement.state.base.memory VHasVar.here hpublic hpublic
  simpa only [hleftSource, hrightSource, VEnv.cons_get_here] using hvalue

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.public_block_action_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.public_block_action_eq
