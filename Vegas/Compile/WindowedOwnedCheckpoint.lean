/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedBlock
import Vegas.Compile.WindowedCheckpoint

/-! # Focal-owned block privacy at actual source checkpoints

Initialized reachability supplies all history lengths and consistency. Source
compilation supplies the concrete instruction and handler lookup. The only
paired premise is the preceding information agreement, as needed by the
source-prefix induction; that induction is a separate obligation.
-/

noncomputable section

namespace Vegas.ApplicationPlan.WindowedCheckpoint

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {accounted : CommitmentAccounting pending prog}
variable {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
variable {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {plan : ApplicationPlan accounted fresh state}
variable {rootProfile : SourceBehavioralProfile rootProg} {profile : SourceBehavioralProfile prog}
variable {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P} {blockIndex : Nat}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {leftCurrent rightCurrent : CoupledAt (compileCore prog fresh state).graph state}
variable {left right :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- Every pair of supported executions of the next focal-owned block retains
focal information agreement. All runtime command forms remain available to
the pure focal replacement; unchanged policies use their actual root lift.
The two source environments need not agree on opponents' sealed values. -/
theorem owned_block_agreement
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      focal replacement blockIndex plan profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      roster focal replacement blockIndex plan profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) focal left right)
    (command :
      List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
        (root.windowed deadlineOf binding choice windowOf).application.View →
          (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (howner : instruction.submitter = some focal) (hroster : roster.Nodup)
    (finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : finalLeft ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) left).support)
    (hright : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) right).support) :
    WindowedApplication.PolicyAgreement (root.windowed deadlineOf binding choice windowOf)
      focal finalLeft finalRight := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf
    focal replacement
  let base := fun actor => runtime.liftPlayerPolicy
    (root.liftProfile deadlineOf rootProfile actor)
  let timed := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have hindexOriginal := leftCheckpoint.instruction_at instruction rest hhead
  have hlookupOriginal := root.image_lookup_of_mem deadlineOf instruction
    (List.mem_of_getElem? hindexOriginal)
  have haddress : timed.address = instruction.address := by simp [timed]
  have hlookup : runtime.image.lookup timed.address = some timed := by
    simp only [runtime, windowed, haddress, ApplicationImage.lookup_withChoiceTimeouts,
      ApplicationImage.lookup_withBindingTimeouts, hlookupOriginal, Option.map_some]
    rfl
  have hindex : runtime.image.instructions[blockIndex]? = some timed := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some]
    rfl
  have htimedOwner : timed.submitter = some focal := by
    have hsame : timed.submitter = instruction.submitter := by cases instruction <;> rfl
    exact hsame.trans howner
  have hlengths : ∀ actor, (left.principalHistory actor).length =
      (right.principalHistory actor).length := by
    intro actor
    have hl := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf) left leftCheckpoint.reached
    have hr := runtime.application.runPolicies_principalHistory_length actor players
      (runtime.blockEnvironment roster)
      (List.replicate blockIndex (WindowedApplication.blockInvocations roster)).flatten
      (root.windowedInitialExecution deadlineOf binding choice windowOf)
      right rightCheckpoint.reached
    exact hl.trans hr.symm
  apply agreement.block_owned roster hroster command base players _ _ timed htimedOwner hlookup
    blockIndex hindex leftCheckpoint.consistent hlengths
    (leftCheckpoint.environmentHistory_length.trans rightCheckpoint.environmentHistory_length.symm)
    (fun actor hactor => (leftCheckpoint.historyAlignment hroster actor hactor).1)
    leftCheckpoint.environmentHistory_length finalLeft finalRight hleft hright
  · simp only [players, windowedPlayers, Function.update_self]
    exact hpure
  · intro actor hactor
    simp only [players, windowedPlayers, Function.update_of_ne hactor, windowedReferencePlayers]
    rfl

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.owned_block_agreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.owned_block_agreement
