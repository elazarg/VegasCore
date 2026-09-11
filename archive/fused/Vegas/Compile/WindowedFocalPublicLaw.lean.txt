/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourceDecisionCoverage
import Vegas.Compile.WindowedBlockDeterminism

/-! # Exact continuation laws for focal public-decision blocks -/

noncomputable section

namespace Vegas.ApplicationPlan.PublicDecision

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {α : Type}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
variable {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
variable {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
variable {windowOf : Nat → Nat} {roster : List P} {focal : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable {blockIndex : Nat} {name publicName : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed focal ty) :: Γ)}
variable {accounted : CommitmentAccounting pending
  (.commit name focal guard (.reveal publicName focal name .here tail))}
variable {fresh : FreshBindings
  (.commit name focal guard (.reveal publicName focal name .here tail))}
variable {state : BuildState P L Γ} {plan : ApplicationPlan accounted fresh state}
variable {profile : SourceBehavioralProfile
  (.commit name focal guard (.reveal publicName focal name .here tail))}
variable {nextPending : Finset VarId} {nextAccounted : CommitmentAccounting nextPending tail}
variable {nextPlan : ApplicationPlan nextAccounted fresh.2.2
  (((state.addCommitEvent name focal guard fresh.1).1).addRevealEvent
    publicName focal .here fresh.2.1).1}

/-- Common probability argument for all three focal public-decision heads.
Constructor-specific callers supply the genuine successor prefix for every
supported native final. -/
theorem continuation_bind_of_successors
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (instruction : ApplicationInstruction P L) (rest : List (ApplicationInstruction P L))
    (hhead : plan.instructions deadlineOf = instruction :: rest)
    (howner : instruction.submitter = some focal)
    (current : CoupledAt
      (compileCore (.commit name focal guard (.reveal publicName focal name .here tail))
        fresh state).graph state)
    (execution :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (trace : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
      replacement initial blockIndex plan profile current execution)
    (nativeAfter :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution → FinDist α)
    (sourceAfter : VEnv L ((publicName, .pub ty) :: (name, .sealed focal ty) :: Γ) → FinDist α)
    (hsuccess : ∀ final, final ∈ ((root.windowed deadlineOf binding choice windowOf).application
        |>.runPolicies
          (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
          ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
          (WindowedApplication.blockInvocations roster) execution).support →
      ∃ (value : L.Val ty)
        (_legal : evalGuard guard value
          ((current.current.source.toView focal).eraseEnv) = true)
        (sourceNext : CoupledAt (compileCore tail fresh.2.2
          (((state.addCommitEvent name focal guard fresh.1).1).addRevealEvent
            publicName focal .here fresh.2.1).1).graph
          (((state.addCommitEvent name focal guard fresh.1).1).addRevealEvent
            publicName focal .here fresh.2.1).1),
        sourceNext.current.source = (current.current.source.cons value).cons value ∧
        final.native.application.base.Refines sourceNext.current.graph.1 ∧
        WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
          replacement initial (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
            sourceNext final)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) focal
        replacement initial (blockIndex + 1) nextPlan profile.afterCommit.afterReveal
          sourceNext final →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
      roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
      command hpure instruction rest hhead howner
    let block := (root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution
    block.bind nativeAfter =
      (head.extend (profile focal (.here guard _))
        ((current.current.source.toView focal).eraseEnv)).bind fun selected =>
          sourceAfter ((current.current.source.cons selected.1).cons selected.1) := by
  dsimp only
  let head := publicDecisionCheckpoints root rootProfile deadlineOf binding choice windowOf
    roster focal replacement initial blockIndex plan profile hinitial horigins hroster howners
    command hpure instruction rest hhead howner
  let block := (root.windowed deadlineOf binding choice windowOf).application.runPolicies
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
    ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
    (WindowedApplication.blockInvocations roster) execution
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let base := fun actor =>
    runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)
  let timed := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp [players, windowedPlayers, hpure]
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hindexOriginal := trace.checkpoint.instruction_at instruction rest hhead
  have hindex : runtime.image.instructions[blockIndex]? = some timed := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, timed]
  have htimedOwner : timed.submitter = some focal := by
    cases instruction <;> exact howner
  obtain ⟨anchorFinal, hblock⟩ := runtime.runPolicies_block_eq_pure roster hroster focal
    command base players hfocal hothers timed htimedOwner blockIndex execution hindex
    (fun actor hactor => trace.checkpoint.historyAlignment hroster actor hactor |>.1)
    trace.checkpoint.environmentHistory_length
  have hblock' : block = FinDist.pure anchorFinal := hblock
  have hanchorFinal : anchorFinal ∈ block.support := by
    rw [hblock']
    exact FinDist.mem_support_pure.mpr rfl
  obtain ⟨anchorValue, anchorLegal, anchorNext, anchorSource, anchorRefines, anchorPrefix⟩ :=
    hsuccess anchorFinal hanchorFinal
  let anchor : PublicDecision root rootProfile deadlineOf binding choice windowOf roster focal
      replacement initial blockIndex plan profile :=
    { current := current, execution := execution, final := anchorFinal
      sourcePrefix := trace, value := anchorValue, legal := anchorLegal
      sourceNext := anchorNext, source := anchorSource, refines := anchorRefines
      block := hanchorFinal }
  have hlocal : head.extend (profile focal (.here guard _))
      ((current.current.source.toView focal).eraseEnv) =
        FinDist.pure (head.action anchor) :=
    head.extend_at_checkpoint (profile focal (.here guard _)) anchor
  change block.bind nativeAfter =
    (head.extend (profile focal (.here guard _))
      ((current.current.source.toView focal).eraseEnv)).bind
        (fun selected => sourceAfter
          (.cons selected (.cons selected current.current.source)))
  rw [hblock', FinDist.pure_bind, hlocal, FinDist.pure_bind]
  have hcontinuation := hafter anchorNext anchorFinal anchorPrefix
  rw [anchorSource] at hcontinuation
  exact hcontinuation

end Vegas.ApplicationPlan.PublicDecision

/-- info: 'Vegas.ApplicationPlan.PublicDecision.continuation_bind_of_successors'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.PublicDecision.continuation_bind_of_successors
