/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourceDecisionCoverage
import Vegas.Compile.WindowedBlockDeterminism

/-! # Exact continuation law for focal binding blocks -/

noncomputable section

namespace Vegas.ApplicationPlan.BindingDecision

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
variable {windowOf : Nat → Nat} {roster : List P} {focal relay : P}
variable {replacement :
  (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
variable {initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState}
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx focal Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed focal ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name focal guard tail)} {state : BuildState P L Γ}
variable {unrestricted : UnrestrictedBinding guard}
variable {next : ApplicationPlan accounted fresh.2
  (state.addCommitEvent name focal guard fresh.1).1}
variable {profile : SourceBehavioralProfile (.commit name focal guard tail)}

/-- Continuations of every actual focal binding outcome factor through the
point-mass source decision extracted from one supported anchor outcome. -/
theorem continuation_bind
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (hrelay : relay ∈ roster) (hrelayOther : relay ≠ focal)
    (anchor : BindingDecision (newName := newName) (fresh := fresh)
      root rootProfile deadlineOf binding choice
      windowOf roster focal replacement initial blockIndex unrestricted next profile)
    (nativeAfter :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution → FinDist α)
    (sourceAfter : VEnv L ((name, .sealed focal ty) :: Γ) → FinDist α)
    (hafter : ∀ sourceNext final,
      WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf roster focal
        replacement initial (blockIndex + 1) next profile.afterCommit sourceNext final →
      nativeAfter final = sourceAfter sourceNext.current.source) :
    let head := bindingDecisionCheckpoints (newName := newName) (fresh := fresh)
      root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
      blockIndex unrestricted next profile hinitial horigins hroster howners command hpure
      relay hrelay hrelayOther
    let block := (root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) anchor.execution
    block.bind nativeAfter =
      (head.extend (profile focal (.here guard tail))
        ((anchor.current.current.source.toView focal).eraseEnv)).bind fun selected =>
          sourceAfter (anchor.current.current.source.cons selected.1) := by
  dsimp only
  let head := bindingDecisionCheckpoints (newName := newName) (fresh := fresh)
    root rootProfile deadlineOf binding choice windowOf roster focal replacement initial
    blockIndex unrestricted next profile hinitial horigins hroster howners command hpure
    relay hrelay hrelayOther
  have hlocal : head.extend (profile focal (.here guard tail))
      ((anchor.current.current.source.toView focal).eraseEnv) =
        FinDist.pure (head.action anchor) :=
    head.extend_at_checkpoint (profile focal (.here guard tail)) anchor
  rw [hlocal, FinDist.pure_bind]
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let base := fun actor =>
    runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)
  let site : SourceDecisionSite focal (.commit name focal guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let instruction : ApplicationInstruction P L := .bind code
  let timed := (instruction.withBindingTimeouts binding).withChoiceTimeouts choice
  have hfocal : players focal = fun history view => FinDist.pure (command history view) := by
    simp [players, windowedPlayers, hpure]
  have hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (base actor) := by
    intro actor hactor
    simp only [players, base, windowedPlayers, Function.update_of_ne hactor,
      windowedReferencePlayers]
    rfl
  have hhead : (ApplicationPlan.binding (newName := newName) (fresh := fresh)
      unrestricted next).instructions deadlineOf =
        instruction :: next.instructions deadlineOf := rfl
  have hindexOriginal := anchor.sourcePrefix.checkpoint.instruction_at instruction _ hhead
  have hindex : runtime.image.instructions[blockIndex]? = some timed := by
    simp only [runtime, windowed, ApplicationImage.withChoiceTimeouts,
      ApplicationImage.withBindingTimeouts, ApplicationPlan.image, List.getElem?_map,
      hindexOriginal, Option.map_some, timed]
  have htimedOwner : timed.submitter = some focal := by rfl
  obtain ⟨deterministicFinal, hblock⟩ := runtime.runPolicies_block_eq_pure roster hroster
    focal command base players hfocal hothers timed htimedOwner blockIndex anchor.execution
    hindex (fun actor hactor =>
      anchor.sourcePrefix.checkpoint.historyAlignment hroster actor hactor |>.1)
    anchor.sourcePrefix.checkpoint.environmentHistory_length
  have hfinal : anchor.final = deterministicFinal := by
    have hanchorBlock := anchor.block
    rw [hblock, FinDist.mem_support_pure] at hanchorBlock
    exact hanchorBlock
  subst deterministicFinal
  have hblock' :
      (root.windowed deadlineOf binding choice windowOf).application.runPolicies
          (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
          ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
          (WindowedApplication.blockInvocations roster) anchor.execution =
        FinDist.pure anchor.final := hblock
  have hrelayReference :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement relay =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf relay := by
    simp only [windowedPlayers, Function.update_of_ne hrelayOther]
  rw [hblock', FinDist.pure_bind]
  obtain ⟨value, sourceNext, hsource, hnext, hresolved, _, _⟩ :=
    anchor.sourcePrefix.checkpoint.binding_block unrestricted next profile anchor.fallback
      anchor.deadline anchor.selected anchor.current anchor.execution anchor.final hroster relay
      hrelay hrelayReference anchor.block
  have hvalue : value = (head.action anchor).1 := hresolved
  rw [← hvalue, ← hsource]
  apply hafter
  exact .step anchor.sourcePrefix anchor.block
    (.binding anchor.fallback anchor.deadline anchor.selected value hsource hresolved) hnext

end Vegas.ApplicationPlan.BindingDecision

/-- info: 'Vegas.ApplicationPlan.BindingDecision.continuation_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BindingDecision.continuation_bind
