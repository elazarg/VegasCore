/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSourceDecisionCoverage

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
  let chosen := (head.action anchor).1
  have hlocal : head.extend (profile focal (.here guard tail))
      ((anchor.current.current.source.toView focal).eraseEnv) =
        FinDist.pure (head.action anchor) :=
    head.extend_at_checkpoint (profile focal (.here guard tail)) anchor
  rw [hlocal, FinDist.pure_bind]
  calc
    _ = ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) anchor.execution).bind
          (fun _ => sourceAfter (anchor.current.current.source.cons chosen)) := by
      apply FinDist.bind_congr
      intro final hfinal
      obtain ⟨value, sourceNext, hsource, hnext, hresolved, _, _⟩ :=
        anchor.sourcePrefix.checkpoint.binding_block unrestricted next profile anchor.fallback
          anchor.deadline anchor.selected anchor.current anchor.execution final hroster relay
          hrelay hrelayOther hfinal
      let sibling : BindingDecision (newName := newName) (fresh := fresh)
          root rootProfile deadlineOf binding choice
          windowOf roster focal replacement initial blockIndex unrestricted next profile :=
        { anchor with final := final, block := hfinal }
      have hvalue : value = chosen := by
        have hagree := head.action_congr sibling anchor rfl
        exact hresolved.trans hagree
      rw [← hvalue, ← hsource]
      apply hafter
      exact .step anchor.sourcePrefix hfinal
        (.binding anchor.fallback anchor.deadline anchor.selected value hsource hresolved) hnext
    _ = sourceAfter (anchor.current.current.source.cons chosen) := FinDist.bind_const _ _

end Vegas.ApplicationPlan.BindingDecision

/-- info: 'Vegas.ApplicationPlan.BindingDecision.continuation_bind'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.BindingDecision.continuation_bind
