/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedOwnedCheckpoint
import Vegas.Compile.WindowedBindingCheckpoint
import Vegas.Compile.WindowedBindingBlock
import Vegas.Core.SourceRecall

/-! # Locality of focal binding actions

The canonical binding value is determined by focal-observable application
state. The opaque case uses generated-handle provenance to select the focal
snapshot retained by `AgreesFor`; public defaults are already public memory.
-/

noncomputable section

namespace Vegas.BindingCode

open EventGraph

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
/-- Canonical resolved binding values agree in focal-related completed states.
The resolved-binding invariant rules out an opaque handle belonging to another
principal or slot at this generated instruction. -/
theorem resolvedValue_eq_of_agreesFor
    (code : BindingCode P L) (image : ApplicationImage P L)
    (left right : ApplicationImage.State P L)
    (agreement : left.AgreesFor code.owner right)
    (leftResolved : image.ResolvedBindings left)
    (hcode : .bind code ∈ image.instructions)
    (hdone : left.memory.done code.node = true)
    (leftFallback rightFallback : L.Val code.ty)
    (hfallback : leftFallback = rightFallback) :
    code.resolvedValue leftFallback left =
      code.resolvedValue rightFallback right := by
  obtain ⟨leftDisposition, hleftAccepted, hleftCanonical⟩ :=
    leftResolved code hcode hdone
  have hrightAccepted : right.memory.accepted code.sourceField = some leftDisposition := by
    rw [← agreement.memory]
    exact hleftAccepted
  cases leftDisposition with
  | publicDefault typed =>
      simp [resolvedValue, hleftAccepted, hrightAccepted, hfallback]
  | «opaque» handle =>
      have hhandle : handle = (code.owner, code.sourceSlot) :=
        hleftCanonical handle rfl
      subst handle
      have hfrozen := agreement.frozen code.sourceField code.sourceSlot hleftAccepted
      simp [resolvedValue, hleftAccepted, hrightAccepted, hfrozen, hfallback]

end Vegas.BindingCode

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
variable {blockIndex : Nat} {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}
variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}
variable {unrestricted : UnrestrictedBinding guard}
variable {nextPlan : ApplicationPlan accounted fresh.2
  (state.addCommitEvent name owner guard fresh.1).1}
variable {profile : SourceBehavioralProfile (.commit name owner guard tail)}
variable {leftCurrent rightCurrent :
  CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state}
variable {left right :
  (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}

/-- Focal binding action extraction agrees across two actual complete blocks
whenever the preceding focal inputs agree. Raw commands,
malformed commitments, and timeout resolution remain unrestricted. The whole
source-prefix information theorem must supply the preceding agreement. Distinct
source fallback certificates are compared through the single selected compiled
fallback code, rather than by identifying their source expressions. -/
theorem binding_block_action_eq
    (leftCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      owner replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile leftCurrent left)
    (rightCheckpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf roster
      owner replacement blockIndex (.binding (newName := newName) unrestricted nextPlan)
        profile rightCurrent right)
    (agreement : WindowedApplication.PolicyAgreement
      (root.windowed deadlineOf binding choice windowOf) owner left right)
    (command :
      List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
        (root.windowed deadlineOf binding choice windowOf).application.View →
          (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (leftFallback rightFallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (leftDeadline rightDeadline : Nat)
    (hleftSelect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨leftDeadline, leftFallback.compiled fresh state⟩)
    (hrightSelect : binding ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
      some ⟨rightDeadline, rightFallback.compiled fresh state⟩)
    (hroster : roster.Nodup) (relay : P) (hrelay : relay ∈ roster) (hunchanged : relay ≠ owner)
    (finalLeft finalRight :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hleft : finalLeft ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) left).support)
    (hright : finalRight ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
        ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
        (WindowedApplication.blockInvocations roster) right).support) :
    let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
      .here guard tail
    let code := site.bindingCode fresh state (site.compiledField fresh state)
    code.resolvedValue (L.eval leftFallback.expr leftCurrent.current.source.erasePubEnv)
      finalLeft.native.application.base =
    code.resolvedValue (L.eval rightFallback.expr rightCurrent.current.source.erasePubEnv)
      finalRight.native.application.base := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let site : SourceDecisionSite owner (.commit name owner guard tail) Γ name ty guard :=
    .here guard tail
  let code := site.bindingCode fresh state (site.compiledField fresh state)
  let timed : BindingCode P L := { code with timeout := binding code }
  let plan := ApplicationPlan.binding (newName := newName) (fresh := fresh) unrestricted nextPlan
  have hhead : plan.instructions deadlineOf =
      .bind code :: nextPlan.instructions deadlineOf := rfl
  have hfinalAgreement := leftCheckpoint.owned_block_agreement rightCheckpoint agreement
    command hpure (.bind code) (nextPlan.instructions deadlineOf) hhead rfl
    hroster finalLeft finalRight hleft hright
  have hrelayReference :
      root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement relay =
        root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf relay := by
    simp only [windowedPlayers, Function.update_of_ne hunchanged]
  obtain ⟨value, sourceNext, _, nextCheckpoint, _, _, _⟩ :=
    binding_block unrestricted nextPlan profile leftFallback leftDeadline hleftSelect
      leftCurrent left
      finalLeft leftCheckpoint hroster relay hrelay hrelayReference hleft
  have hmemOriginal : .bind code ∈ root.instructions deadlineOf :=
    List.mem_of_getElem? (leftCheckpoint.instruction_at _ _ hhead)
  have hmem : .bind timed ∈ runtime.image.instructions := by
    change .bind timed ∈ ((root.instructions deadlineOf).map
      (ApplicationInstruction.withBindingTimeouts binding)).map
      (ApplicationInstruction.withChoiceTimeouts choice)
    apply List.mem_map.mpr
    refine ⟨.bind timed, ?_, rfl⟩
    exact List.mem_map.mpr ⟨.bind code, hmemOriginal, rfl⟩
  have hdone : finalLeft.native.application.base.memory.done timed.node = true := by
    apply (nextCheckpoint.refines.memory.completed (site.compiledNode fresh state)).mpr
    rw [sourceNext.completedPrefix]
    change state.nodes.length < (state.addCommitEvent name owner guard fresh.1).1.nodes.length
    simp only [BuildState.addCommitEvent_nodes, List.length_append, List.length_singleton]
    omega
  have hselected :
      (⟨leftDeadline, leftFallback.compiled fresh state⟩ : PublicFallbackCode L ty) =
        ⟨rightDeadline, rightFallback.compiled fresh state⟩ :=
    Option.some.inj (hleftSelect.symm.trans hrightSelect)
  have hcompiled : leftFallback.compiled fresh state = rightFallback.compiled fresh state :=
    congrArg PublicFallbackCode.value hselected
  have hleftEval := leftFallback.compiled_evalStore?_eq_source fresh state
    leftCurrent.current.graph.1.store left.native.application.base.memory.store
    leftCurrent.current.source leftCurrent.current.agrees (fun ref href =>
      leftCheckpoint.refines.memory.publicFields ref
        (leftFallback.compiled_reads_public fresh state ref href))
  have hrightEval := rightFallback.compiled_evalStore?_eq_source fresh state
    rightCurrent.current.graph.1.store right.native.application.base.memory.store
    rightCurrent.current.source rightCurrent.current.agrees (fun ref href =>
      rightCheckpoint.refines.memory.publicFields ref
        (rightFallback.compiled_reads_public fresh state ref href))
  have hevalCode :
      (leftFallback.compiled fresh state).evalStore?
          left.native.application.base.memory.store =
        (rightFallback.compiled fresh state).evalStore?
          right.native.application.base.memory.store := by
    rw [hcompiled, agreement.state.base.memory]
  have hfallback : L.eval leftFallback.expr leftCurrent.current.source.erasePubEnv =
      L.eval rightFallback.expr rightCurrent.current.source.erasePubEnv :=
    Option.some.inj (hleftEval.symm.trans (hevalCode.trans hrightEval))
  exact timed.resolvedValue_eq_of_agreesFor runtime.image
    finalLeft.native.application.base finalRight.native.application.base
    hfinalAgreement.state.base nextCheckpoint.resolvedBindings hmem hdone _ _
    hfallback

end Vegas.ApplicationPlan.WindowedCheckpoint

/-- info: 'Vegas.BindingCode.resolvedValue_eq_of_agreesFor' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.BindingCode.resolvedValue_eq_of_agreesFor

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_action_eq' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.binding_block_action_eq
