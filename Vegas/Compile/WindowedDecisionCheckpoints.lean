/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Core.SourcePolicyExtension
import Vegas.Compile.WindowedSourcePrivacy
import Vegas.Compile.WindowedBindingAction
import Vegas.Compile.WindowedPublicAction

/-! # Source decision kernels from actual windowed blocks

Representatives retain a supported prefix and its next complete native block.
Binding actions use the canonical frozen-value or fallback resolution; public
actions use the source value represented by the resulting public state.
Equal source observations determine equal extracted actions, so each family
defines a total legal source decision kernel. These are single-decision
kernels, not yet a whole-program deviation law.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable (root : ApplicationPlan rootAccounted rootFresh rootState)
variable (rootProfile : SourceBehavioralProfile rootProg) (deadlineOf : Nat → Nat)
variable (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
variable (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
variable (windowOf : Nat → Nat) (roster : List P) (owner : P)
variable (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
variable (initial : CoupledAt (compileCore rootProg rootFresh rootState).graph rootState)
variable (blockIndex : Nat) {name : VarId} {ty : L.Ty}
variable {guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx owner Γ)) L.bool}

section Binding

variable {tail : VegasCore P L ((name, .sealed owner ty) :: Γ)}
variable {newName : name ∉ pending}
variable {accounted : CommitmentAccounting (insert name pending) tail}
variable {fresh : FreshBindings (.commit name owner guard tail)} {state : BuildState P L Γ}
variable (unrestricted : UnrestrictedBinding guard)
variable (next : ApplicationPlan accounted fresh.2
  (state.addCommitEvent name owner guard fresh.1).1)
variable (profile : SourceBehavioralProfile (.commit name owner guard tail))

/-- An actual focal binding block, including the selected source-certified
fallback. The extracted value is a function of this evidence, not a free field. -/
structure BindingDecision where
  current : CoupledAt (compileCore (.commit name owner guard tail) fresh state).graph state
  execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution
  final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution
  sourcePrefix : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) owner
    replacement initial blockIndex (.binding (newName := newName) unrestricted next)
      profile current execution
  fallback : SourceDecisionSite.PublicFallback (.here guard tail)
  deadline : Nat
  selected : binding ((.here guard tail : SourceDecisionSite owner
    (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
      ((.here guard tail : SourceDecisionSite owner
        (.commit name owner guard tail) Γ name ty guard).compiledField fresh state)) =
    some ⟨deadline, fallback.compiled fresh state⟩
  block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
    ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
    (WindowedApplication.blockInvocations roster) execution).support

/-- Binding representatives define a legal decision kernel determined only by
the focal source view, including malformed submissions and timeout resolution. -/
def bindingDecisionCheckpoints
    (hinitial : root.InitialControllerReadsPublic)
    (horigins : (root.image deadlineOf).HasBindingOrigins)
    (hroster : roster.Nodup)
    (howners : ∀ instruction ∈ root.instructions deadlineOf,
      ∀ actor, instruction.submitter = some actor → actor ∈ roster)
    (command : List (root.windowed deadlineOf binding choice windowOf).application.PlayerEntry →
      (root.windowed deadlineOf binding choice windowOf).application.View →
        (root.windowed deadlineOf binding choice windowOf).application.PlayerCommand)
    (hpure : replacement = fun history view => FinDist.pure (command history view))
    (relay : P) (hrelay : relay ∈ roster) (hunchanged : relay ≠ owner) :
    SourceDecisionCheckpoints owner guard where
  Carrier := BindingDecision (newName := newName) root rootProfile deadlineOf binding choice
    windowOf roster owner replacement initial blockIndex unrestricted next profile
  visible witness := (witness.current.current.source.toView owner).eraseEnv
  action witness := ⟨BindingCode.resolvedValue
    ((.here guard tail : SourceDecisionSite owner
      (.commit name owner guard tail) Γ name ty guard).bindingCode fresh state
        ((.here guard tail : SourceDecisionSite owner
          (.commit name owner guard tail) Γ name ty guard).compiledField fresh state))
    (L.eval witness.fallback.expr witness.current.current.source.erasePubEnv)
    witness.final.native.application.base, unrestricted witness.current.current.source _⟩
  action_congr left right hview := by
    have agreement := WindowedSourcePrefix.policyAgreement_of_sourceView_eq
      (rootProfile := rootProfile) (initial := initial)
      (point := ⟨Γ, pending, .commit name owner guard tail,
        .commit newName accounted, fresh, state,
        .binding (newName := newName) unrestricted next, profile⟩)
      (leftCurrent := left.current) (rightCurrent := right.current)
      (left := left.execution) (right := right.execution)
      hinitial horigins hroster howners command hpure blockIndex
      left.sourcePrefix right.sourcePrefix hview
    exact left.sourcePrefix.checkpoint.binding_block_action_eq
      right.sourcePrefix.checkpoint agreement
      command hpure left.fallback right.fallback left.deadline right.deadline
      left.selected right.selected hroster relay hrelay hunchanged
      left.final right.final left.block right.block

end Binding

section Public

variable {publicName : VarId}
variable {tail : VegasCore P L ((publicName, .pub ty) :: (name, .sealed owner ty) :: Γ)}
variable {accounted : CommitmentAccounting pending
  (.commit name owner guard (.reveal publicName owner name .here tail))}
variable {fresh : FreshBindings (.commit name owner guard
  (.reveal publicName owner name .here tail))} {state : BuildState P L Γ}
variable (plan : ApplicationPlan accounted fresh state)
variable (profile : SourceBehavioralProfile
  (.commit name owner guard (.reveal publicName owner name .here tail)))

/-- A supported public decision block and its legal source value. This shared
representation covers ordinary choice and both conditional disclosure forms. -/
structure PublicDecision where
  current : CoupledAt (compileCore
    (.commit name owner guard (.reveal publicName owner name .here tail)) fresh state).graph state
  execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution
  final : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution
  sourcePrefix : WindowedSourcePrefix root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster) owner
    replacement initial blockIndex plan profile current execution
  value : L.Val ty
  legal : evalGuard guard value ((current.current.source.toView owner).eraseEnv) = true
  sourceNext : CoupledAt (compileCore tail fresh.2.2
    (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
      publicName owner .here fresh.2.1).1).graph
    (((state.addCommitEvent name owner guard fresh.1).1).addRevealEvent
      publicName owner .here fresh.2.1).1
  source : sourceNext.current.source = (current.current.source.cons value).cons value
  refines : final.native.application.base.Refines sourceNext.current.graph.1
  block : final ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
    (root.windowedPlayers rootProfile deadlineOf binding choice windowOf owner replacement)
    ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
    (WindowedApplication.blockInvocations roster) execution).support

/-- Actual public-decision representatives define one legal source kernel.
The source view fixes its value before the resolution block is run. -/
def publicDecisionCheckpoints
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
    (howner : instruction.submitter = some owner) : SourceDecisionCheckpoints owner guard where
  Carrier := PublicDecision root rootProfile deadlineOf binding choice windowOf roster owner
    replacement initial blockIndex plan profile
  visible witness := (witness.current.current.source.toView owner).eraseEnv
  action witness := ⟨witness.value, witness.legal⟩
  action_congr left right hview := by
    have agreement := WindowedSourcePrefix.policyAgreement_of_sourceView_eq
      (point := .of plan profile)
      hinitial horigins hroster howners command hpure blockIndex
      left.sourcePrefix right.sourcePrefix hview
    exact left.sourcePrefix.checkpoint.public_block_action_eq
      right.sourcePrefix.checkpoint agreement
      command hpure instruction rest hhead howner hroster
      left.final right.final left.block right.block left.value right.value
      left.sourceNext right.sourceNext left.source right.source left.refines right.refines

end Public
end Vegas.ApplicationPlan
