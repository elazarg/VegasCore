/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import Interaction.SealedKnowledge

/-! # Source-order knowledge before a focal commitment is registered

A compiled opening submitted before the focal registration must be earlier
in source order. All preceding commitments are prerequisites of that opening,
and native binding makes those prerequisites evidence of occupied slots.
This gives the known-handle predicate used by the causal replay proof.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Before a compiled opening can be submitted, every earlier commitment
has an immutable value, including commitments belonging to other players. -/
theorem openingReady_prior_commit_lookup (supported : SealedFragment G ty)
    (owner : Player) (node prior : Fin G.nodeCount)
    (state : (supported.compile.messageApplication (Value := L.Val ty)).State)
    (invariant : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts state))
    (hready : SealedProgram.openingReady supported.compile state.application.events
      owner node.val = true)
    (priorOwner : Player) (guard : EventGuard L)
    (hprior : (G.nodeRow prior).sem = .commit priorOwner guard)
    (hearlier : prior.val < node.val) :
    ∃ value, state.application.service.lookup (priorOwner, prior.val) = some value := by
  obtain ⟨source, requires, hrule, _hnotDone, hrequires, _haccepted⟩ :=
    SealedProgram.openingReady_sound supported.compile state.application.events
      owner node.val hready
  obtain ⟨actual, producer, _guard, hactual, _hproducer, hsem, _hcommit⟩ :=
    supported.ruleAt_reveal hrule rfl
  have heq : actual = node := Fin.ext hactual
  subst actual
  have hdep : prior ∈ G.prereqs node :=
    G.prior_commit_mem_prereqs_of_reveal (G.nodes_get?_nodeRow node)
      (G.nodes_get?_nodeRow prior) hearlier hsem hprior
  have hrequiresEq : G.messagePrerequisites node = requires :=
    congrArg SealedRule.requires (Option.some.inj ((supported.compile_rule node).symm.trans hrule))
  have hdone : SealedProgram.done state.application.events prior.val = true := by
    apply List.all_eq_true.mp hrequires prior.val
    rw [← hrequiresEq]
    exact (G.mem_messagePrerequisites node prior).mpr hdep
  have hpriorRule : supported.compile.rules[prior.val]? =
      some ⟨.commit priorOwner, G.messagePrerequisites prior⟩ := by
    rw [supported.compile_rule]
    apply congrArg some
    exact congrArg (fun kind => SealedRule.mk kind (G.messagePrerequisites prior))
      (G.sealedRule_commit prior priorOwner guard hprior)
  exact invariant.done_commit_lookup prior.val priorOwner _ hpriorRule hdone

/-- The focal principal's own slots and values disclosed before this source
decision. This predicate does not include future honest disclosures. -/
def knownBefore (supported : SealedFragment G ty) (focal : Player)
    (decision : Fin G.nodeCount) (handle : CommitmentHandle Player Nat) : Prop :=
  handle.1 = focal ∨ ∃ opening requires, opening < decision.val ∧
    supported.compile.rules[opening]? = some ⟨.reveal handle.1 handle.2, requires⟩

/-- Before the focal slot is registered, every opening allowed by the
compiler is a source-earlier disclosure. This is a submission-time fact. -/
theorem openingHandle?_knownBefore (supported : SealedFragment G ty)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (state : (supported.compile.messageApplication (Value := L.Val ty)).State)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts state))
    (hempty : state.application.service.lookup (focal, decision.val) = none)
    (owner : Player) (opening : Nat) (handle : CommitmentHandle Player Nat)
    (hhandle : supported.compile.openingHandle? state.application.events owner opening =
      some handle) : supported.knownBefore focal decision handle := by
  obtain ⟨source, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
    supported.compile state.application.events owner opening handle hhandle
  obtain ⟨requires, hrule, _, _, _⟩ := SealedProgram.openingHandle?_sound
    supported.compile state.application.events owner opening source hhandle
  obtain ⟨node, producer, producerGuard, hnode, _, hsem, _⟩ :=
    supported.ruleAt_reveal hrule rfl
  have hearlier : opening < decision.val := by
    by_contra hnot
    have hne : decision.val ≠ opening := by
      intro heq
      have hn : decision = node := Fin.ext (heq.trans hnode.symm)
      rw [← hn, hdecision] at hsem
      cases hsem
    have hlt : decision.val < node.val := by omega
    have hready : supported.compile.openingReady state.application.events
        owner node.val = true := by
      simp only [SealedProgram.openingReady, hnode, hhandle, Option.isSome_some]
    obtain ⟨value, hvalue⟩ := supported.openingReady_prior_commit_lookup owner node decision
      state hbinding hready focal guard hdecision hlt
    rw [hempty] at hvalue
    contradiction
  exact Or.inr ⟨opening, requires, hearlier, hrule⟩

/-- Every packet emitted by a compiled policy before the focal registration
meets the native knowledge relation's authenticated-opening condition. -/
theorem playerPolicy_openings_known (supported : SealedFragment G ty)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (hempty : execution.native.application.service.lookup (focal, decision.val) = none)
    (owner : Player) (policy : CommitPolicy G owner)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈ (supported.playerPolicy owner policy
      (execution.principalHistory owner)
      (MessageApplication.State.observe _ execution.native owner)).support) :
    SealedProgram.OpeningKnown (supported.knownBefore focal decision)
      ⟨(owner, execution.native.pool.nextSerial owner), payload⟩ := by
  rcases supported.playerPolicy_submission owner policy _ _ payload hsubmit with
    ⟨node, rfl⟩ | ⟨node, handle, value, rfl, hhandle⟩
  · trivial
  · intro _
    exact supported.openingHandle?_knownBefore focal decision guard hdecision
      execution.native hbinding hempty owner node handle hhandle

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.playerPolicy_openings_known' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.playerPolicy_openings_known
