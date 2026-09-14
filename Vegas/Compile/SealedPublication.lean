/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import Interaction.SealedKnowledge

/-! # Source-order knowledge before public commitment acceptance

A compiled opening submitted before the focal commitment is complete must be
earlier in source order. This follows from the public prerequisite log alone;
it does not require the focal private registration slot to be empty. Native
binding separately turns completed commitment prerequisites into stored values.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Before a compiled opening can be submitted, every earlier commitment is
complete in the public log. No private service state or value invariant is used. -/
theorem openingReady_prior_commit_done (supported : SealedFragment G ty)
    (owner : Player) (node prior : Fin G.nodeCount)
    (events : List (SealedProgram.Event Player (L.Val ty)))
    (hready : SealedProgram.openingReady supported.compile events
      owner node.val = true)
    (priorOwner : Player) (guard : EventGuard L)
    (hprior : (G.nodeRow prior).sem = .commit priorOwner guard)
    (hearlier : prior.val < node.val) :
    SealedProgram.done events prior.val = true := by
  obtain ⟨source, requires, hrule, _hnotDone, hrequires, _haccepted⟩ :=
    SealedProgram.openingReady_sound supported.compile events
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
  apply List.all_eq_true.mp hrequires prior.val
  rw [← hrequiresEq]
  exact (G.mem_messagePrerequisites node prior).mpr hdep

/-- The current registered-handle functionality turns public commitment
completion into a stored value. This is separate from the publication barrier. -/
theorem openingReady_prior_commit_lookup (supported : SealedFragment G ty)
    [DecidableEq (L.Val ty)]
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
  apply invariant.done_commit_lookup prior.val priorOwner (G.messagePrerequisites prior)
  · rw [supported.compile_rule, G.sealedRule_commit_eq prior priorOwner guard hprior]
  · exact supported.openingReady_prior_commit_done owner node prior state.application.events
      hready priorOwner guard hprior hearlier

/-- In the registered-handle functionality, absence of a private value rules
out public completion of the corresponding commitment. -/
theorem commit_not_done_of_lookup_none (supported : SealedFragment G ty)
    (owner : Player) (node : Fin G.nodeCount) (guard : EventGuard L)
    (hnode : (G.nodeRow node).sem = .commit owner guard)
    (state : SealedProgram.State Player (L.Val ty))
    (invariant : SealedProgram.BindingInvariant supported.compile state)
    (hempty : state.service.lookup (owner, node.val) = none) :
    SealedProgram.done state.events node.val = false := by
  cases hdone : SealedProgram.done state.events node.val with
  | false => rfl
  | true =>
      have hrule : supported.compile.rules[node.val]? =
          some ⟨.commit owner, G.messagePrerequisites node⟩ := by
        rw [supported.compile_rule, G.sealedRule_commit_eq node owner guard hnode]
      obtain ⟨value, hvalue⟩ := invariant.done_commit_lookup node.val owner _ hrule hdone
      rw [hempty] at hvalue
      contradiction

/-- The focal principal's own slots and values disclosed before this source
decision. This predicate does not include future honest disclosures. -/
def knownBefore (supported : SealedFragment G ty) (focal : Player)
    (decision : Fin G.nodeCount) (handle : CommitmentHandle Player Nat) : Prop :=
  handle.1 = focal ∨ ∃ opening requires, opening < decision.val ∧
    supported.compile.rules[opening]? = some ⟨.reveal handle.1 handle.2, requires⟩

/-- Before the focal commitment is publicly complete, every allowed opening
is a source-earlier disclosure. Private registrations are unrestricted by this
lemma. This is a submission-time fact, not merely an inclusion check. -/
theorem openingHandle?_knownBefore (supported : SealedFragment G ty)
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (events : List (SealedProgram.Event Player (L.Val ty)))
    (hnotDone : SealedProgram.done events decision.val = false)
    (owner : Player) (opening : Nat) (handle : CommitmentHandle Player Nat)
    (hhandle : supported.compile.openingHandle? events owner opening =
      some handle) : supported.knownBefore focal decision handle := by
  obtain ⟨source, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
    supported.compile events owner opening handle hhandle
  obtain ⟨requires, hrule, _, _, _⟩ := SealedProgram.openingHandle?_sound
    supported.compile events owner opening source hhandle
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
    have hready : supported.compile.openingReady events
        owner node.val = true := by
      simp only [SealedProgram.openingReady, hnode, hhandle, Option.isSome_some]
    have hdone := supported.openingReady_prior_commit_done owner node decision
      events hready focal guard hdecision hlt
    rw [hnotDone] at hdone
    contradiction
  exact Or.inr ⟨opening, requires, hearlier, hrule⟩

/-- Every packet emitted by a compiled policy before the focal commitment completes
meets the native knowledge relation's authenticated-opening condition. -/
theorem playerPolicy_openings_known (supported : SealedFragment G ty)
    [DecidableEq (L.Val ty)]
    (focal : Player) (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hnotDone : SealedProgram.done execution.native.application.events decision.val = false)
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
      execution.native.application.events hnotDone owner node handle hhandle

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.playerPolicy_openings_known' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.playerPolicy_openings_known
