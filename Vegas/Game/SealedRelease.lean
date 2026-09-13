/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedController
import Interaction.SealedPolicyBinding
import Vegas.Compile.SealedRules

/-! # Compiled opening release barrier

The generic opening controller can submit for a compiled reveal node only after
every graph prerequisite of that node is complete in its public runtime view.
Every source-earlier commitment is among those prerequisites. At a reachable
release checkpoint, its ideal-service slot is therefore occupied, and the
same value persists through any subsequent native policy execution. This is
an irrevocability result, not a source-policy backtranslation or a quit law.
-/

namespace Vegas.EventGraph.SealedFragment

open Interaction
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Any non-wait opening command for a compiled node certifies completion of
all of that graph node's prerequisites in the controller's public view. -/
theorem openingCommand_prerequisites (supported : SealedFragment G ty)
    [DecidableEq (L.Val ty)]
    (owner : Player) (node : Fin G.nodeCount) (value : L.Val ty)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hnonwait : SealedProgram.openingCommand supported.compile owner node.val value view ≠
      .wait) :
    ∀ prior, prior ∈ G.prereqs node →
      SealedProgram.done view.application prior.val = true := by
  obtain ⟨source, requires, _hcommand, hrule, _hnotDone, hrequires, _haccepted⟩ :=
    SealedProgram.openingCommand_ne_wait_sound supported.compile owner node.val value view
      hnonwait
  have hcompiled := supported.compile_rule node
  have hruleEq : G.sealedRule node =
      { kind := .reveal owner source, requires := requires } :=
    Option.some.inj (hcompiled.symm.trans hrule)
  have hrequiresEq : G.messagePrerequisites node = requires :=
    congrArg SealedRule.requires hruleEq
  rw [← hrequiresEq] at hrequires
  intro prior hprior
  apply List.all_eq_true.mp hrequires prior.val
  exact (G.mem_messagePrerequisites node prior).2 hprior

/-! The binding invariant converts public completion into private value
fixation. The proof reads the ideal service; neither the opening policy nor
its public readiness test does so. -/

/-- Before a compiled opening can be submitted, every earlier commitment
has an immutable value, including commitments belonging to other players. -/
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

/-- On any actual policy trace, the first opening-ready checkpoint fixes all
earlier commitments through the end of that same trace. The environment and
all player policies may be randomized and adaptive; replay, malformed
messages, delivery, and inclusion remain available in the suffix.

Readiness need not be reached. The explicit `hready` premise selects traces
on which an opening can be published; no fairness assumption is smuggled into
this safety theorem. -/
theorem opening_barrier_trace (supported : SealedFragment G ty)
    [DecidableEq (L.Val ty)]
    (owner : Player) (node prior : Fin G.nodeCount)
    (players : Player → (supported.compile.messageApplication (Value := L.Val ty)).PlayerPolicy)
    (environment : (supported.compile.messageApplication (Value := L.Val ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (state : (supported.compile.messageApplication (Value := L.Val ty)).State)
    (invariant : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts state))
    (trace : (supported.compile.messageApplication (Value := L.Val ty)).PolicyTrace)
    (htrace : trace ∈ ((supported.compile.messageApplication (Value := L.Val ty)).tracePolicies
      players environment schedule (MessageApplication.PolicyExecution.initial _ state)).support)
    (hready : SealedProgram.openingReady supported.compile
      (trace.firstRelease (fun (execution :
        (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution) =>
        SealedProgram.openingReady supported.compile
        execution.native.application.events owner node.val)).native.application.events
          owner node.val = true)
    (priorOwner : Player) (guard : EventGuard L)
    (hprior : (G.nodeRow prior).sem = .commit priorOwner guard)
    (hearlier : prior.val < node.val) :
    ∃ value,
      (trace.firstRelease (fun (execution :
        (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution) =>
        SealedProgram.openingReady supported.compile
        execution.native.application.events owner node.val)).native.application.service.lookup
          (priorOwner, prior.val) = some value ∧
      trace.last.native.application.service.lookup (priorOwner, prior.val) = some value := by
  let release := fun execution :
      (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution =>
    SealedProgram.openingReady supported.compile execution.native.application.events owner node.val
  have hbinding := SealedProgram.tracePolicies_firstRelease_bindingInvariant supported.compile
    players environment release schedule state trace invariant htrace
  obtain ⟨value, hvalue⟩ := supported.openingReady_prior_commit_lookup owner node prior
    (trace.firstRelease release).native hbinding hready priorOwner guard hprior hearlier
  refine ⟨value, hvalue, ?_⟩
  exact SealedProgram.tracePolicies_firstRelease_lookup_persists supported.compile
    players environment release schedule (MessageApplication.PolicyExecution.initial _ state)
    trace (priorOwner, prior.val) value htrace hvalue

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.opening_barrier_trace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.opening_barrier_trace
