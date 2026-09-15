/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.SealedCandidatePrerequisites
import Vegas.Compile.SealedRules
import Vegas.Compile.SealedResolutionPolicy

/-! # Producer prerequisites before the first timeout

A compiled rule ready in the normal event log is owned by a commitment
producer.  For a reveal, normal readiness forces that producer to have an
accepted event.  Candidate admission then retains the producer's own normally
completed prerequisites.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}

/-- Before the first timeout, normal readiness of a compiled timeout node
includes normal readiness of the commitment producer that owns it.  In the
reveal case this uses only the direct producer prerequisite, not a transitive
closure assumption. -/
theorem ready_node_producer_prerequisites
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (pre : SealedResolution.PublicState Player (L.Val ty))
    (hpublic : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) pre)
    (hcandidates : SealedResolution.CandidatePrerequisiteInvariant
      (supported.resolvingRuntime nullValue window) pre)
    (hclear : pre.timeouts = []) (timeoutNode : Fin G.nodeCount)
    (rule : SealedRule Player)
    (hrule : (supported.resolvingRuntime nullValue window).program.rules[timeoutNode.val]? =
      some rule)
    (hrequires : rule.requires.all (SealedProgram.done pre.events) = true) :
    ∃ (producer : Fin G.nodeCount) (owner : Player) (guard : EventGuard L),
      (G.nodeRow producer).sem = .commit owner guard ∧
      (timeoutNode = producer ∨
        (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget producer)) ∧
      ∀ prior, prior ∈ G.prereqs producer →
        SealedProgram.done pre.events prior.val = true := by
  change supported.compile.rules[timeoutNode.val]? = some rule at hrule
  have hruleEq : G.sealedRule timeoutNode = rule :=
    Option.some.inj ((supported.compile_rule timeoutNode).symm.trans hrule)
  subst rule
  obtain ⟨owner, ⟨guard, hcommit⟩ | ⟨producer, guard, hreveal, hproducer⟩⟩ :=
    supported.node_owner timeoutNode
  · refine ⟨timeoutNode, owner, guard, hcommit, Or.inl rfl, ?_⟩
    rw [G.sealedRule_commit_eq timeoutNode owner guard hcommit] at hrequires
    intro prior hprior
    exact List.all_eq_true.mp hrequires prior.val
      ((G.mem_messagePrerequisites timeoutNode prior).mpr hprior)
  · refine ⟨producer, owner, guard, hproducer, Or.inr hreveal, ?_⟩
    rw [G.sealedRule_reveal_eq timeoutNode producer owner guard hreveal hproducer]
      at hrequires
    have hlt : producer.val < timeoutNode.val := by
      have hnodeWF := supported.graphWF timeoutNode (G.nodeRow timeoutNode)
        (G.nodes_get?_nodeRow timeoutNode)
      have havailable := hnodeWF.1 (G.nodeTarget producer)
        (by simp [hreveal, NodeSem.reads])
      unfold Graph.fieldAvailableBefore at havailable
      rw [G.field?_nodeTarget (G.nodes_get?_nodeRow producer)] at havailable
      simpa using havailable
    have hproducerPrerequisite : producer ∈ G.prereqs timeoutNode :=
      G.nodeTarget_mem_prereqs_of_read (G.nodes_get?_nodeRow timeoutNode)
        (G.nodes_get?_nodeRow producer) hlt (by simp [hreveal, NodeSem.reads])
    have hproducerDone : SealedProgram.done pre.events producer.val = true :=
      List.all_eq_true.mp hrequires producer.val
        ((G.mem_messagePrerequisites timeoutNode producer).mpr hproducerPrerequisite)
    have hproducerRule :
        (supported.resolvingRuntime nullValue window).program.rules[producer.val]? =
          some ⟨.commit owner, G.messagePrerequisites producer⟩ := by
      change supported.compile.rules[producer.val]? = _
      rw [supported.compile_rule,
        G.sealedRule_commit_eq producer owner guard hproducer]
    have hacceptedSome : (SealedProgram.accepted? pre.events producer.val).isSome = true :=
      (hpublic.done_eq_accepted_isSome
        (supported.resolvingRuntime nullValue window) producer.val owner
        (G.messagePrerequisites producer) hproducerRule).symm.trans hproducerDone
    obtain ⟨handle, haccepted⟩ := Option.isSome_iff_exists.mp hacceptedSome
    have hacceptedMem : SealedProgram.Event.accepted producer.val handle ∈ pre.events :=
      SealedProgram.accepted_mem_of_accepted?_eq_some haccepted
    obtain ⟨candidateOwner, candidateRequires, hcandidateRule, hcandidateRequires⟩ :=
      hcandidates producer.val handle hacceptedMem
    have hrequiresEq : candidateRequires = G.messagePrerequisites producer :=
      congrArg SealedRule.requires
        (Option.some.inj (hcandidateRule.symm.trans hproducerRule))
    intro prior hprior
    have hcompleted := List.all_eq_true.mp hcandidateRequires prior.val
      (hrequiresEq.symm ▸ (G.mem_messagePrerequisites producer prior).mpr hprior)
    simpa [SealedResolution.PublicState.completed, hclear] using hcompleted

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.ready_node_producer_prerequisites' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.ready_node_producer_prerequisites
