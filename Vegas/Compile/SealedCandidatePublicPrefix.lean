/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicStore
import Interaction.SealedCandidatePublicPersistence

/-! # Public decision inputs persist through candidate continuations

Public reads of a ready commitment have already been disclosed. If their
included values agree with a retained graph realization, arbitrary subsequent
candidate traffic and deadline resolution preserve that agreement. The theorem
does not require normal completion of the continuation or inspect private
candidate meanings.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Public declared inputs at a normally ready commitment retain the values
of the same graph realization through every supported candidate continuation,
including one that later defaults. Initial public data needs no disclosure. -/
theorem candidate_publicRead_eq_of_prereqs_done
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (players : Player → (supported.resolvingRuntime
      nullValue window).candidateApplication.PlayerPolicy)
    (environment : (supported.resolvingRuntime
      nullValue window).candidateApplication.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (before after : (supported.resolvingRuntime
      nullValue window).candidateApplication.PolicyExecution)
    (hpublicEvents : SealedResolution.PublicEventInvariant
      (supported.resolvingRuntime nullValue window) before.native.application.visible)
    (hcontinuation : after ∈ ((supported.resolvingRuntime
      nullValue window).candidateApplication.runPolicies
        players environment schedule before).support)
    (node : Fin G.nodeCount) (who : Player) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hready : ∀ prior, prior ∈ G.prereqs node →
      SealedProgram.done before.native.application.visible.events prior.val = true)
    (cfg : ReachableConfig G)
    (hvalues : ∀ index value,
      SealedProgram.Event.opened index value ∈ before.native.application.visible.events →
        cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))
    (ref : FieldRef L) (href : ref ∈ guard.choiceReads) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty after.native.application.visible.events) ref.field ref.ty =
      Store.getAs cfg.1.store ref.field ref.ty := by
  let runtime := supported.resolvingRuntime nullValue window
  rcases G.publicField_origin supported.graphWF supported.rowType supported.noSamples
    supported.revealSource ref hpublic with
    ⟨spec, value, hfield, hsource, hty, howner⟩ |
      ⟨prior, producer, owner, priorGuard, htarget, hrefty, hreveal, hcommit⟩
  · rw [← hty, G.publicSealedStore_getAs_initial ty after.native.application.visible.events
      ref.field spec value hfield hsource howner]
    have hcfg := Graph.reachable_store_eq_initial_of_not_nodeTarget cfg.2 ref.field
      (fun node => G.initial_field_ne_target ref.field spec value hfield hsource node.val)
    simp [Store.getAs, hcfg, Graph.initialStore, hfield, FieldSpec.initialValue?,
      hsource, TypedValue.as?]
  · have hread : G.nodeTarget prior ∈ (G.nodeRow node).sem.reads := by
      rw [hsem]
      exact Finset.mem_image.mpr ⟨ref, href, htarget⟩
    have hlt : prior.val < node.val := by
      have havailable := (supported.graphWF node (G.nodeRow node)
        (G.nodes_get?_nodeRow node)).1 (G.nodeTarget prior) hread
      unfold Graph.fieldAvailableBefore at havailable
      rw [G.field?_nodeTarget (G.nodes_get?_nodeRow prior)] at havailable
      simpa using havailable
    have hprereq := G.nodeTarget_mem_prereqs_of_read (G.nodes_get?_nodeRow node)
      (G.nodes_get?_nodeRow prior) hlt hread
    have hdone := hready prior hprereq
    have hcompleted : before.native.application.visible.completed prior.val = true := by
      simp [SealedResolution.PublicState.completed, hdone]
    have hrule : runtime.program.rules[prior.val]? =
        some ⟨.reveal owner producer.val, G.messagePrerequisites prior⟩ := by
      rw [show runtime.program = supported.compile from rfl, supported.compile_rule]
      exact congrArg some
        (G.sealedRule_reveal_eq prior producer owner priorGuard hreveal hcommit)
    obtain ⟨value, hopened⟩ := hpublicEvents.opened_of_completed_reveal
      prior.val owner producer.val (G.messagePrerequisites prior) hrule hcompleted
    have hevents := runtime.runPolicies_candidate_events_at_done players environment schedule
      before after prior.val hdone hcontinuation
    have hmembership : ∀ value, SealedProgram.Event.opened prior.val value ∈
        after.native.application.visible.events ↔
      SealedProgram.Event.opened prior.val value ∈ before.native.application.visible.events := by
      intro value
      have hfiltered : SealedProgram.Event.opened prior.val value ∈
          after.native.application.visible.events.filter (fun event => event.node == prior.val) ↔
        SealedProgram.Event.opened prior.val value ∈
          before.native.application.visible.events.filter
            (fun event => event.node == prior.val) := by
        rw [hevents]
      simpa [List.mem_filter, SealedProgram.Event.node] using hfiltered
    have hfinalOpened := (hmembership value).mpr hopened
    have hsame : ∀ other, SealedProgram.Event.opened prior.val other ∈
        after.native.application.visible.events → other = value := by
      intro other hother
      have heq := Option.some.inj
        ((hvalues prior.val other ((hmembership other).mp hother)).symm.trans
          (hvalues prior.val value hopened))
      have htyped := congrArg (fun entry : TypedValue L => entry.as? ty) heq
      simpa [TypedValue.as?] using htyped
    rw [htarget, hrefty, G.publicSealedStore_getAs_of_opened ty
      after.native.application.visible.events prior.val value hfinalOpened hsame]
    simp [Store.getAs, hvalues prior.val value hopened, TypedValue.as?]

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidate_publicRead_eq_of_prereqs_done'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidate_publicRead_eq_of_prereqs_done
