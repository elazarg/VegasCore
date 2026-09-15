/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSettlementValues
import Vegas.Compile.SealedGuardSettlement
import Vegas.EventGraph.ValueRealization
import Interaction.SealedValidatedEvents

/-! # Legal graph realizations of validated public settlement

The native host validates ordinary openings and supplies the declared default
on timeout. Publicly checkable guards and legal defaults suffice to realize
every completed invariant settlement as a graph execution. Private candidate
contents need not be legal or match this realization. This is a support-level
result, not a policy or deviation-law simulation.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem terminal_readEnv {G : Graph Player L} {cfg : Config G}
    (hcoherent : StoreCoherent G cfg) (hterminal : Terminal G cfg)
    (refs : Finset (FieldRef L))
    (htyped : ∀ ref ∈ refs,
      ∃ spec, G.field? ref.field = some spec ∧ spec.ty = ref.ty) :
    ∃ env, ReadEnv.ofStore? cfg.store refs = some env := by
  have available : ∀ ref ∈ refs,
      ∃ value, Store.getAs cfg.store ref.field ref.ty = some value := by
    intro ref href
    obtain ⟨spec, hfield, hty⟩ := htyped ref href
    have hready : match spec.source with
        | .initial _ => True
        | .event writer => cfg.nodeDone writer := by
      cases hsource : spec.source with
      | initial value => trivial
      | event writer =>
          obtain ⟨_, hwriter⟩ := G.node_get_of_field_event_source hfield hsource
          have hlt : writer < G.nodeCount := (List.getElem?_eq_some_iff.mp hwriter).1
          exact Finset.mem_image.mpr ⟨⟨writer, hlt⟩, hterminal ⟨writer, hlt⟩, rfl⟩
    obtain ⟨value, hvalue⟩ := hcoherent ref.field spec hfield hready
    exact ⟨cast (congrArg L.Val hty) value,
      Store.getAs_cast cfg.store ref.field hty hvalue⟩
  exact ⟨ReadEnv.ofStore cfg.store refs available,
    by unfold ReadEnv.ofStore?; rw [dif_pos available]⟩

/-- Validated openings and legal defaults determine a reachable terminal
graph store. Guards may reject arbitrary other values. The statement uses
only graph metadata and actual public host invariants, not source syntax or
a pre-existing graph execution. -/
theorem validated_settlement_reachable (G : Graph Player L) {ty : L.Ty}
    (hwf : G.WF) (hrow : ∀ node, (G.nodeRow node).ty = ty)
    (hnoSamples : ∀ node dist, (G.nodeRow node).sem ≠ .sample dist)
    (hreveals : ∀ node source, (G.nodeRow node).sem = .reveal source →
      ∃ (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L),
        source = G.nodeTarget producer ∧ (G.nodeRow producer).sem = .commit who guard)
    (hunique : G.UniqueReveals)
    (hpublic : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
      guard.PubliclyValidatable G)
    (runtime : SealedResolution Player (L.Val ty))
    (hrules : runtime.program.rules = G.nodeOrder.map G.sealedRule)
    (hdefault : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
      ∀ hty : guard.ty = ty, ∀ reads,
        guard.eval (cast (congrArg L.Val hty.symm) runtime.nullValue) reads = true)
    (state : SealedResolution.PublicState Player (L.Val ty))
    (hevents : runtime.PublicEventInvariant state)
    (hhistory : runtime.OpeningHistoryInvariant (G.sealedOpeningValidator ty) state)
    (hcomplete : runtime.complete state = true) :
    Reachable G (G.settlementConfig runtime.nullValue (G.publicSealedStore ty state.events)) := by
  let store := G.publicSealedStore ty state.events
  let cfg := G.settlementConfig runtime.nullValue store
  have hterminal : Terminal G cfg := Config.canonicalCompletion_terminal G _
  have htyped : ∀ node : Fin G.nodeCount,
      (⟨ty, G.settlementValue runtime.nullValue store node⟩ : TypedValue L).ty =
        (G.nodeRow node).ty := fun node => (hrow node).symm
  have hcoherent : StoreCoherent G cfg :=
    Config.canonicalCompletion_storeCoherent G _ htyped
  have hagrees : ∀ ref, G.fieldRefPublic ref →
      Store.getAs cfg.store ref.field ref.ty = Store.getAs store ref.field ref.ty :=
    G.settlementConfig_public_store hwf hrow hnoSamples hreveals runtime.nullValue store
      (G.publicSealedStore_available_of_complete hwf hrow hnoSamples hreveals
        runtime hrules state hevents hcomplete)
      (G.publicSealedStore_getAs_initial ty state.events)
  apply Config.canonicalCompletion_reachable G hwf _ htyped
  intro node
  refine ⟨G.nodeRow node, G.nodes_get?_nodeRow node, ?_⟩
  cases hsem : (G.nodeRow node).sem with
  | sample dist => exact (hnoSamples node dist hsem).elim
  | commit owner guard =>
      have hnodeWF := hwf node (G.nodeRow node) (G.nodes_get?_nodeRow node)
      unfold Graph.nodeWFAt at hnodeWF
      rw [hsem] at hnodeWF
      have hguardType : guard.ty = ty := hnodeWF.2.1.symm.trans (hrow node)
      subst ty
      obtain ⟨reads, hreads⟩ := terminal_readEnv hcoherent hterminal guard.choiceReads
        (fun ref href => by
          obtain ⟨spec, hfield, hty, _⟩ := hnodeWF.2.2.2 ref href
          exact ⟨spec, hfield, hty⟩)
      refine ⟨G.settlementValue runtime.nullValue store node,
        G.settlementConfig_getAs runtime.nullValue store node, reads, hreads, ?_⟩
      by_cases found : ∃ reveal, (G.nodeRow reveal).sem = .reveal (G.nodeTarget node)
      · obtain ⟨reveal, hrev⟩ := found
        have hrule : runtime.program.rules[reveal.val]? =
            some ⟨.reveal owner node.val, G.messagePrerequisites reveal⟩ := by
          have hlookup : runtime.program.rules[reveal.val]? = some (G.sealedRule reveal) := by
            simp [hrules, Graph.nodeOrder]
          rw [hlookup, G.sealedRule_reveal_eq reveal node owner guard hrev hsem]
        have hdone : state.completed reveal.val = true := by
          apply List.all_eq_true.mp hcomplete reveal.val
          simp [hrules, Graph.nodeOrder]
        obtain ⟨value, hopened⟩ := hevents.opened_of_completed_reveal
          reveal.val owner node.val (G.messagePrerequisites reveal) hrule hdone
        have hsame : ∀ other, .opened reveal.val other ∈ state.events → other = value := by
          intro other hother
          have hinj := (List.nodup_map_iff_inj_on
            (hhistory.nodes_unique.of_map SealedProgram.Event.node)).mp hhistory.nodes_unique
          have heq := hinj (.opened reveal.val other) hother (.opened reveal.val value) hopened rfl
          exact SealedProgram.Event.opened.inj heq |>.2
        have hvalue := G.publicSealedStore_getAs_of_opened guard.ty state.events
          reveal.val value hopened hsame
        change guard.eval (G.settlementValue runtime.nullValue store node) reads = true
        rw [settlementValue, hsem,
          G.revealAssignment_reveal hunique runtime.nullValue store reveal node hrev]
        change guard.eval ((Store.getAs store (G.nodeTarget reveal) guard.ty).getD
          runtime.nullValue) reads = true
        rw [hvalue]
        apply G.opened_guard_legal reveal.val node.val owner guard
          ((G.node?_nodeRow reveal).trans (congrArg some hrev))
          ((G.node?_nodeRow node).trans (congrArg some hsem))
          runtime state hhistory (hdefault node owner guard hsem rfl) value hopened reads
        intro ref href
        rw [← hagrees ref (hpublic node owner guard hsem ref href)]
        exact ReadEnv.ofStore?_read hreads (guard.validationReads_subset href)
      · simpa [settlementValue, hsem, revealAssignment, found] using
          hdefault node owner guard hsem rfl reads
  | reveal source =>
      obtain ⟨producer, owner, guard, rfl, hcommit⟩ := hreveals node source hsem
      rw [hrow node]
      refine ⟨G.settlementValue runtime.nullValue store node,
        G.settlementConfig_getAs runtime.nullValue store node, ?_⟩
      change Store.getAs (G.settlementConfig runtime.nullValue store).store
        (G.nodeTarget producer) ty = some (G.settlementValue runtime.nullValue store node)
      rw [G.settlementConfig_getAs, settlementValue, hcommit,
        G.revealAssignment_reveal hunique runtime.nullValue store node producer hsem]
      simp [settlementValue, hsem]

/-- Every completed execution of arbitrary guarded native policies has the
public store of a legal terminal graph execution. This includes invalid
private candidates followed by timeout; it asserts no preservation of private
choices or opponents' policy laws. -/
theorem runPolicies_validated_settlement (G : Graph Player L) {ty : L.Ty}
    [DecidableEq (L.Val ty)]
    (hwf : G.WF) (hrow : ∀ node, (G.nodeRow node).ty = ty)
    (hnoSamples : ∀ node dist, (G.nodeRow node).sem ≠ .sample dist)
    (hreveals : ∀ node source, (G.nodeRow node).sem = .reveal source →
      ∃ (producer : Fin G.nodeCount) (who : Player) (guard : EventGuard L),
        source = G.nodeTarget producer ∧ (G.nodeRow producer).sem = .commit who guard)
    (hunique : G.UniqueReveals)
    (hpublic : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
      guard.PubliclyValidatable G)
    (runtime : SealedResolution Player (L.Val ty))
    (hrules : runtime.program.rules = G.nodeOrder.map G.sealedRule)
    (hdefault : ∀ node who guard, (G.nodeRow node).sem = .commit who guard →
      ∀ hty : guard.ty = ty, ∀ reads,
        guard.eval (cast (congrArg L.Val hty.symm) runtime.nullValue) reads = true)
    (players : Player →
      (runtime.guardedCandidateApplication (G.sealedOpeningValidator ty)).PlayerPolicy)
    (environment :
      (runtime.guardedCandidateApplication (G.sealedOpeningValidator ty)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : (runtime.guardedCandidateApplication (G.sealedOpeningValidator ty)).PolicyExecution)
    (hnext : next ∈
      ((runtime.guardedCandidateApplication (G.sealedOpeningValidator ty)).runPolicies
        players environment schedule
        (MessageApplication.PolicyExecution.initial _
          (MessageApplication.State.initial _ runtime.candidateInitial))).support)
    (hcomplete : runtime.complete next.native.application.visible = true) :
    ∃ cfg : ReachableConfig G, Terminal G cfg.1 ∧
      ∀ ref, G.fieldRefPublic ref →
        Store.getAs cfg.1.store ref.field ref.ty =
          Store.getAs (G.publicSealedStore ty next.native.application.visible.events)
            ref.field ref.ty := by
  have hevents := runtime.runPolicies_guarded_publicEvents (G.sealedOpeningValidator ty)
    players environment schedule _ next
    (SealedResolution.PublicEventInvariant.initial runtime) hnext
  have hhistory := runtime.runPolicies_guarded_openingHistory (G.sealedOpeningValidator ty)
    players environment schedule _ next (SealedResolution.OpeningHistoryInvariant.initial _ _) hnext
  refine ⟨⟨_, G.validated_settlement_reachable hwf hrow hnoSamples hreveals hunique hpublic
    runtime hrules hdefault _ hevents hhistory hcomplete⟩,
      Config.canonicalCompletion_terminal G _, ?_⟩
  exact G.settlementConfig_public_store hwf hrow hnoSamples hreveals runtime.nullValue _
    (G.publicSealedStore_available_of_complete hwf hrow hnoSamples hreveals
      runtime hrules _ hevents hcomplete)
    (G.publicSealedStore_getAs_initial ty _)

end Vegas.EventGraph.Graph

/-- info: 'Vegas.EventGraph.Graph.validated_settlement_reachable'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Graph.validated_settlement_reachable

/-- info: 'Vegas.EventGraph.Graph.runPolicies_validated_settlement'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.Graph.runPolicies_validated_settlement
