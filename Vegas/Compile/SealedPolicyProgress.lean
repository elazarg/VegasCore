/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolvedReads
import Vegas.EventGraph.TopologicalOrder
import Interaction.SealedResolutionClosure
import Interaction.SealedResolutionSubmission
import Interaction.SealedResolutionRounds

/-! # Protocol progress of compiled sealed policies

At a snapshot with public event provenance and the owner's accepted-value
cache, a selected honest node prepares a choice, submits its commitment, or
opens its cached value. Timeout defaults do not invalidate the declared reads.
Both commitment hosts use this selector proof. The exact finite selected node
and cache phase are retained for deadline charging.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- An emitted registration uses an empty native slot, including after timeout
resolution. This fact needs only exact own-command memory. -/
theorem resolvingPolicy_registration_fresh (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      (supported.resolvingPolicy nullValue window who policy (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)).support) :
    execution.native.application.service.lookup (who, slot) = none := by
  let runtime := supported.resolvingRuntime nullValue window
  let history := runtime.eventHistory (execution.principalHistory who)
  let view := runtime.eventView (MessageApplication.State.observe _ execution.native who)
  let store := supported.resolvedPlayerStore who nullValue
    execution.native.application.visible.timeouts history view
  obtain ⟨node, guard, hsem, reads, hslot, hcache, _⟩ :=
    supported.selected_registration_kernel who execution.native.application.visible.timeouts
      policy history view store slot value hcommand
  rw [hslot, hmemory who node.val]
  exact (runtime.eventHistory_cache (runtime.program.registrationEncoding node.val)
    (execution.principalHistory who)).symm.trans hcache

/-- Once a slot is occupied, arbitrary intervening native policies cannot make
the compiled policy register it again. This supplies the one-registration
charge per source commitment without assuming a fixed selected node. -/
theorem runPolicies_no_reregistration (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat)
    (players : Player →
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next :
      (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hmemory : SealedResolution.RegistrationMemory (supported.resolvingRuntime nullValue window)
      execution)
    (who : Player) (slot : Nat) (stored : L.Val ty)
    (hlookup : execution.native.application.service.lookup (who, slot) = some stored)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).messageApplication.runPolicies
      players environment schedule execution).support)
    (policy : CommitPolicy G who) (value : L.Val ty) :
    .privateCommand ⟨(slot, value)⟩ ∉
      (supported.resolvingPolicy nullValue window who policy (next.principalHistory who)
        (MessageApplication.State.observe _ next.native who)).support := by
  let runtime := supported.resolvingRuntime nullValue window
  have hretained := runtime.runPolicies_lookup_of_eq_some players environment schedule
    execution next (who, slot) stored hlookup hnext
  have hnextMemory := SealedResolution.RegistrationMemory.runPolicies players environment
    schedule execution next hmemory hnext
  intro hcommand
  have hfresh := supported.resolvingPolicy_registration_fresh nullValue window who policy
    next hnextMemory slot value hcommand
  rw [hretained] at hfresh
  contradiction

/-- The three honest protocol phases at the exact selected graph site. -/
inductive ProgressCommand (supported : SealedFragment G ty) (who : Player)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry) :
    Fin G.nodeCount →
      (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand → Prop where
  | registration (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = none) :
      ProgressCommand supported who history node (.privateCommand ⟨(node.val, value)⟩)
  | commitment (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = some value) :
      ProgressCommand supported who history node
        (.submit (.commitment node.val (who, node.val)))
  | opening (node producer : Fin G.nodeCount) (guard : EventGuard L)
      (hnode : (G.nodeRow node).sem = .reveal (G.nodeTarget producer))
      (hproducer : (G.nodeRow producer).sem = .commit who guard)
      (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding producer.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = some value) :
      ProgressCommand supported who history node
        (.submit (.opening node.val (who, producer.val) value))

/-- A selected node performs a protocol phase at that same finite site.
The statement also retains its public readiness, including after defaults. -/
theorem nodeCommand_progress (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (nativeHistory : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (nativeView : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (hpublic : SealedResolution.PublicEventInvariant (supported.resolvingRuntime nullValue window)
      nativeView.application)
    (hownCache : supported.OwnCommitCache who nativeView.application.events
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory))
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who nativeView.application.timeouts policy
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory)
      ((supported.resolvingRuntime nullValue window).eventView
        nativeView)
      (supported.resolvedPlayerStore who nullValue nativeView.application.timeouts
        ((supported.resolvingRuntime nullValue window).eventHistory
          nativeHistory)
        ((supported.resolvingRuntime nullValue window).eventView
          nativeView)) node = some law) :
    nativeView.application.completed node.val = false ∧
      (G.messagePrerequisites node).all nativeView.application.completed = true ∧
      ∀ command ∈ law.support,
        ProgressCommand supported who
          ((supported.resolvingRuntime nullValue window).eventHistory
            nativeHistory) node command := by
  let runtime := supported.resolvingRuntime nullValue window
  let history := runtime.eventHistory nativeHistory
  let view := runtime.eventView nativeView
  let store := supported.resolvedPlayerStore who nullValue
    nativeView.application.timeouts history view
  change supported.nodeCommand? who nativeView.application.timeouts
    policy history view store node = some law at hselected
  change _ ∧ _ ∧ ∀ command ∈ law.support, ProgressCommand supported who history node command
  unfold nodeCommand? at hselected
  split at hselected
  · contradiction
  next htimeout =>
    split at hselected
    next hready =>
      have hdone : SealedProgram.done nativeView.application.events
          node.val = false := hready.1
      have hrequires : (G.messagePrerequisites node).all
          nativeView.application.completed = true := by
        have h := (nativeView.application.prerequisitesDone_discharge
          (G.sealedRule node)).symm.trans hready.2
        simpa only [Graph.sealedRule] using h
      refine ⟨?_, hrequires, ?_⟩
      · exact Bool.or_eq_false_iff.mpr ⟨hdone, Bool.eq_false_of_not_eq_true htimeout⟩
      · split at hselected
        next owner guard hsem =>
          split at hselected
          next howner =>
            subst owner
            rw [← Option.some.inj hselected]
            cases hcache : (supported.compile.registrationEncoding node.val).cachedValue
                (supported.compile.messageApplication (Value := L.Val ty)) history with
            | some value =>
                intro command hcommand
                have heq : command = .submit (.commitment node.val (who, node.val)) := by
                  simpa only [commitCommand, hcache, FinDist.mem_support_pure] using hcommand
                subst command
                exact .commitment node guard hsem value hcache
            | none =>
                obtain ⟨reads, hreads⟩ := supported.resolvedPlayerStore_reads_of_ready
                  nullValue window who nativeHistory nativeView hpublic hownCache node guard
                  hsem hrequires
                change ReadEnv.ofStoreExec? store guard.choiceReads = some reads at hreads
                intro command hcommand
                rw [commitCommand, hcache, hreads, FinDist.support_map] at hcommand
                obtain ⟨choice, _, rfl⟩ := hcommand
                exact .registration node guard hsem _ hcache
          next => contradiction
        next source hsem =>
          let discharged :=
            supported.compile.discharge nativeView.application.timeouts
          change (discharged.openingHandle? view.application who node.val).map _ = some law
            at hselected
          cases hhandle : discharged.openingHandle? view.application who node.val with
          | none => simp only [hhandle, Option.map_none] at hselected; contradiction
          | some handle =>
              obtain ⟨sourceSlot, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
                discharged view.application who node.val handle hhandle
              obtain ⟨requires, hrule, _, _, haccepted⟩ := SealedProgram.openingHandle?_sound
                discharged view.application who node.val sourceSlot hhandle
              have hkind : (G.sealedRule node).kind = .reveal who sourceSlot := by
                change (supported.compile.discharge _).rules[node.val]? = _ at hrule
                simp only [SealedProgram.discharge, List.getElem?_map, supported.compile_rule,
                  Option.map_some, Option.some.injEq] at hrule
                exact congrArg SealedRule.kind hrule
              obtain ⟨revealNode, producer, guard, hrevealIndex, hproducerIndex,
                  hreveal, hproducer⟩ :=
                supported.ruleAt_reveal (supported.compile_rule node) hkind
              have hrevealNode : revealNode = node := Fin.ext hrevealIndex
              subst revealNode
              have hdone : SealedProgram.done nativeView.application.events producer.val = true :=
                hproducerIndex.symm ▸ SealedProgram.done_of_accepted _ sourceSlot (who, sourceSlot)
                  (SealedProgram.accepted_mem_of_accepted?_eq_some haccepted)
              obtain ⟨value, _, hcache⟩ := hownCache producer guard hproducer hdone
              rw [hproducerIndex] at hcache
              change (supported.compile.registrationEncoding sourceSlot).cachedValue
                (supported.compile.messageApplication (Value := L.Val ty)) history = some value
                at hcache
              intro command hcommand
              rw [hhandle] at hselected
              simp only [Option.map_some, hcache] at hselected
              rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hcommand
              subst command
              have hsourceSlot : producer.val = sourceSlot := hproducerIndex
              subst sourceSlot
              exact .opening node producer guard hreveal hproducer value hcache
        next dist hsem => exact (supported.noSamples node dist hsem).elim
    next => contradiction

/-- A ready unfinished reveal uses an actually accepted producer. If the
producer had defaulted instead, propagation would already complete the reveal. -/
theorem ready_reveal_source_accepted (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player)
    (nativeHistory : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (nativeView : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (hownCache : supported.OwnCommitCache who nativeView.application.events
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory))
    (hclosed : nativeView.application.ResolutionClosed
      (supported.resolvingRuntime nullValue window))
    (node producer : Fin G.nodeCount) (guard : EventGuard L)
    (hreveal : (G.nodeRow node).sem = .reveal (G.nodeTarget producer))
    (hproducer : (G.nodeRow producer).sem = .commit who guard)
    (hnotDone : nativeView.application.completed node.val = false)
    (hrequires : (G.messagePrerequisites node).all
      nativeView.application.completed = true) :
    SealedProgram.accepted? nativeView.application.events producer.val =
      some (who, producer.val) := by
  let runtime := supported.resolvingRuntime nullValue window
  let state := nativeView.application
  have hlt : producer.val < node.val := by
    have hnodeWF := supported.graphWF node (G.nodeRow node) (G.nodes_get?_nodeRow node)
    have havailable := hnodeWF.1 (G.nodeTarget producer) (by simp [hreveal, NodeSem.reads])
    unfold Graph.fieldAvailableBefore at havailable
    rw [G.field?_nodeTarget (G.nodes_get?_nodeRow producer)] at havailable
    simpa using havailable
  have hprereq : producer ∈ G.prereqs node :=
    G.nodeTarget_mem_prereqs_of_read (G.nodes_get?_nodeRow node)
      (G.nodes_get?_nodeRow producer) hlt (by simp [hreveal, NodeSem.reads])
  have hproducerComplete : state.completed producer.val = true :=
    List.all_eq_true.mp hrequires producer.val ((G.mem_messagePrerequisites node producer).mpr
      hprereq)
  have hrevealRule : runtime.program.rules[node.val]? =
      some ⟨.reveal who producer.val, G.messagePrerequisites node⟩ := by
    change supported.compile.rules[node.val]? = _
    rw [supported.compile_rule]
    exact congrArg some (G.sealedRule_reveal_eq node producer who guard hreveal hproducer)
  have hproducerNotTimeout : producer.val ∉ state.timeouts := by
    intro htimeout
    have hcomplete := hclosed node.val who producer.val (G.messagePrerequisites node)
      hrevealRule hrequires htimeout
    rw [hnotDone] at hcomplete
    contradiction
  have hproducerDone : SealedProgram.done state.events producer.val = true := by
    simpa [SealedResolution.PublicState.completed, hproducerNotTimeout] using hproducerComplete
  exact (hownCache producer guard hproducer hproducerDone).choose_spec.1

private theorem nodeCommand_isSome_of_ready (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (nativeHistory : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (nativeView : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (hownCache : supported.OwnCommitCache who nativeView.application.events
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory))
    (hclosed : nativeView.application.ResolutionClosed
      (supported.resolvingRuntime nullValue window))
    (node : Fin G.nodeCount)
    (hnotDone : nativeView.application.completed node.val = false)
    (hrequires : (G.messagePrerequisites node).all
      nativeView.application.completed = true)
    (howned :
      (∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    (supported.nodeCommand? who nativeView.application.timeouts policy
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory)
      ((supported.resolvingRuntime nullValue window).eventView
        nativeView)
      (supported.resolvedPlayerStore who nullValue nativeView.application.timeouts
        ((supported.resolvingRuntime nullValue window).eventHistory
          nativeHistory)
        ((supported.resolvingRuntime nullValue window).eventView
          nativeView)) node).isSome := by
  let runtime := supported.resolvingRuntime nullValue window
  let state := nativeView.application
  have hchecks : SealedProgram.done state.events node.val = false ∧
      state.timeouts.contains node.val = false := by
    simpa only [SealedResolution.PublicState.completed, Bool.or_eq_false_iff] using hnotDone
  have hrequires' : SealedProgram.prerequisitesDone state.events
      ((G.sealedRule node).discharge state.timeouts) = true := by
    rw [state.prerequisitesDone_discharge]
    exact hrequires
  unfold nodeCommand?
  change (if state.timeouts.contains node.val then none else
    if SealedProgram.done state.events node.val = false ∧
      SealedProgram.prerequisitesDone state.events
        ((G.sealedRule node).discharge state.timeouts) = true then _ else none).isSome
  simp only [hchecks.2, Bool.false_eq_true, ↓reduceIte]
  have hready : SealedProgram.done state.events node.val = false ∧
      SealedProgram.prerequisitesDone state.events
        ((G.sealedRule node).discharge state.timeouts) = true := ⟨hchecks.1, hrequires'⟩
  rw [if_pos hready]
  split
  next owner guard hsem =>
    have howner : owner = who := by
      rcases howned with ⟨otherGuard, hother⟩ | ⟨producer, otherGuard, hother, _⟩
      · exact (NodeSem.commit.inj (hsem.symm.trans hother)).1
      · cases hsem.symm.trans hother
    subst owner
    simp
  next source hsem =>
    rcases howned with ⟨otherGuard, hother⟩ | ⟨producer, guard, hreveal, hproducer⟩
    · cases hsem.symm.trans hother
    have hrevealRule : runtime.program.rules[node.val]? =
        some ⟨.reveal who producer.val, G.messagePrerequisites node⟩ := by
      change supported.compile.rules[node.val]? = _
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_reveal_eq node producer who guard hreveal hproducer)
    have haccepted := supported.ready_reveal_source_accepted nullValue window who
      nativeHistory nativeView hownCache hclosed node producer guard hreveal hproducer
      hnotDone hrequires
    change SealedProgram.accepted? state.events producer.val = some (who, producer.val)
      at haccepted
    have hhandle : (supported.compile.discharge state.timeouts).openingHandle?
        state.events who node.val = some (who, producer.val) := by
      have hbase : supported.compile.rules[node.val]? =
          some ⟨.reveal who producer.val, G.messagePrerequisites node⟩ := hrevealRule
      have hremaining : ((G.messagePrerequisites node).filter
          (fun prior => !state.timeouts.contains prior)).all
          (SealedProgram.done state.events) = true := hrequires'
      simp only [SealedProgram.openingHandle?, SealedProgram.discharge, List.getElem?_map,
        hbase, Option.map_some, SealedRule.discharge, hchecks.1,
        SealedProgram.prerequisitesDone, hremaining, haccepted, and_self, ↓reduceIte]
    change ((supported.compile.discharge state.timeouts).openingHandle?
      state.events who node.val |>.map _).isSome
    simp only [hhandle, Option.map_some, Option.isSome_some]
  next dist hsem => exact (supported.noSamples node dist hsem).elim

/-- An unfinished ready owned node forces a protocol phase at that node or
an earlier owned site. This holds after defaults under the actual native
invariants, without a decoded source state or an event-log uniqueness premise. -/
theorem resolvingPolicy_progress_of_ready (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (nativeHistory : List
      (supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry)
    (nativeView : (supported.resolvingRuntime nullValue window).messageApplication.View)
    (hpublic : SealedResolution.PublicEventInvariant (supported.resolvingRuntime nullValue window)
      nativeView.application)
    (hownCache : supported.OwnCommitCache who nativeView.application.events
      ((supported.resolvingRuntime nullValue window).eventHistory nativeHistory))
    (hclosed : nativeView.application.ResolutionClosed
      (supported.resolvingRuntime nullValue window))
    (target : Fin G.nodeCount)
    (hnotDone : nativeView.application.completed target.val = false)
    (hrequires : (G.messagePrerequisites target).all
      nativeView.application.completed = true)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    ∀ command ∈ (supported.resolvingPolicy nullValue window who policy
      nativeHistory
      nativeView).support,
      ∃ selected : Fin G.nodeCount,
        selected.val ≤ target.val ∧
        nativeView.application.completed selected.val = false ∧
        (G.messagePrerequisites selected).all
          nativeView.application.completed = true ∧
        ProgressCommand supported who
          ((supported.resolvingRuntime nullValue window).eventHistory
            nativeHistory) selected command := by
  let runtime := supported.resolvingRuntime nullValue window
  let history := runtime.eventHistory nativeHistory
  let view := runtime.eventView nativeView
  let commandAt := supported.nodeCommand? who nativeView.application.timeouts
    policy history view (supported.resolvedPlayerStore who nullValue
      nativeView.application.timeouts history view)
  have htarget : (commandAt target).isSome := supported.nodeCommand_isSome_of_ready
    nullValue window who policy nativeHistory nativeView hownCache hclosed target
      hnotDone hrequires howned
  change ∀ command ∈ ((G.nodeOrder.findSome? commandAt).getD (FinDist.pure .wait)).support, _
  cases hselected : G.nodeOrder.findSome? commandAt with
  | none =>
      have hnone := List.findSome?_eq_none_iff.mp hselected target (G.mem_nodeOrder target)
      rw [hnone] at htarget
      contradiction
  | some law =>
      simp only [Option.getD_some]
      obtain ⟨front, selected, rest, hnodes, hnode, hfront⟩ :=
        List.findSome?_eq_some_iff.mp hselected
      have hbound : selected.val ≤ target.val := by
        have hmem := G.mem_nodeOrder target
        rw [hnodes] at hmem
        rcases List.mem_append.mp hmem with hbefore | hafter
        · rw [hfront target hbefore] at htarget
          contradiction
        · rcases List.mem_cons.mp hafter with rfl | hrest
          · rfl
          · have hsorted : G.nodeOrder.Pairwise (fun left right => left < right) := by
              simpa only [Graph.nodeOrder, List.sortedLT_iff_pairwise] using
                List.sortedLT_finRange G.nodeCount
            rw [hnodes] at hsorted
            exact Nat.le_of_lt ((List.pairwise_cons.mp
              (List.pairwise_append.mp hsorted).2.1).1 target hrest)
      have hprogress := supported.nodeCommand_progress nullValue window who policy
        nativeHistory nativeView hpublic hownCache selected law hnode
      intro command hcommand
      exact ⟨selected, hbound, hprogress.1, hprogress.2.1, hprogress.2.2 command hcommand⟩

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.resolvingPolicy_progress_of_ready' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.resolvingPolicy_progress_of_ready

/-- info: 'Vegas.EventGraph.SealedFragment.runPolicies_no_reregistration' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runPolicies_no_reregistration
