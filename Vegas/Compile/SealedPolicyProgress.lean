/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedView
import Vegas.EventGraph.SourceOrder

/-! # Local progress of compiled sealed policies before timeout

At a decoded reachable snapshot, a selected honest node cannot silently wait.
A fresh commitment has all declared reads, an occupied commitment publishes its
opaque handle, and an enabled reveal has the owner's registered value.  These
are local command facts; bounded inclusion and deadline-relative scheduling
remain obligations of the service layer.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The protocol phases emitted by an honest compiled policy, indexed by the
actual local history that determines its write-once cache.  Every phase retains
its finite source site and ownership evidence. -/
inductive ProgressCommand (supported : SealedFragment G ty) (who : Player)
    (history : List (supported.compile.messageApplication
      (Value := L.Val ty)).PlayerEntry) :
    (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand → Prop where
  | registration (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = none) :
      ProgressCommand supported who history (.privateCommand ⟨(node.val, value)⟩)
  | commitment (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding node.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = some value) :
      ProgressCommand supported who history
        (.submit (.commitment node.val (who, node.val)))
  | opening (node producer : Fin G.nodeCount) (guard : EventGuard L)
      (hnode : (G.nodeRow node).sem = .reveal (G.nodeTarget producer))
      (hproducer : (G.nodeRow producer).sem = .commit who guard)
      (value : L.Val ty)
      (hcache : (supported.compile.registrationEncoding producer.val).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history = some value) :
      ProgressCommand supported who history
        (.submit (.opening node.val (who, producer.val) value))

private theorem selected_nodeCommand_progress
    (supported : SealedFragment G ty) (who : Player) (policy : CommitPolicy G who)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmemory : SealedProgram.RegistrationMemory supported.compile execution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (cfg : ReachableConfig G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg.1)
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who [] policy (execution.principalHistory who)
      (MessageApplication.State.observe _ execution.native who)
      (supported.playerStore who (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)) node = some law) :
    ∀ command ∈ law.support,
      ProgressCommand supported who (execution.principalHistory who) command := by
  let view := MessageApplication.State.observe
    supported.compile.messageApplication execution.native who
  change supported.nodeCommand? who [] policy (execution.principalHistory who) view
    (supported.playerStore who (execution.principalHistory who) view) node = some law at hselected
  have hview : view.application = execution.native.application.events := rfl
  have hcompleted (query : Fin G.nodeCount) :
      SealedProgram.done view.application query.val = true ↔
        query ∈ cfg.1.done := by
    rw [hview]
    exact (Graph.mem_done_decodeSealed ty _ cfg.1 hdecode query).symm
  simp only [nodeCommand?, List.contains_nil, Bool.false_eq_true, if_false,
    SealedRule.discharge_nil, SealedProgram.discharge_nil] at hselected
  split at hselected
  next hreadyChecks =>
    have hready : Ready G cfg.1 node :=
      ready_of_messagePrerequisites view.application cfg.1 node hcompleted
        hreadyChecks.1 (by simpa only [SealedProgram.prerequisitesDone,
          Graph.sealedRule] using hreadyChecks.2)
    split at hselected
    next owner guard hsem =>
      split at hselected
      next howner =>
        subst owner
        have hlaw : law = supported.commitCommand who policy node guard hsem
            (execution.principalHistory who)
            (supported.playerStore who (execution.principalHistory who)
              (MessageApplication.State.observe _ execution.native who)) :=
          Option.some.inj hselected |>.symm
        rw [hlaw]
        cases hcache : (supported.compile.registrationEncoding node.val).cachedValue
            (supported.compile.messageApplication (Value := L.Val ty))
            (execution.principalHistory who) with
        | some value =>
            intro command hcommand
            have heq : command = .submit (.commitment node.val (who, node.val)) := by
              simpa only [commitCommand, hcache, FinDist.mem_support_pure] using hcommand
            subst command
            exact .commitment node guard hsem value hcache
        | none =>
            have hnodeWF := supported.graphWF node (G.nodeRow node)
              (G.nodes_get?_nodeRow node)
            obtain ⟨reads, hreads⟩ :=
              (reachable_storeCoherent supported.graphWF cfg.2).readEnvOfReady
                supported.graphWF (G.nodes_get?_nodeRow node) hready
                (fun ref href => by
                  rw [hsem]
                  exact Finset.mem_image.mpr ⟨ref, href, rfl⟩)
                (fun ref href => by
                  simp only [Graph.nodeWFAt, hsem] at hnodeWF
                  obtain ⟨spec, hfield, hty, _⟩ := hnodeWF.2.2.2 ref href
                  exact ⟨spec, hfield, hty⟩)
            intro command hcommand
            rw [supported.commitCommand_fresh who policy node guard hsem execution hmemory
              hbinding cfg.1 hdecode reads hreads hcache, FinDist.support_map] at hcommand
            obtain ⟨choice, _, rfl⟩ := hcommand
            exact .registration node guard hsem _ hcache
      next => contradiction
    next source hsem =>
      cases hhandle : supported.compile.openingHandle?
          view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          obtain ⟨sourceSlot, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
            supported.compile view.application who node.val handle hhandle
          obtain ⟨requires, hrule, _, _, haccepted⟩ := SealedProgram.openingHandle?_sound
            supported.compile view.application who node.val sourceSlot hhandle
          obtain ⟨revealNode, producer, guard, hrevealIndex, hproducerIndex,
              hreveal, hproducer⟩ := supported.ruleAt_reveal hrule rfl
          have hrevealNode : revealNode = node := Fin.ext hrevealIndex
          subst revealNode
          have hacceptedMem : SealedProgram.Event.accepted sourceSlot (who, sourceSlot) ∈
              execution.native.application.events := by
            rw [← hview]
            exact SealedProgram.accepted_mem_of_accepted?_eq_some haccepted
          obtain ⟨owner, eventRequires, value, eventRule, hcanonical, hlookup⟩ :=
            hbinding.accepted sourceSlot (who, sourceSlot) hacceptedMem
          have howner : owner = who := by
            exact congrArg Prod.fst hcanonical.symm
          subst owner
          have hcache : (supported.compile.registrationEncoding sourceSlot).cachedValue
              (supported.compile.messageApplication (Value := L.Val ty))
              (execution.principalHistory who) = some value := by
            exact (hmemory who sourceSlot).symm.trans hlookup
          intro command hcommand
          rw [hhandle] at hselected
          simp only [Option.map_some] at hselected
          rw [hcache] at hselected
          have hlaw : law = FinDist.pure
              (.submit (.opening node.val (who, sourceSlot) value)) := by
            have hsome : some (FinDist.pure
                (.submit (.opening node.val (who, sourceSlot) value))) = some law := by
              simpa only [hhandle, Option.map_some, hcache] using hselected
            exact (Option.some.inj hsome).symm
          rw [hlaw, FinDist.mem_support_pure] at hcommand
          subst command
          have hsourceSlot : producer.val = sourceSlot := hproducerIndex
          subst sourceSlot
          exact .opening node producer guard hreveal hproducer value hcache
    next dist hsem => exact (supported.noSamples node dist hsem).elim
  next => contradiction

private theorem source_ready_checks
    (supported : SealedFragment G ty)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (cfg : ReachableConfig G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg.1)
    (node : Fin G.nodeCount) (hready : Ready G cfg.1 node) :
    SealedProgram.done execution.native.application.events node.val = false ∧
      SealedProgram.prerequisitesDone execution.native.application.events
        (G.sealedRule node) = true := by
  have hcompleted (query : Fin G.nodeCount) :
      SealedProgram.done execution.native.application.events query.val = true ↔
        query ∈ cfg.1.done :=
    (Graph.mem_done_decodeSealed ty _ cfg.1 hdecode query).symm
  constructor
  · apply Bool.eq_false_of_not_eq_true
    intro hdone
    exact hready.1 ((hcompleted node).1 hdone)
  · unfold SealedProgram.prerequisitesDone
    apply List.all_eq_true.mpr
    intro prior hprior
    simp only [Graph.sealedRule, Graph.messagePrerequisites, List.mem_map,
      List.mem_filter, Graph.mem_nodeOrder, true_and, decide_eq_true_eq] at hprior
    obtain ⟨priorNode, hprereq, rfl⟩ := hprior
    exact (hcompleted priorNode).2 (hready.2 hprereq)

omit [DecidableEq Player] [DecidableEq (L.Val ty)] in
private theorem accepted?_eq_some_of_mem_of_nodup
    {events : List (SealedProgram.Event Player (L.Val ty))}
    (hnodup : (events.map SealedProgram.Event.node).Nodup)
    {node : Nat} {handle : CommitmentHandle Player Nat}
    (hmem : SealedProgram.Event.accepted node handle ∈ events) :
    SealedProgram.accepted? events node = some handle := by
  classical
  induction events with
  | nil => simp at hmem
  | cons event rest ih =>
      have htailNodup := (List.nodup_cons.mp hnodup).2
      rcases List.mem_cons.mp hmem with rfl | htail
      · simp [SealedProgram.accepted?]
      · have hnodeMem : node ∈ rest.map SealedProgram.Event.node :=
          List.mem_map.mpr ⟨.accepted node handle, htail, rfl⟩
        have hne : event.node ≠ node := fun heq =>
          (List.nodup_cons.mp hnodup).1 (heq ▸ hnodeMem)
        cases event with
        | accepted eventNode eventHandle =>
            change eventNode ≠ node at hne
            simp only [SealedProgram.accepted?, List.findSome?_cons]
            rw [if_neg (by simpa using hne)]
            exact ih htailNodup htail
        | opened eventNode value =>
            simp only [SealedProgram.accepted?, List.findSome?_cons]
            exact ih htailNodup htail

private theorem source_ready_nodeCommand_some
    (supported : SealedFragment G ty) (who : Player) (policy : CommitPolicy G who)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (hnodup : (execution.native.application.events.map SealedProgram.Event.node).Nodup)
    (cfg : ReachableConfig G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg.1)
    (node : Fin G.nodeCount) (hready : Ready G cfg.1 node)
    (howned :
      (∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    (supported.nodeCommand? who [] policy (execution.principalHistory who)
      (MessageApplication.State.observe _ execution.native who)
      (supported.playerStore who (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)) node).isSome := by
  obtain ⟨hnotDone, hrequires⟩ :=
    supported.source_ready_checks execution cfg hdecode node hready
  let view := MessageApplication.State.observe
    supported.compile.messageApplication execution.native who
  change (supported.nodeCommand? who [] policy (execution.principalHistory who) view
    (supported.playerStore who (execution.principalHistory who) view) node).isSome
  have hview : view.application = execution.native.application.events := rfl
  unfold nodeCommand?
  simp only [List.contains_nil, Bool.false_eq_true, if_false, hview,
    SealedRule.discharge_nil, hnotDone, hrequires, and_self, if_true]
  split
  next owner guard hsem =>
    have howner : owner = who := by
      rcases howned with ⟨otherGuard, hother⟩ |
          ⟨producer, otherGuard, hother, hproducer⟩
      · exact (NodeSem.commit.inj (hsem.symm.trans hother)).1
      · cases hsem.symm.trans hother
    subst owner
    simp
  next source hnodeSem =>
    rcases howned with ⟨otherGuard, hother⟩ |
        ⟨producer, guard, hsem, hproducer⟩
    · cases hnodeSem.symm.trans hother
    have hsource : source = G.nodeTarget producer :=
      NodeSem.reveal.inj (hnodeSem.symm.trans hsem)
    have hlt : producer.val < node.val := by
      have hnodeWF := supported.graphWF node (G.nodeRow node) (G.nodes_get?_nodeRow node)
      have havailable := hnodeWF.1 (G.nodeTarget producer) (by simp [hsem, NodeSem.reads])
      unfold Graph.fieldAvailableBefore at havailable
      rw [G.field?_nodeTarget (G.nodes_get?_nodeRow producer)] at havailable
      simpa using havailable
    have hproducerDone : producer ∈ cfg.1.done :=
      Ready.prior_commit_done_of_reveal G cfg.1 (G.nodes_get?_nodeRow node)
        (G.nodes_get?_nodeRow producer) hlt hsem hproducer hready
    have hproducerPublic :
        SealedProgram.done execution.native.application.events producer.val = true :=
      (Graph.mem_done_decodeSealed ty _ cfg.1 hdecode producer).mp hproducerDone
    have hproducerRule : supported.compile.rules[producer.val]? =
        some ⟨.commit who, G.messagePrerequisites producer⟩ := by
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_commit_eq producer who guard hproducer)
    have hacceptedMem := hbinding.accepted_mem_of_done_commit producer.val who
      (G.messagePrerequisites producer) hproducerRule hproducerPublic
    have haccepted := accepted?_eq_some_of_mem_of_nodup hnodup hacceptedMem
    have hnodeRule : supported.compile.rules[node.val]? =
        some ⟨.reveal who producer.val, G.messagePrerequisites node⟩ := by
      rw [supported.compile_rule]
      exact congrArg some (G.sealedRule_reveal_eq node producer who guard hsem hproducer)
    have hrequires' : (G.messagePrerequisites node).all
        (SealedProgram.done execution.native.application.events) = true := by
      simpa only [SealedProgram.prerequisitesDone, Graph.sealedRule] using hrequires
    have hhandle : supported.compile.openingHandle?
        execution.native.application.events who node.val = some (who, producer.val) := by
      simp only [SealedProgram.openingHandle?, hnodeRule, hnotDone,
        SealedProgram.prerequisitesDone, hrequires', haccepted, and_self, if_true]
    subst source
    simp only [SealedProgram.discharge_nil, hhandle, Option.map_some,
      Option.isSome_some]
  next dist hsem => exact (supported.noSamples node dist hsem).elim

/-- Before any timeout, if the decoded source graph has an owned ready
commitment or reveal, every possible command of the compiled resolving policy
performs one of its three protocol phases.  An earlier ready owned node may be
selected instead of the witness, but it also performs a phase. -/
theorem resolvingPolicy_progress_of_ready (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) (who : Player) (policy : CommitPolicy G who)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hclear : execution.native.application.visible.timeouts = [])
    (hmemory : SealedResolution.RegistrationMemory
      (supported.resolvingRuntime nullValue window) execution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts
        ((supported.resolvingRuntime nullValue window).eventState execution.native)))
    (hnodup : (execution.native.application.visible.events.map
      SealedProgram.Event.node).Nodup)
    (cfg : ReachableConfig G)
    (hdecode : G.decodeSealed ty
      (supported.compile.eraseReceipts
        ((supported.resolvingRuntime nullValue window).eventState execution.native)) = some cfg.1)
    (node : Fin G.nodeCount) (hready : Ready G cfg.1 node)
    (howned :
      (∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    ∀ command ∈ (supported.resolvingPolicy nullValue window who policy
      (execution.principalHistory who)
      (MessageApplication.State.observe _ execution.native who)).support,
      ProgressCommand supported who
        ((supported.resolvingRuntime nullValue window).eventHistory
          (execution.principalHistory who)) command := by
  let projected : (supported.compile.messageApplication
      (Value := L.Val ty)).PolicyExecution :=
    { native := (supported.resolvingRuntime nullValue window).eventState execution.native
      principalHistory := fun owner =>
        (supported.resolvingRuntime nullValue window).eventHistory
          (execution.principalHistory owner)
      environmentHistory := []
      nativeTrace := [] }
  have hprojectedMemory : SealedProgram.RegistrationMemory supported.compile projected := by
    intro owner slot
    exact (hmemory owner slot).trans
      ((supported.resolvingRuntime nullValue window).eventHistory_cache
        ((supported.resolvingRuntime nullValue window).program.registrationEncoding slot)
        (execution.principalHistory owner)).symm
  have hcandidate := supported.source_ready_nodeCommand_some who policy projected hbinding
    hnodup cfg hdecode node hready howned
  rw [supported.resolvingPolicy_no_timeout nullValue window who policy _ _ hclear]
  change ∀ command ∈ (supported.playerPolicy who policy (projected.principalHistory who)
    (MessageApplication.State.observe _ projected.native who)).support,
      ProgressCommand supported who (projected.principalHistory who) command
  unfold playerPolicy
  cases hselected : G.nodeOrder.findSome? (supported.nodeCommand? who [] policy
      (projected.principalHistory who)
      (MessageApplication.State.observe _ projected.native who)
      (supported.playerStore who (projected.principalHistory who)
        (MessageApplication.State.observe _ projected.native who))) with
  | none =>
      have hnone := List.findSome?_eq_none_iff.mp hselected node (G.mem_nodeOrder node)
      rw [hnone] at hcandidate
      contradiction
  | some law =>
      simp only [Option.getD_some]
      obtain ⟨selected, _, hnode⟩ := List.exists_of_findSome?_eq_some hselected
      exact supported.selected_nodeCommand_progress who policy projected hprojectedMemory
        hbinding cfg hdecode selected law hnode

end Vegas.EventGraph.SealedFragment
