/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedViewAgreement
import Vegas.EventGraph.KernelRealization

/-! # Complete source values determine native declared inputs

Before timeout, accepted commitments and included openings have the same values
as a complete reachable source realization whenever their private registrations
agree. Local read reconstruction then supplies that realization's exact kernel
arguments. This compares values and kernels; equality of execution probabilities
additionally requires the source cylinder-mass calculation.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}
variable (supported : SealedFragment G ty)
variable (cfg : ReachableConfig G) (hterminal : Terminal G cfg.1) (fallback : L.Val ty)

include supported hterminal

/-- A completed source reveal contains its producer's committed value. -/
theorem terminal_reveal_store (node producer : Fin G.nodeCount)
    (hsem : (G.nodeRow node).sem = .reveal (G.nodeTarget producer)) :
    cfg.1.store (G.nodeTarget node) =
      some (⟨ty, cfg.1.nodeValues fallback producer⟩ : TypedValue L) := by
  obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues supported.graphWF
    cfg.2 node (hterminal node)
  have hrowEq : row = G.nodeRow node :=
    Option.some.inj (hrow.symm.trans (G.nodes_get?_nodeRow node))
  subst row
  rw [hsem] at hvalid
  change ∃ value : L.Val (G.nodeRow node).ty,
    Store.getAs cfg.1.store (G.nodeTarget node) (G.nodeRow node).ty = some value ∧
    Store.getAs cfg.1.store (G.nodeTarget producer) (G.nodeRow node).ty = some value at hvalid
  rw [supported.rowType node] at hvalid
  obtain ⟨value, hnode, hproducer⟩ := hvalid
  have heq : cfg.1.nodeValues fallback node = cfg.1.nodeValues fallback producer := by
    simp only [Config.nodeValues, hnode, hproducer]
  rw [cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
    fallback node (supported.rowType node) (hterminal node), heq]

variable (state : SealedProgram.State Player (L.Val ty))
variable (hbinding : SealedProgram.BindingInvariant supported.compile state)
variable (hregistered : ∀ owner (node : Fin G.nodeCount) guard,
  (G.nodeRow node).sem = .commit owner guard → ∀ value,
    state.service.lookup (owner, node.val) = some value → cfg.1.nodeValues fallback node = value)

include hbinding hregistered

/-- Included public openings agree with the complete source even if they
arrived in an order different from the written source order. -/
theorem opened_source_value (index : Nat) (value : L.Val ty)
    (hopened : .opened index value ∈ state.events) :
    cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L) := by
  obtain ⟨owner, producer, requires, hrule, hlookup⟩ := hbinding.opened index value hopened
  obtain ⟨node, source, guard, rfl, rfl, hsem, hsource⟩ := supported.ruleAt_reveal hrule rfl
  rw [supported.terminal_reveal_store cfg hterminal fallback node source hsem,
    hregistered owner source guard hsource value hlookup]

private theorem accepted_source_value (index : Nat) (handle : CommitmentHandle Player Nat)
    (value : L.Val ty) (haccepted : .accepted index handle ∈ state.events)
    (hlookup : state.service.lookup handle = some value) :
    cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L) := by
  obtain ⟨owner, requires, registered, hrule, hhandle, _⟩ :=
    hbinding.accepted index handle haccepted
  obtain ⟨node, guard, rfl, hsem⟩ := supported.ruleAt_commit hrule rfl
  rw [hhandle] at hlookup
  rw [cfg.1.store_nodeValues (reachable_storeCoherent supported.graphWF cfg.2)
    fallback node (supported.rowType node) (hterminal node),
    hregistered owner node guard hsem value hlookup]

/-- When every graph node has completed normally, native event decoding
recovers this very source realization. Accepted handles and openings are checked
through binding and registration agreement; no node-order or distinctness
premise is needed in addition. -/
theorem decodeSealed_eq_source
    (hcomplete : ∀ node : Fin G.nodeCount, SealedProgram.done state.events node.val = true) :
    G.decodeSealed ty state = some cfg.1 := by
  apply Graph.decodeSealedFrom_eq_of_terminal_agreement ty state.service cfg state.events
    hterminal ?_ hcomplete
  intro event hevent
  cases event with
  | accepted index handle =>
      obtain ⟨owner, requires, value, hrule, _, hlookup⟩ :=
        hbinding.accepted index handle hevent
      obtain ⟨node, guard, rfl, _⟩ := supported.ruleAt_commit hrule rfl
      refine ⟨(node, ⟨ty, value⟩), ?_, ?_⟩
      · rw [Graph.decodeSealedEvent_accepted, hlookup, Option.map_some]
      · exact supported.accepted_source_value cfg hterminal fallback state hbinding hregistered
          node.val handle value hevent hlookup
  | opened index value =>
      obtain ⟨owner, source, requires, hrule, _⟩ := hbinding.opened index value hevent
      obtain ⟨node, producer, guard, rfl, _, _, _⟩ := supported.ruleAt_reveal hrule rfl
      exact ⟨(node, ⟨ty, value⟩), G.decodeSealedEvent_opened ty state.service node value,
        supported.opened_source_value cfg hterminal fallback state hbinding hregistered
          node.val value hevent⟩

/-- Reconstructed player reads agree with the complete source. The common
event-value lemma does not require a particular commitment service. -/
theorem sealedPlayerStore_source (who : Player) (memory : Nat → Option (L.Val ty))
    (hmemory : ∀ slot, memory slot = state.service.lookup (who, slot))
    (field : Nat) (value : TypedValue L)
    (hvalue : G.sealedPlayerStore ty who memory state.events field = some value) :
    cfg.1.store field = some value := by
  apply cfg.sealedPlayerStore_agrees ty who memory state.events ?_
    (supported.opened_source_value cfg hterminal fallback state hbinding hregistered)
    field value hvalue
  intro index handle stored haccepted howner hcache
  have hlookup : state.service.lookup handle = some stored := by
    rw [hmemory, ← howner] at hcache
    exact hcache
  exact supported.accepted_source_value cfg hterminal fallback state hbinding hregistered
    index handle stored haccepted hlookup

/-- A successful native restriction to declared fields is exactly the same
read environment in the complete source. -/
theorem sealedPlayerStore_source_reads (who : Player) (memory : Nat → Option (L.Val ty))
    (hmemory : ∀ slot, memory slot = state.service.lookup (who, slot))
    (refs : Finset (FieldRef L)) (reads : ReadEnv L refs)
    (hreads : ReadEnv.ofStore? (G.sealedPlayerStore ty who memory state.events) refs = some reads) :
    ReadEnv.ofStore? cfg.1.store refs = some reads := by
  apply cfg.sealedPlayerStore_reads_eq ty who memory state.events ?_
    (supported.opened_source_value cfg hterminal fallback state hbinding hregistered)
    refs reads hreads
  intro index handle stored haccepted howner hcache
  have hlookup : state.service.lookup handle = some stored := by
    rw [hmemory, ← howner] at hcache
    exact hcache
  exact supported.accepted_source_value cfg hterminal fallback state hbinding hregistered
    index handle stored haccepted hlookup

variable [DecidableEq (L.Val ty)]

/-- A fresh native registration draws the original policy kernel at exactly
the complete source's declared inputs. The premises describe successful native
reads and local registration memory, not an assumed equality of source inputs. -/
theorem commitCommand_source_kernel (who : Player) (policy : CommitPolicy G who)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (history : List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (hmemory : ∀ slot, (supported.compile.registrationEncoding slot).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) history =
        state.service.lookup (who, slot))
    (hcache : (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) history = none)
    (havailable : (ReadEnv.ofStoreExec? (G.sealedPlayerStore ty who
      (fun slot => (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) history) state.events)
      guard.choiceReads).isSome) :
    ∃ reads : ReadEnv L guard.choiceReads,
      ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
      supported.commitCommand who policy node guard hsem history
        (G.sealedPlayerStore ty who (fun slot =>
          (supported.compile.registrationEncoding slot).cachedValue
            (supported.compile.messageApplication (Value := L.Val ty)) history) state.events) =
        (policy node guard hsem reads).map (fun choice =>
          .privateCommand ⟨(node.val,
            cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩) := by
  obtain ⟨reads, hreads⟩ := Option.isSome_iff_exists.mp havailable
  refine ⟨reads, supported.sealedPlayerStore_source_reads cfg hterminal fallback state hbinding
    hregistered who _ hmemory _ reads
    (ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreads), ?_⟩
  simp only [SealedShape.commitCommand, hcache, hreads]

omit hbinding hregistered in
/-- At any compatible native snapshot before timeout, a fresh registration
uses the complete source realization's declared input. This statement is
independent of how the snapshot was selected from a trace. -/
theorem resolving_registration_kernel (nullValue : L.Val ty) (window : Nat)
    (execution : (supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution)
    (hclear : execution.native.application.visible.timeouts = [])
    (hmemory : SealedResolution.RegistrationMemory
      (supported.resolvingRuntime nullValue window) execution)
    (hvalid : SealedProgram.BindingInvariant supported.compile
      ⟨execution.native.application.service, execution.native.pool,
        execution.native.application.visible.events⟩)
    (hvalues : ∀ owner (node : Fin G.nodeCount) guard,
      (G.nodeRow node).sem = .commit owner guard → ∀ value,
        execution.native.application.service.lookup (owner, node.val) = some value →
          cfg.1.nodeValues fallback node = value)
    (who : Player) (original replacement : CommitPolicy G who) (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈
      (supported.resolvingPolicy nullValue window who original (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who)).support) :
    ∃ (node : Fin G.nodeCount) (guard : EventGuard L)
      (hsem : (G.nodeRow node).sem = .commit who guard) (reads : ReadEnv L guard.choiceReads),
      slot = node.val ∧ execution.native.application.service.lookup (who, node.val) = none ∧
      ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
      supported.resolvingPolicy nullValue window who replacement (execution.principalHistory who)
        (MessageApplication.State.observe _ execution.native who) =
        (replacement node guard hsem reads).map (fun choice =>
          .privateCommand ⟨(node.val,
            cast (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩) := by
  rw [supported.resolvingPolicy_no_timeout _ _ _ _ _ _ hclear] at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, hcache, hreads, hkernel⟩ :=
    supported.selected_registration_kernel who [] original _ _ _ slot value hcommand
  let runtime := supported.resolvingRuntime nullValue window
  have hhistory : ∀ index,
      (supported.compile.registrationEncoding index).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty))
        (runtime.eventHistory (execution.principalHistory who)) =
          execution.native.application.service.lookup (who, index) := by
    intro index
    exact (runtime.eventHistory_cache (runtime.program.registrationEncoding index)
      (execution.principalHistory who)).trans (hmemory who index).symm
  refine ⟨node, guard, hsem, reads, hslot, (hhistory node.val).symm.trans hcache, ?_, ?_⟩
  · exact supported.sealedPlayerStore_source_reads cfg hterminal fallback _ hvalid hvalues who
      _ hhistory _ reads (ReadEnv.ofStore?_eq_some_of_ofStoreExec?_eq_some hreads)
  · rw [supported.resolvingPolicy_no_timeout _ _ _ _ _ _ hclear]
    exact hkernel replacement

end Vegas.EventGraph.SealedFragment
