/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedDecodeLaws
import Vegas.Compile.SealedRules
import Interaction.SealedMemory
import Interaction.SealedBinding

/-! # Source decision reads from native local memory and public events

The player-side store contains only public initial inputs, the player's own
initial inputs, accepted own commitments reconstructed from its local history,
and included openings. It does not inspect the ideal commitment service or
pending payloads. The proof-side decoder may inspect the service; the agreement
theorem relates the two on precisely the fields visible to the player.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Filter the initial inputs by the source's ownership metadata. -/
def initialPlayerStore (G : Graph Player L) (who : Player) : Store L := fun field =>
  match G.field? field with
  | none => none
  | some spec =>
      if spec.owner = none ∨ spec.owner = some who then spec.initialValue? else none

/-- Replay accepted own commitments and public openings into a local store.
`memory` is the player's own first-registration cache, not the ideal table. -/
def replaySealedView (G : Graph Player L) (ty : L.Ty) (who : Player)
    (memory : Nat → Option (L.Val ty)) (store : Store L) :
    List (SealedProgram.Event Player (L.Val ty)) → Store L
  | [] => store
  | event :: rest =>
      let value := match event with
        | .accepted _ handle => if handle.1 = who then memory handle.2 else none
        | .opened _ value => some value
      let next := match value with
        | none => store
        | some value => store.set (G.nodeTarget event.node) ⟨ty, value⟩
      G.replaySealedView ty who memory next rest

/-- Local reconstruction needs the current public events and only the
principal's own private registration history. -/
def sealedPlayerStore (G : Graph Player L) (ty : L.Ty) (who : Player)
    (memory : Nat → Option (L.Val ty))
    (events : List (SealedProgram.Event Player (L.Val ty))) : Store L :=
  G.replaySealedView ty who memory (G.initialPlayerStore who) events

private theorem replaySealedView_agrees (G : Graph Player L) (ty : L.Ty) (who : Player)
    (memory : Nat → Option (L.Val ty))
    (service : IdealCommitments Player Nat (L.Val ty))
    (hmemory : ∀ slot, service.lookup (who, slot) = memory slot)
    (events : List (SealedProgram.Event Player (L.Val ty)))
    (haccepted : ∀ node handle, SealedProgram.Event.accepted node handle ∈ events →
      ∃ row, G.nodes[node]? = some row ∧ row.owner = some handle.1)
    (localStore : Store L) (cfg result : Config G)
    (hagrees : ∀ field spec, G.field? field = some spec →
      (spec.owner = none ∨ spec.owner = some who) → localStore field = cfg.store field)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    ∀ field spec, G.field? field = some spec →
      (spec.owner = none ∨ spec.owner = some who) →
      G.replaySealedView ty who memory localStore events field = result.store field := by
  induction events generalizing localStore cfg with
  | nil =>
      cases Option.some.inj hdecode
      exact hagrees
  | cons event rest ih =>
      have hrest : ∀ node handle, SealedProgram.Event.accepted node handle ∈ rest →
          ∃ row, G.nodes[node]? = some row ∧ row.owner = some handle.1 :=
        fun node handle hmem => haccepted node handle (List.mem_cons_of_mem _ hmem)
      unfold decodeSealedFrom at hdecode
      unfold decodeSealedEvent at hdecode
      split at hdecode
      · rename_i hnode
        cases event with
        | accepted node handle =>
            cases hlookup : service.lookup handle with
            | none => simp [hlookup] at hdecode
            | some value =>
                simp only [hlookup, Option.map_some, Option.bind_some] at hdecode
                dsimp only [replaySealedView]
                apply ih hrest _ _ ?_ hdecode
                intro field spec hfield hvisible
                by_cases howner : handle.1 = who
                · have hcache : memory handle.2 = some value := by
                    rw [← hmemory, ← howner]
                    exact hlookup
                  simp only [if_pos howner, hcache]
                  change (localStore.set (G.nodeTarget node) ⟨ty, value⟩) field =
                    (cfg.store.set (G.nodeTarget node) ⟨ty, value⟩) field
                  by_cases heq : field = G.nodeTarget node
                  · simp [heq]
                  · simp only [Store.set_ne _ heq]
                    exact hagrees field spec hfield hvisible
                · simp only [if_neg howner]
                  have hne : field ≠ G.nodeTarget node := by
                    intro heq
                    obtain ⟨row, hrow, hrowOwner⟩ := haccepted node handle (List.mem_cons_self ..)
                    have hspec := G.field?_nodeTarget hrow
                    rw [← heq, hfield] at hspec
                    have hownerSpec : spec.owner = some handle.1 := by
                      rw [Option.some.inj hspec]
                      exact hrowOwner
                    rcases hvisible with hpublic | hown
                    · rw [hpublic] at hownerSpec
                      contradiction
                    · exact howner (Option.some.inj (hownerSpec.symm.trans hown))
                  change localStore field = (cfg.store.set (G.nodeTarget node) ⟨ty, value⟩) field
                  rw [Store.set_ne _ hne]
                  exact hagrees field spec hfield hvisible
        | opened node value =>
            simp only [Option.bind_some] at hdecode
            dsimp only [replaySealedView]
            apply ih hrest _ _ ?_ hdecode
            intro field spec hfield hvisible
            change (localStore.set (G.nodeTarget node) ⟨ty, value⟩) field =
              (cfg.store.set (G.nodeTarget node) ⟨ty, value⟩) field
            by_cases heq : field = G.nodeTarget node
            · simp [heq]
            · simp only [Store.set_ne _ heq]
              exact hagrees field spec hfield hvisible
      · simp at hdecode

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- The native local reconstruction agrees with the decoded graph store on
all source-visible fields. No source-policy restriction is needed. -/
theorem sealedPlayerStore_agrees (supported : SealedFragment G ty) (who : Player)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmemory : SealedProgram.RegistrationMemory supported.compile execution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (cfg : Config G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg)
    (ref : FieldRef L) (hvisible : G.fieldRefVisibleTo who ref) :
    Store.getAs
      (G.sealedPlayerStore ty who (fun slot =>
        (supported.compile.registrationEncoding slot).cachedValue
          (supported.compile.messageApplication (Value := L.Val ty))
          (execution.principalHistory who)) execution.native.application.events)
      ref.field ref.ty = Store.getAs cfg.store ref.field ref.ty := by
  obtain ⟨spec, hfield, _hty, howner⟩ := hvisible
  have hstore := G.replaySealedView_agrees ty who _ execution.native.application.service
    (hmemory who) execution.native.application.events (fun node handle hmem => by
      obtain ⟨owner, requires, value, hrule, hhandle, _hlookup⟩ :=
        hbinding.accepted node handle hmem
      obtain ⟨index, guard, rfl, hsem⟩ := supported.ruleAt_commit hrule rfl
      refine ⟨G.nodeRow index, G.nodes_get?_nodeRow index, ?_⟩
      have hwf := supported.graphWF index (G.nodeRow index) (G.nodes_get?_nodeRow index)
      unfold Graph.nodeWFAt at hwf
      rw [hsem] at hwf
      simpa only [hhandle] using hwf.2.2.1)
    (G.initialPlayerStore who) (Config.initial G) cfg (fun field spec hfield howner => by
      simp only [Graph.initialPlayerStore, hfield, if_pos howner,
        Config.initial, Graph.initialStore]) hdecode ref.field spec hfield howner
  unfold Store.getAs Graph.sealedPlayerStore
  rw [hstore]

/-- Reconstruct the actual declared-read environment of a source commitment
from the player's local history and the public application events. -/
theorem sealedPlayerStore_reads (supported : SealedFragment G ty) (who : Player)
    (execution : (supported.compile.messageApplication (Value := L.Val ty)).PolicyExecution)
    (hmemory : SealedProgram.RegistrationMemory supported.compile execution)
    (hbinding : SealedProgram.BindingInvariant supported.compile
      (supported.compile.eraseReceipts execution.native))
    (cfg : Config G)
    (hdecode : G.decodeSealed ty (supported.compile.eraseReceipts execution.native) = some cfg)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.store guard.choiceReads = some reads) :
    ReadEnv.ofStore?
      (G.sealedPlayerStore ty who (fun slot =>
        (supported.compile.registrationEncoding slot).cachedValue
          (supported.compile.messageApplication (Value := L.Val ty))
          (execution.principalHistory who)) execution.native.application.events)
      guard.choiceReads = some reads := by
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  have hwf := supported.graphWF node (G.nodeRow node) (G.nodes_get?_nodeRow node)
  unfold Graph.nodeWFAt at hwf
  rw [hsem] at hwf
  exact (supported.sealedPlayerStore_agrees who execution hmemory hbinding cfg hdecode
    ref (hwf.2.2.2 ref href)).symm

end Vegas.EventGraph.SealedFragment
