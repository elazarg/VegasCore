/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedView
import Vegas.EventGraph.KernelRealization

/-! # Local read reconstruction from agreeing event values

Player-side reconstruction depends on included openings and the player's own
cached values at accepted handles. It needs no private service table and no
assumption that every accepted commitment is openable. These lemmas apply to
both commitment hosts without changing their policy code.
-/

noncomputable section

namespace Vegas.EventGraph.ReachableConfig

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} (cfg : ReachableConfig G) (ty : L.Ty) (who : Player)
variable (memory : Nat → Option (L.Val ty))
variable (events : List (SealedProgram.Event Player (L.Val ty)))
variable (haccepted : ∀ index handle value, SealedProgram.Event.accepted index handle ∈ events →
  handle.1 = who → memory handle.2 = some value →
    cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))
variable (hopened : ∀ index value, SealedProgram.Event.opened index value ∈ events →
  cfg.1.store (G.nodeTarget index) = some (⟨ty, value⟩ : TypedValue L))

include haccepted hopened

private theorem replaySealedView_agrees (store : Store L)
    (hstore : ∀ field value, store field = some value → cfg.1.store field = some value) :
    ∀ field value, G.replaySealedView ty who memory store events field = some value →
      cfg.1.store field = some value := by
  induction events generalizing store with
  | nil => exact hstore
  | cons event rest ih =>
      apply ih (fun _ _ _ hmem => haccepted _ _ _ (List.mem_cons_of_mem _ hmem))
        (fun _ _ hmem => hopened _ _ (List.mem_cons_of_mem _ hmem))
      intro field stored hstored
      have hmem := List.mem_cons_self (a := event) (l := rest)
      cases event with
      | accepted index handle =>
          by_cases howner : handle.1 = who
          · dsimp only at hstored
            rw [if_pos howner] at hstored
            cases hcache : memory handle.2 with
            | none =>
                simp only [hcache] at hstored
                exact hstore field stored hstored
            | some value =>
                simp only [hcache] at hstored
                change (store.set (G.nodeTarget index) ⟨ty, value⟩) field = some stored at hstored
                by_cases heq : field = G.nodeTarget index
                · subst field
                  rw [Store.set_eq] at hstored
                  exact (haccepted index handle value hmem howner hcache).trans hstored
                · rw [Store.set_ne _ heq] at hstored
                  exact hstore field stored hstored
          · simp only [if_neg howner] at hstored
            exact hstore field stored hstored
      | opened index value =>
          change (store.set (G.nodeTarget index) ⟨ty, value⟩) field = some stored at hstored
          by_cases heq : field = G.nodeTarget index
          · subst field
            rw [Store.set_eq] at hstored
            exact (hopened index value hmem).trans hstored
          · rw [Store.set_ne _ heq] at hstored
            exact hstore field stored hstored

omit haccepted hopened in
private theorem initialStore_agrees (field : Nat) (value : TypedValue L)
    (hinitial : G.initialStore field = some value) : cfg.1.store field = some value := by
  rcases cfg with ⟨cfg, hreach⟩
  induction hreach with
  | initial => exact hinitial
  | step hprior event hnext ih =>
      obtain ⟨written, rfl⟩ := stepAvailableEvent_support_completeNode event hnext
      have hne : field ≠ G.nodeTarget event.node := by
        intro heq
        obtain ⟨row, hrow⟩ := event.row_get
        rw [heq, Graph.initialStore, G.field?_nodeTarget hrow] at hinitial
        cases hinitial
      exact (Store.set_ne _ hne written).trans ih

/-- Successful reconstructed reads agree with the source when the events and
own cached values that actually contribute writes agree. Unrelated candidate
meanings, absent cache entries, and unavailable fields are unrestricted. -/
theorem sealedPlayerStore_agrees (field : Nat) (value : TypedValue L)
    (hvalue : G.sealedPlayerStore ty who memory events field = some value) :
    cfg.1.store field = some value := by
  apply cfg.replaySealedView_agrees ty who memory events haccepted hopened
    (G.initialPlayerStore who) ?_ field value hvalue
  intro initialField initialValue hvalue
  apply cfg.initialStore_agrees initialField initialValue
  unfold Graph.initialPlayerStore at hvalue
  cases hfield : G.field? initialField with
  | none => simp only [hfield] at hvalue; contradiction
  | some spec =>
      simp only [hfield] at hvalue
      split at hvalue
      · simpa only [Graph.initialStore, hfield] using hvalue
      · contradiction

/-- Restriction to declared choice fields gives exactly the source read
environment, rather than merely equal support or equal public fields. -/
theorem sealedPlayerStore_reads_eq (refs : Finset (FieldRef L)) (reads : ReadEnv L refs)
    (hreads : ReadEnv.ofStore? (G.sealedPlayerStore ty who memory events) refs = some reads) :
    ReadEnv.ofStore? cfg.1.store refs = some reads := by
  apply ReadEnv.ofStore?_eq_of_getAs_eq hreads
  intro ref href
  have hread := ReadEnv.ofStore?_read hreads href
  cases hstored : G.sealedPlayerStore ty who memory events ref.field with
  | none => simp only [Store.getAs, hstored] at hread; contradiction
  | some value =>
      have hsource := cfg.sealedPlayerStore_agrees ty who memory events haccepted hopened
        ref.field value hstored
      simp only [Store.getAs, hstored, hsource]

end Vegas.EventGraph.ReachableConfig
