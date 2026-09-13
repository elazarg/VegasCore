/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedReplay
import Vegas.Compile.SealedPublication

/-! # Compiled policy commands under partial disclosure

The value-substituted honest policy consults private history only for its
registration cache. Equal occupancy preserves typed read availability and
node selection; equal known values preserve permitted opening payloads.
Fresh registrations may differ only at handles outside the knowledge set.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

private theorem store_set_available (ty : L.Ty)
    (left right : Store L) (leftValue rightValue : L.Val ty) (target : Nat)
    (hstore : ∀ field queryTy,
      (Store.getAs left field queryTy).isSome = (Store.getAs right field queryTy).isSome) :
    ∀ field queryTy,
      (Store.getAs (left.set target ⟨ty, leftValue⟩) field queryTy).isSome =
      (Store.getAs (right.set target ⟨ty, rightValue⟩) field queryTy).isSome := by
  intro field queryTy
  by_cases hfield : field = target
  · subst field
    simp only [Store.getAs, Store.set_eq, TypedValue.as?]
    split <;> rfl
  · simp only [Store.getAs_set_ne _ hfield]
    exact hstore field queryTy

private theorem replaySealedView_available (G : Graph Player L) (ty : L.Ty) (who : Player)
    (leftMemory rightMemory : Nat → Option (L.Val ty))
    (hmemory : ∀ slot, (leftMemory slot).isSome = (rightMemory slot).isSome)
    (events : List (SealedProgram.Event Player (L.Val ty))) (left right : Store L)
    (hstore : ∀ field queryTy,
      (Store.getAs left field queryTy).isSome = (Store.getAs right field queryTy).isSome) :
    ∀ field queryTy,
      (Store.getAs (G.replaySealedView ty who leftMemory left events) field queryTy).isSome =
      (Store.getAs (G.replaySealedView ty who rightMemory right events) field queryTy).isSome := by
  induction events generalizing left right with
  | nil => exact hstore
  | cons event rest ih =>
      cases event with
      | accepted node handle =>
          by_cases howner : handle.1 = who
          · have hslot := hmemory handle.2
            cases hl : leftMemory handle.2 <;> cases hr : rightMemory handle.2 <;>
              simp only [hl, hr, Option.isSome_none, Option.isSome_some] at hslot
            · simpa only [replaySealedView, if_pos howner, hl, hr] using ih left right hstore
            · contradiction
            · contradiction
            · simp only [replaySealedView, if_pos howner, hl, hr]
              exact ih _ _ (store_set_available ty left right _ _ _ hstore)
          · simpa only [replaySealedView, if_neg howner] using ih left right hstore
      | opened node value =>
          exact ih _ _ (store_set_available ty left right value value _ hstore)

/-- The executable local read check depends on slot occupancy and public
events, not on private payloads stored at those occupied slots. -/
theorem sealedPlayerStore_readAvailability (G : Graph Player L) (ty : L.Ty) (who : Player)
    (leftMemory rightMemory : Nat → Option (L.Val ty))
    (hmemory : ∀ slot, (leftMemory slot).isSome = (rightMemory slot).isSome)
    (events : List (SealedProgram.Event Player (L.Val ty))) (refs : Finset (FieldRef L)) :
    (ReadEnv.ofStoreExec? (G.sealedPlayerStore ty who leftMemory events) refs).isSome =
      (ReadEnv.ofStoreExec? (G.sealedPlayerStore ty who rightMemory events) refs).isSome := by
  have hstore := G.replaySealedView_available ty who leftMemory rightMemory hmemory events
    (G.initialPlayerStore who) (G.initialPlayerStore who) (fun _ _ => rfl)
  unfold ReadEnv.ofStoreExec?
  have havailable :
      (∀ ref, ref ∈ refs →
        (Store.getAs (G.sealedPlayerStore ty who leftMemory events) ref.field ref.ty).isSome) ↔
      (∀ ref, ref ∈ refs →
        (Store.getAs (G.sealedPlayerStore ty who rightMemory events) ref.field ref.ty).isSome) := by
    simp only [sealedPlayerStore, hstore]
  split <;> split
  · rfl
  · rename_i hleft hright
    exact False.elim (hright (havailable.mp hleft))
  · rename_i hleft hright
    exact False.elim (hleft (havailable.mpr hright))
  · rfl

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

private theorem commitCommand_knowledge (supported : SealedFragment G ty)
    (known : CommitmentHandle Player Nat → Prop) (who : Player)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (leftHistory rightHistory :
      List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hoccupied : ∀ slot,
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory).isSome =
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory).isSome)
    (node : Fin G.nodeCount) (guard : EventGuard L)
    (hsem : (G.nodeRow node).sem = .commit who guard)
    (hvalues : known (who, node.val) → leftValues node = rightValues node) :
    ∃ leftCommand rightCommand,
      supported.commitCommand who (supported.valuePolicy leftValues who) node guard hsem
        leftHistory view = FinDist.pure leftCommand ∧
      supported.commitCommand who (supported.valuePolicy rightValues who) node guard hsem
        rightHistory view = FinDist.pure rightCommand ∧
      SealedProgram.CommandAgreement supported.compile known who leftCommand rightCommand := by
  have hslot := hoccupied node.val
  unfold commitCommand
  cases hl : (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) leftHistory <;>
    cases hr : (supported.compile.registrationEncoding node.val).cachedValue
      (supported.compile.messageApplication (Value := L.Val ty)) rightHistory <;>
    simp only [hl, hr, Option.isSome_none, Option.isSome_some] at hslot
  · have havailable := G.sealedPlayerStore_readAvailability ty who
      (fun slot => (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory)
      (fun slot => (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory)
      hoccupied view.application guard.choiceReads
    change (ReadEnv.ofStoreExec? (supported.playerStore who leftHistory view)
      guard.choiceReads).isSome =
      (ReadEnv.ofStoreExec? (supported.playerStore who rightHistory view)
        guard.choiceReads).isSome at havailable
    cases hreadsL : ReadEnv.ofStoreExec? (supported.playerStore who leftHistory view)
        guard.choiceReads <;>
      cases hreadsR : ReadEnv.ofStoreExec? (supported.playerStore who rightHistory view)
        guard.choiceReads <;>
      simp only [hreadsL, hreadsR, Option.isSome_none, Option.isSome_some] at havailable
    · exact ⟨_, _, rfl, rfl, SealedProgram.CommandAgreement.refl _ who⟩
    · contradiction
    · contradiction
    · simp only [valuePolicy, FinDist.map_pure, cast_cast, cast_eq]
      exact ⟨_, _, rfl, rfl, ⟨rfl, hvalues⟩⟩
  · contradiction
  · contradiction
  · exact ⟨_, _, rfl, rfl, SealedProgram.CommandAgreement.refl _ who⟩

private theorem nodeCommand?_knowledge (supported : SealedFragment G ty)
    (known : CommitmentHandle Player Nat → Prop) (who : Player)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (leftHistory rightHistory :
      List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hoccupied : ∀ slot,
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory).isSome =
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory).isSome)
    (hcache : ∀ slot, known (who, slot) →
      (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory =
      (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory)
    (hvalues : ∀ node, known (who, node.val) → leftValues node = rightValues node)
    (hopenings : ∀ (node : Fin G.nodeCount) handle,
      supported.compile.openingHandle? view.application who node.val = some handle → known handle)
    (node : Fin G.nodeCount)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who (supported.valuePolicy leftValues who)
      leftHistory view node = some law) :
    ∃ leftCommand rightCommand, law = FinDist.pure leftCommand ∧
      supported.nodeCommand? who (supported.valuePolicy rightValues who)
        rightHistory view node = some (FinDist.pure rightCommand) ∧
      SealedProgram.CommandAgreement supported.compile known who leftCommand rightCommand := by
  unfold nodeCommand? at hselected ⊢
  split at hselected
  · rename_i hready
    rw [if_pos hready]
    split at hselected
    · rename_i owner guard hsem
      split at hselected
      · rename_i howner
        rw [dif_pos howner]
        obtain ⟨lc, rc, hl, hr, hrelated⟩ := supported.commitCommand_knowledge known who
          leftValues rightValues leftHistory rightHistory view hoccupied node guard
          (howner ▸ hsem) (hvalues node)
        exact ⟨lc, rc, (Option.some.inj hselected).symm.trans hl, congrArg some hr, hrelated⟩
      · contradiction
    · cases hhandle : supported.compile.openingHandle? view.application who node.val with
      | none => simp only [hhandle, Option.map_none] at hselected; contradiction
      | some handle =>
          have hknown := hopenings node handle hhandle
          obtain ⟨slot, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
            supported.compile view.application who node.val handle hhandle
          have heq := hcache slot hknown
          simp only [hhandle, Option.map_some] at hselected ⊢
          rw [heq] at hselected
          split at hselected
          all_goals
            exact ⟨_, _, (Option.some.inj hselected).symm, rfl,
              SealedProgram.CommandAgreement.refl _ who⟩
    · contradiction
  · contradiction

/-- Honest command shape is independent of hidden registered values.
Designated known openings agree, while fresh private values need agree only
at designated known slots. Both sides are the actual compiled policy. -/
theorem playerPolicy_knowledge (supported : SealedFragment G ty)
    (known : CommitmentHandle Player Nat → Prop) (who : Player)
    (leftValues rightValues : Fin G.nodeCount → L.Val ty)
    (leftHistory rightHistory :
      List (supported.compile.messageApplication (Value := L.Val ty)).PlayerEntry)
    (view : (supported.compile.messageApplication (Value := L.Val ty)).View)
    (hoccupied : ∀ slot,
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory).isSome =
      ((supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory).isSome)
    (hcache : ∀ slot, known (who, slot) →
      (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) leftHistory =
      (supported.compile.registrationEncoding slot).cachedValue
        (supported.compile.messageApplication (Value := L.Val ty)) rightHistory)
    (hvalues : ∀ node, known (who, node.val) → leftValues node = rightValues node)
    (hopenings : ∀ (node : Fin G.nodeCount) handle,
      supported.compile.openingHandle? view.application who node.val = some handle → known handle) :
    ∃ leftCommand rightCommand,
      supported.playerPolicy who (supported.valuePolicy leftValues who) leftHistory view =
        FinDist.pure leftCommand ∧
      supported.playerPolicy who (supported.valuePolicy rightValues who) rightHistory view =
        FinDist.pure rightCommand ∧
      SealedProgram.CommandAgreement supported.compile known who leftCommand rightCommand := by
  unfold playerPolicy
  cases hselected : G.nodeOrder.findSome?
      (supported.nodeCommand? who (supported.valuePolicy leftValues who) leftHistory view) with
  | none =>
      have hnone : G.nodeOrder.findSome?
          (supported.nodeCommand? who (supported.valuePolicy rightValues who) rightHistory view) =
            none := by
        apply List.findSome?_eq_none_iff.mpr
        intro node hnode
        exact (supported.nodeCommand?_none_iff who _ _ leftHistory rightHistory view node).mp
          (List.findSome?_eq_none_iff.mp hselected node hnode)
      simp only [hnone, Option.getD_none]
      exact ⟨_, _, rfl, rfl, SealedProgram.CommandAgreement.refl _ who⟩
  | some law =>
      obtain ⟨front, node, rest, hnodes, hnode, hfront⟩ :=
        List.findSome?_eq_some_iff.mp hselected
      obtain ⟨lc, rc, hl, hr, hrelated⟩ := supported.nodeCommand?_knowledge known who
        leftValues rightValues leftHistory rightHistory view hoccupied hcache hvalues hopenings
        node law hnode
      have hright : G.nodeOrder.findSome?
          (supported.nodeCommand? who (supported.valuePolicy rightValues who) rightHistory view) =
            some (FinDist.pure rc) := by
        apply List.findSome?_eq_some_iff.mpr
        refine ⟨front, node, rest, hnodes, hr, ?_⟩
        intro prior hprior
        exact (supported.nodeCommand?_none_iff who _ _ leftHistory rightHistory view prior).mp
          (hfront prior hprior)
      simp only [hright, Option.getD_some]
      exact ⟨lc, rc, hl, rfl, hrelated⟩

end Vegas.EventGraph.SealedFragment
