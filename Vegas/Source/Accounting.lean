/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Source.Semantics

/-! # Publication accounting in source execution

The syntax's open-resource index agrees with the pending private publications.
Consequently a complete source execution resolves every initial or committed
resource, including when its publication fails.
-/

namespace Vegas.SourceProgram

open Interaction GameTheory.Math.Probability

variable {Player : Type} {L : IExpr}

/-- Pending resources, computed from publication status rather than raw binding.
An unopenable binding remains pending until its explicit reveal operation. -/
def pendingNames : {Γ : SourceCtx Player L} → State L Γ → Finset VarId
  | [], _ => ∅
  | (name, .privateData _ _) :: _, state =>
      let rest := pendingNames (fun _ _ h => state.get (.there h))
      if (state.get .here).2.isPending then insert name rest else rest
  | (_, .publicData _) :: _, state | (_, .publication _) :: _, state =>
      pendingNames (fun _ _ h => state.get (.there h))

private theorem mem_pendingNames_context {Γ : SourceCtx Player L}
    (state : State L Γ) {name : VarId} (member : name ∈ pendingNames state) :
    name ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil => simp [pendingNames] at member
  | cons entry tail ih =>
      obtain ⟨head, cell⟩ := entry
      cases cell with
      | publicData payload =>
          exact List.mem_cons_of_mem _ (ih _ member)
      | publication payload =>
          exact List.mem_cons_of_mem _ (ih _ member)
      | privateData owner payload =>
          simp only [pendingNames] at member
          split at member
          · rcases Finset.mem_insert.mp member with same | remaining
            · simp [same]
            · exact List.mem_cons_of_mem _ (ih _ remaining)
          · exact List.mem_cons_of_mem _ (ih _ member)

theorem pendingNames_of_privatePending {Γ : SourceCtx Player L}
    (state : State L Γ) (initial : PrivatePending state) :
    pendingNames state = privateNames Γ := by
  induction Γ with
  | nil => rfl
  | cons entry tail ih =>
      obtain ⟨name, cell⟩ := entry
      cases cell with
      | publicData payload => exact ih _ initial
      | publication payload => exact ih _ initial
      | privateData owner payload =>
          rcases initial with ⟨pending, rest⟩
          simp only [pendingNames, pending, Publication.isPending,
            if_true, privateNames]
          rw [ih _ rest]

/-- Resolving one resource removes exactly its name from pending accounting.
Unique names prevent a distinct cell from sharing that resource identifier. -/
theorem pendingNames_updatePrivate {Γ : SourceCtx Player L}
    {owner : Player} {payload : L.Ty} {name : VarId}
    (state : State L Γ) (source : HasVar Γ name (.privateData owner payload))
    (value : Publication (L.Val payload)) (resolved : value ≠ .pending)
    (unique : (Γ.map Prod.fst).Nodup) :
    pendingNames (updatePrivate state source value) = (pendingNames state).erase name := by
  induction Γ with
  | nil => cases source
  | cons entry tail ih =>
      obtain ⟨head, headCell⟩ := entry
      cases source with
      | here =>
          have absent : name ∉ pendingNames (fun _ _ h => state.get (.there h)) := by
            intro member
            exact (List.nodup_cons.mp unique).1 (mem_pendingNames_context _ member)
          simp only [updatePrivate, pendingNames, Env.get, Env.cons,
            Publication.isPending_eq_true]
          split_ifs <;> simp_all [Env.get]
      | there source =>
          have different : name ≠ head := by
            intro same
            exact (List.nodup_cons.mp unique).1 (same ▸ source.mem_map_fst)
          have tailEq := ih (fun _ _ h => state.get (.there h)) source
            (List.nodup_cons.mp unique).2
          cases headCell with
          | publicData _ =>
              simpa only [updatePrivate, pendingNames, Env.get, Env.cons] using tailEq
          | publication _ =>
              simpa only [updatePrivate, pendingNames, Env.get, Env.cons] using tailEq
          | privateData _ _ =>
              have erases (names : Finset VarId) :
                  (insert head names).erase name = insert head (names.erase name) :=
                Finset.erase_insert_of_ne (Ne.symm different)
              simp only [updatePrivate, pendingNames, Env.get, Env.cons]
              split_ifs <;> simp_all [Env.get]

/-- A private cell is unresolved only if its name occurs in pending accounting. -/
theorem mem_pendingNames_of_pending {Γ : SourceCtx Player L}
    {owner : Player} {payload : L.Ty} {name : VarId}
    (state : State L Γ) (source : HasVar Γ name (.privateData owner payload))
    (pending : (state.get source).2 = .pending) : name ∈ pendingNames state := by
  induction Γ with
  | nil => cases source
  | cons entry tail ih =>
      obtain ⟨head, headCell⟩ := entry
      cases source with
      | here => simp [pendingNames, pending, Publication.isPending]
      | there source =>
          have member := ih (fun _ _ h => state.get (.there h)) source pending
          cases headCell with
          | publicData _ => exact member
          | publication _ => exact member
          | privateData _ _ =>
              simp only [pendingNames]
              split <;> simp_all

/-- For a unique typed resource, membership in the pending index means that
the actual publication cell is pending, not merely a namesake. -/
theorem pending_of_mem_pendingNames {Γ : SourceCtx Player L}
    {owner : Player} {payload : L.Ty} {name : VarId}
    (state : State L Γ) (source : HasVar Γ name (.privateData owner payload))
    (unique : (Γ.map Prod.fst).Nodup) (member : name ∈ pendingNames state) :
    (state.get source).2 = .pending := by
  induction Γ with
  | nil => cases source
  | cons entry tail ih =>
      obtain ⟨head, headCell⟩ := entry
      cases source with
      | here =>
          have absent : name ∉ pendingNames (fun _ _ h => state.get (.there h)) := by
            intro occurs
            exact (List.nodup_cons.mp unique).1 (mem_pendingNames_context _ occurs)
          by_contra resolved
          apply absent
          simpa [pendingNames, resolved] using member
      | there source =>
          have different : name ≠ head := by
            intro same
            exact (List.nodup_cons.mp unique).1 (same ▸ source.mem_map_fst)
          apply ih (fun _ _ h => state.get (.there h)) source (List.nodup_cons.mp unique).2
          cases headCell with
          | publicData _ => exact member
          | publication _ => exact member
          | privateData _ _ =>
              simp only [pendingNames] at member
              split at member <;> simpa [different] using member

variable [DecidableEq Player] [IExpr.ResultTypes L]

/-- Every supported complete run discharges the source's pending resources.
The claim covers arbitrary policies, all sample outcomes, and publication
failure; it does not assume that any guard has an ordinary satisfying value. -/
theorem runWith_pending_empty {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) :
    ∀ (profile : BehavioralProfile program) (state : State L Γ)
      (registry : Registry Γ) (history : History Player L),
      (Γ.map Prod.fst).Nodup → pendingNames state = O →
      ∀ outcome ∈ (runWith program profile state registry history).support,
        pendingNames outcome = ∅ := by
  induction program with
  | ret payoffs =>
      intro profile state registry history unique accounts outcome supported
      have same : outcome = state := FinDist.mem_support_pure.mp supported
      simpa [same] using accounts
  | sample name fresh law next ih =>
      intro profile state registry history unique accounts outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      exact ih (afterSample profile) (Env.cons value state) registry.weaken history
        (by simp [fresh, unique]) accounts outcome supported
  | commit name owner fresh guard next ih =>
      intro profile state registry history unique accounts outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨value, _, supported⟩ := supported
      apply ih (afterCommit profile) (Env.cons (value, Publication.pending) state)
        _ _ (by simp [fresh, unique]) _ outcome supported
      simpa only [pendingNames, Env.cons_get_here, Env.cons_get_there,
        Publication.isPending, if_true, Env.get, Env.cons] using congrArg (insert name) accounts
  | reveal published owner name fresh source unresolved next ih =>
      intro profile state registry history unique accounts outcome supported
      simp only [runWith, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨disclose, _, supported⟩ := supported
      apply ih (afterReveal profile) _ _ _ (by simp [fresh, unique]) _ outcome supported
      simpa only [pendingNames, Env.cons_get_there, Env.get, Env.cons, accounts] using
        pendingNames_updatePrivate state source _ (resultPublication_ne_pending _) unique

/-- All publication obligations of a checked initial source game are resolved
at every supported terminal state, even for invalid or withholding policies. -/
theorem Initial.terminal_resolved (initial : Initial (Player := Player) (L := L))
    (profile : BehavioralProfile initial.program)
    (outcome : State L initial.program.terminalCtx)
    (supported : outcome ∈ (initial.run profile).support)
    {owner : Player} {payload : L.Ty} {name : VarId}
    (source : HasVar initial.program.terminalCtx name (.privateData owner payload)) :
    (outcome.get source).2 ≠ .pending := by
  have empty := runWith_pending_empty initial.program profile initial.state [] (fun _ => [])
    initial.namesNodup
    ((pendingNames_of_privatePending initial.state initial.privatePending).trans
      initial.accounts.symm) outcome supported
  intro pending
  have member := mem_pendingNames_of_pending outcome source pending
  simp [empty] at member

end Vegas.SourceProgram
