/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicyHistory

/-! # Extension laws for compiled logical histories -/

noncomputable section
namespace Vegas.GraphRuntime

open Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

namespace Prefix

/-- Lift an immutable field through the context extensions of a graph prefix. -/
def lift {origin target : VCtx Player L} {whole : Graph Player L origin Δ}
    {suffix : Graph Player L target Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) {name : VarId} {binding : BindTy Player L}
    (source : HasVar origin name binding) : HasVar target name binding :=
  match walk with
  | .refl _ => source
  | .sample tail => tail.lift (.there source)
  | .bind tail => tail.lift (.there source)
  | .resolve tail => tail.lift (.there source)

/-- Split the compiler's history scan at an actual typed graph cursor. -/
theorem projectLogicalHistory_append {runtime : GraphRuntime Player L Δ}
    {origin target observed : VCtx Player L} {whole : Graph Player L origin Δ}
    {suffix : Graph Player L target Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (who : Player)
    (observation : Observation L who observed) (history : List (Entry runtime))
    (site extra : Nat) :
    projectLogicalHistory who observation history whole site (length + extra) =
      projectLogicalHistory who observation history whole site length ++
        projectLogicalHistory who observation history suffix (site + length) extra := by
  induction walk generalizing site with
  | refl graph => cases graph <;> simp [projectLogicalHistory]
  | sample walk ih =>
      simpa [projectLogicalHistory, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (site + 1)
  | bind walk ih =>
      rw [Nat.add_right_comm _ 1 extra]
      simp only [projectLogicalHistory]
      split <;>
        simpa only [List.cons_append, List.cons.injEq, true_and,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (site + 1)
  | resolve walk ih =>
      rw [Nat.add_right_comm _ 1 extra]
      simp only [projectLogicalHistory]
      split <;>
        simpa only [List.cons_append, List.cons.injEq, true_and,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (site + 1)

/-- Adding a fresh immutable graph field preserves the entire earlier
own-action projection, including the recovered values of earlier bindings. -/
theorem projectLogicalHistory_cons {runtime : GraphRuntime Player L Δ}
    {origin target : VCtx Player L} {whole : Graph Player L origin Δ}
    {suffix : Graph Player L target Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (who : Player)
    (env : VEnv L target) (history : List (Entry runtime))
    {name : VarId} {binding : BindTy Player L} (value : L.Val binding.base)
    (unique : (target.map Prod.fst).Nodup) (fresh : name ∉ target.map Prod.fst)
    (site : Nat) :
    projectLogicalHistory who (observe who (VEnv.cons (x := name) value env))
        history whole site length =
      projectLogicalHistory who (observe who env) history whole site length := by
  have extended : (((name, binding) :: target).map Prod.fst).Nodup :=
    List.nodup_cons.mpr ⟨fresh, unique⟩
  induction walk generalizing site with
  | refl graph => cases graph <;> rfl
  | sample walk ih =>
      simpa [projectLogicalHistory] using ih env unique fresh (site + 1) extended
  | bind walk ih =>
      simp only [projectLogicalHistory]
      split
      · rename_i same
        subst same
        have ref := walk.lift HasVar.here
        rw [observedBindChoice_observe _ _ _ _ (.there ref) extended,
          observedBindChoice_observe _ _ _ _ ref unique]
        simp only [VEnv.cons_get_there]
        exact congrArg (List.cons _) (ih env unique fresh (site + 1) extended)
      · exact ih env unique fresh (site + 1) extended
  | resolve walk ih =>
      simp only [projectLogicalHistory]
      split
      · exact congrArg (List.cons _) (ih env unique fresh (site + 1) extended)
      · exact ih env unique fresh (site + 1) extended

/-- Completing a bind at the current cursor appends precisely the owner's
graph action to the full original-graph history scan. -/
theorem projectLogicalHistory_bind {runtime : GraphRuntime Player L Δ}
    {origin : VCtx Player L} {whole : Graph Player L origin Δ}
    {name : VarId} {owner : Player} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {tail : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
    {length : Nat} (walk : Prefix Δ whole (.bind name owner fresh tail) length)
    (who : Player) (env : VEnv L Γ) (history : List (Entry runtime))
    (choice : PublicationResult (L.Val payload)) (unique : (Γ.map Prod.fst).Nodup) :
    projectLogicalHistory who
        (observe who (VEnv.cons (x := name) (τ := .sealed owner (R.result payload))
          ((R.valueEquiv payload).symm choice) env))
        history whole 0 (length + 1) =
      projectLogicalHistory who (observe who env) history whole 0 length ++
        (if owner = who then [OwnAction.bind owner name payload choice] else []) := by
  rw [walk.projectLogicalHistory_append who _ history 0 1,
    walk.projectLogicalHistory_cons who env history _ unique fresh 0]
  simp only [Nat.zero_add, projectLogicalHistory]
  split
  · rename_i same
    subst same
    rw [observedBindChoice_observe _ _ _ _ HasVar.here
      (List.nodup_cons.mpr ⟨fresh, unique⟩)]
    simp only [VEnv.cons_get_here, Equiv.apply_symm_apply]
    cases tail <;> rfl
  · cases tail <;> rfl

/-- Completing a resolve appends the remembered logical Boolean, even when
the public result is failure for both possible Booleans. -/
theorem projectLogicalHistory_resolve {runtime : GraphRuntime Player L Δ}
    {origin : VCtx Player L} {whole : Graph Player L origin Δ}
    {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
    {fresh : outputName ∉ Γ.map Prod.fst}
    {source : HasVar Γ bindingName (.sealed owner (R.result payload))}
    {checks : List (GuardCheck (R := R)
      ((outputName, .pub (R.result payload)) :: Γ))}
    {tail : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
    {length : Nat}
    (walk : Prefix Δ whole (.resolve outputName owner bindingName fresh source checks tail) length)
    (who : Player) (env : VEnv L Γ) (history : List (Entry runtime))
    (result : PublicationResult (L.Val payload)) (disclose : Bool)
    (remembered : rememberedDisclosure history length = some disclose)
    (unique : (Γ.map Prod.fst).Nodup) :
    projectLogicalHistory who
        (observe who (VEnv.cons (x := outputName) (τ := .pub (R.result payload))
          ((R.valueEquiv payload).symm result) env))
        history whole 0 (length + 1) =
      projectLogicalHistory who (observe who env) history whole 0 length ++
        (if owner = who then [OwnAction.resolve owner bindingName disclose] else []) := by
  rw [walk.projectLogicalHistory_append who _ history 0 1,
    walk.projectLogicalHistory_cons who env history _ unique fresh 0]
  simp only [Nat.zero_add, projectLogicalHistory, remembered, Option.getD_some]
  split <;> cases tail <;> rfl

/-- Public chance extends the immutable context without adding a player action. -/
theorem projectLogicalHistory_sample {runtime : GraphRuntime Player L Δ}
    {origin : VCtx Player L} {whole : Graph Player L origin Δ}
    {name : VarId} {payload : L.Ty} {fresh : name ∉ Γ.map Prod.fst}
    {law : PublicDist (L := L) Γ payload}
    {tail : Graph Player L ((name, .pub payload) :: Γ) Δ}
    {length : Nat} (walk : Prefix Δ whole (.sample name fresh law tail) length)
    (who : Player) (env : VEnv L Γ) (history : List (Entry runtime))
    (value : L.Val payload) (unique : (Γ.map Prod.fst).Nodup) :
    projectLogicalHistory who (observe who (VEnv.cons (x := name) (τ := .pub payload) value env))
        history whole 0 (length + 1) =
      projectLogicalHistory who (observe who env) history whole 0 length := by
  rw [walk.projectLogicalHistory_append who _ history 0 1,
    walk.projectLogicalHistory_cons who env history _ unique fresh 0]
  cases tail <;> simp [projectLogicalHistory]

end Prefix

/-- The resolve marker, if any, contributed by one authenticated entry at a
given graph site. -/
def entryDisclosureAt {runtime : GraphRuntime Player L Δ}
    (entry : Entry runtime) (site : Nat) : Option Bool :=
  match entry.command with
  | .privateCommand (.rememberDisclosure disclose) =>
      if entry.beforeView.application.publicState.pc = site then some disclose else none
  | _ => none

theorem rememberedDisclosure_append_of_entry_none
    {runtime : GraphRuntime Player L Δ} (history : List (Entry runtime))
    (entry : Entry runtime) (site : Nat) (hentry : entryDisclosureAt entry site = none) :
    rememberedDisclosure (history ++ [entry]) site = rememberedDisclosure history site := by
  induction history with
  | nil =>
      cases hcommand : entry.command with
      | privateCommand command =>
          cases command with
          | prepare => simp [rememberedDisclosure, hcommand]
          | rememberDisclosure =>
              simp [entryDisclosureAt, hcommand] at hentry
              simpa [rememberedDisclosure, hcommand] using hentry
      | submit => simp [rememberedDisclosure, hcommand]
      | replay => simp [rememberedDisclosure, hcommand]
      | wait => simp [rememberedDisclosure, hcommand]
  | cons head tail ih =>
      unfold rememberedDisclosure at ih ⊢
      simp only [List.cons_append, List.findSome?_cons]
      split <;> simp_all

/-- It is enough for the appended entry to avoid only the resolve sites scanned
by this projection. In particular, a marker at the new current site preserves
all strictly earlier logical history. -/
theorem projectLogicalHistory_append_of_no_disclosure_range
    {runtime : GraphRuntime Player L Δ} (who : Player)
    {target : VCtx Player L} (observation : Observation L who target)
    (history : List (Entry runtime)) (entry : Entry runtime) :
    ∀ {Γ : VCtx Player L} (graph : Graph Player L Γ Δ) (site fuel : Nat),
      (∀ scanned, site ≤ scanned → scanned < site + fuel →
        entryDisclosureAt entry scanned = none) →
      projectLogicalHistory who observation (history ++ [entry]) graph site fuel =
        projectLogicalHistory who observation history graph site fuel := by
  intro Γ graph site fuel hentry
  induction fuel generalizing Γ site with
  | zero => cases graph <;> rfl
  | succ fuel ih =>
      have htail : ∀ scanned, site + 1 ≤ scanned → scanned < site + 1 + fuel →
          entryDisclosureAt entry scanned = none := by
        intro scanned hlo hhi
        exact hentry scanned (by omega) (by omega)
      cases graph with
      | ret => rfl
      | sample name fresh law next => simpa [projectLogicalHistory] using ih next (site + 1) htail
      | bind name owner fresh next =>
          simp only [projectLogicalHistory]
          split <;> simp [ih next (site + 1) htail]
      | resolve outputName owner bindingName fresh source checks next =>
          rw [projectLogicalHistory, projectLogicalHistory]
          rw [rememberedDisclosure_append_of_entry_none history entry site
            (hentry site (by omega) (by omega))]
          split <;> simp [ih next (site + 1) htail]

theorem entryDisclosureAt_remember_ne
    {runtime : GraphRuntime Player L Δ} (entry : Entry runtime) (disclose : Bool)
    (hcommand : entry.command = .privateCommand (.rememberDisclosure disclose))
    (site : Nat) (hne : entry.beforeView.application.publicState.pc ≠ site) :
    entryDisclosureAt entry site = none := by
  simp [entryDisclosureAt, hcommand, hne]

@[simp] theorem entryDisclosureAt_prepare
    {runtime : GraphRuntime Player L Δ} (entry : Entry runtime) (slot : Nat) (raw : Raw L)
    (hcommand : entry.command = .privateCommand (.prepare slot raw)) (site : Nat) :
    entryDisclosureAt entry site = none := by simp [entryDisclosureAt, hcommand]

theorem preparedRaw_append_prepare (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (site : Nat) (raw : Raw L) (missing : preparedRaw history site = none) :
    preparedRaw (history ++ [⟨before, .privateCommand (.prepare site raw)⟩]) site =
      some raw := by
  unfold preparedRaw at missing ⊢
  rw [List.findSome?_append, missing]
  simp

theorem rememberedDisclosure_append_remember (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (site : Nat) (disclose : Bool) (missing : rememberedDisclosure history site = none)
    (atSite : before.application.publicState.pc = site) :
    rememberedDisclosure
        (history ++ [⟨before, .privateCommand (.rememberDisclosure disclose)⟩]) site =
      some disclose := by
  unfold rememberedDisclosure at missing ⊢
  rw [List.findSome?_append, missing]
  simp [atSite]

theorem preparedRaw_append_prepare_ne (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (marked queried : Nat) (raw : Raw L) (hne : marked ≠ queried) :
    preparedRaw (history ++ [⟨before, .privateCommand (.prepare marked raw)⟩]) queried =
      preparedRaw history queried := by
  unfold preparedRaw
  rw [List.findSome?_append]
  simp [hne]

theorem preparedRaw_append_remember (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (disclose : Bool) (queried : Nat) :
    preparedRaw (history ++ [⟨before, .privateCommand (.rememberDisclosure disclose)⟩]) queried =
      preparedRaw history queried := by
  unfold preparedRaw
  rw [List.findSome?_append]
  simp

theorem rememberedDisclosure_append_prepare (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (marked : Nat) (raw : Raw L) (queried : Nat) :
    rememberedDisclosure
        (history ++ [⟨before, .privateCommand (.prepare marked raw)⟩]) queried =
      rememberedDisclosure history queried := by
  apply rememberedDisclosure_append_of_entry_none
  simp [entryDisclosureAt]

theorem rememberedDisclosure_append_remember_ne (runtime : GraphRuntime Player L Δ)
    (history : List (Entry runtime)) (before : runtime.application.View)
    (marked queried : Nat) (disclose : Bool)
    (atMarked : before.application.publicState.pc = marked) (hne : marked ≠ queried) :
    rememberedDisclosure
        (history ++ [⟨before, .privateCommand (.rememberDisclosure disclose)⟩]) queried =
      rememberedDisclosure history queried := by
  apply rememberedDisclosure_append_of_entry_none
  simp [entryDisclosureAt, atMarked, hne]

end Vegas.GraphRuntime
