/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicies

/-! # Original-graph cursors and logical policy histories

The message-policy compiler retains the original graph while walking a suffix.
This file records that walk as a typed prefix and proves that both the policy
cursor and the projected own-action history are the ones determined by that
prefix.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

omit R in
/-- In a context with unique field names, typed lookup returns the supplied
reference. Thus callers need no auxiliary claim about the lookup algorithm. -/
theorem findVar_eq_some_of_nodup {context : VCtx Player L} {name : VarId}
    {binding : BindTy Player L} (unique : (context.map Prod.fst).Nodup)
    (source : HasVar context name binding) :
    findVar context name binding = some source := by
  induction context with
  | nil => exact nomatch source
  | cons head tail ih =>
      obtain ⟨headName, headBinding⟩ := head
      cases source with
      | here => simp [findVar]
      | there source =>
          have headNe : headName ≠ name := by
            intro h
            apply (List.nodup_cons.mp unique).1
            simpa [h] using source.mem_map_fst
          have pairNe : (headName, headBinding) ≠ (name, binding) := by
            intro h
            exact headNe (congrArg Prod.fst h)
          simp [findVar, pairNe, ih unique.tail source]

/-- Reading an owned immutable bind cell through the compiler projection
recovers the graph-level choice encoded in that cell. -/
theorem observedBindChoice_observe {target : VCtx Player L} (who : Player)
    (env : VEnv L target) (name : VarId) (payload : L.Ty)
    (source : HasVar target name (.sealed who (R.result payload)))
    (unique : (target.map Prod.fst).Nodup) :
    observedBindChoice who (observe who env) name payload =
      R.valueEquiv payload (env.get source) := by
  have hfind := findVar_eq_some_of_nodup unique source
  unfold observedBindChoice
  rw [hfind]
  have hcell : (observe who env).cells.get source = some (env.get source) := by
    cases source <;> simp [observe, Env.get]
  simp [hcell]

/-- A typed proof that `suffix` is reached after exactly `length` constructors
of `whole`. Unlike a numerical cursor, this retains the intermediate contexts. -/
inductive Prefix (Δ : VCtx Player L) : {Γ : VCtx Player L} → Graph Player L Γ Δ →
    {target : VCtx Player L} → Graph Player L target Δ → Nat → Type where
  | refl {Γ : VCtx Player L} (graph : Graph Player L Γ Δ) : Prefix Δ graph graph 0
  | sample {Γ : VCtx Player L} {name : VarId} {payload : L.Ty} {fresh} {law}
      {next : Graph Player L ((name, .pub payload) :: Γ) Δ}
      {target suffix n} (walk : Prefix Δ next (target := target) suffix n) :
      Prefix Δ (.sample name fresh law next) suffix (n + 1)
  | bind {Γ : VCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty} {fresh}
      {next : Graph Player L ((name, .sealed owner (R.result payload)) :: Γ) Δ}
      {target suffix n} (walk : Prefix Δ next (target := target) suffix n) :
      Prefix Δ (.bind (payload := payload) name owner fresh next) suffix (n + 1)
  | resolve {Γ : VCtx Player L} {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
      {fresh source checks}
      {next : Graph Player L ((outputName, .pub (R.result payload)) :: Γ) Δ}
      {target suffix n} (walk : Prefix Δ next (target := target) suffix n) :
      Prefix Δ (.resolve (payload := payload) outputName owner bindingName fresh source checks next)
        suffix (n + 1)

namespace Prefix

/-- Concatenate two typed graph-prefix witnesses. -/
def trans {first : Graph Player L Γ₀ Δ} {middle : Graph Player L Γ Δ}
    {target : VCtx Player L} {last : Graph Player L target Δ} {n m : Nat}
    (left : Prefix Δ first middle n) (right : Prefix Δ middle last m) :
    Prefix Δ first last (n + m) := by
  induction left with
  | refl => simpa using right
  | sample left ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Prefix.sample (ih right)
  | bind left ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Prefix.bind (ih right)
  | resolve left ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Prefix.resolve (ih right)

/-- Graph freshness preserves unique field names across a typed prefix. -/
theorem target_names_nodup {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (unique : (Γ₀.map Prod.fst).Nodup) :
    (Γ.map Prod.fst).Nodup := by
  induction walk with
  | refl => exact unique
  | sample walk ih => exact ih (List.nodup_cons.mpr ⟨by assumption, unique⟩)
  | bind walk ih => exact ih (List.nodup_cons.mpr ⟨by assumption, unique⟩)
  | resolve walk ih => exact ih (List.nodup_cons.mpr ⟨by assumption, unique⟩)

/-- The behavioral-policy tail selected by a typed graph prefix. -/
def policyTail (who : Player) : {Γ : VCtx Player L} →
    {whole : Graph Player L Γ Δ} → {target : VCtx Player L} →
    {suffix : Graph Player L target Δ} → {n : Nat} →
    Prefix Δ whole suffix n → BehavioralPolicy who whole → BehavioralPolicy who suffix
  | _, _, _, _, _, .refl _, policy => policy
  | _, _, _, _, _, .sample walk, policy => policyTail who walk policy
  | _, _, _, _, _, .bind walk, policy => policyTail who walk policy.2
  | _, _, _, _, _, .resolve walk, policy => policyTail who walk policy.2

/-- Restrict every player's policy to the same typed graph suffix. -/
def profileTail {whole : Graph Player L Γ₀ Δ} {suffix : Graph Player L Γ Δ}
    {length : Nat} (walk : Prefix Δ whole suffix length)
    (profile : BehavioralProfile whole) : BehavioralProfile suffix :=
  fun who => walk.policyTail who (profile who)

/-- At the phase selected by a typed prefix, compiling from the ambient graph
is definitionally the same command kernel as compiling its residual policy at
the corresponding suffix. -/
theorem compileAt_eq_suffixFrom
    {runtime : GraphRuntime Player L Δ} {origin : Graph Player L Γ₀ Δ}
    {cursor : Graph Player L Γ Δ} {target : VCtx Player L}
    {suffix : Graph Player L target Δ} {length site : Nat}
    (walk : Prefix Δ cursor suffix length) (who : Player)
    (policy : BehavioralPolicy who cursor) (history : List (Entry runtime))
    (view : runtime.application.View)
    (hpc : view.application.publicState.pc = site + length) :
    compileAt runtime who origin cursor policy site history view =
      compileAt runtime who origin suffix (policyTail who walk policy)
        (site + length) history view := by
  induction walk generalizing site with
  | refl => simp [policyTail]
  | sample walk ih =>
      simp only [compileAt]
      rw [if_neg]
      · have step := ih (site := site + 1) policy (by omega)
        simpa [policyTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
      · omega
  | bind walk ih =>
      simp only [compileAt]
      rw [dif_neg]
      · have step := ih (site := site + 1) policy.2 (by omega)
        simpa [policyTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
      · omega
  | resolve walk ih =>
      simp only [compileAt]
      rw [dif_neg]
      · have step := ih (site := site + 1) policy.2 (by omega)
        simpa [policyTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using step
      · omega

theorem compilePlayerPolicy_eq_suffix
    {runtime : GraphRuntime Player L Δ} {whole : Graph Player L Γ₀ Δ}
    {suffix : Graph Player L Γ Δ} {length : Nat}
    (walk : Prefix Δ whole suffix length) (who : Player)
    (policy : BehavioralPolicy who whole) (history : List (Entry runtime))
    (view : runtime.application.View)
    (hpc : view.application.publicState.pc = length) :
    compilePlayerPolicy runtime whole who policy history view =
      compileAt runtime who whole suffix (policyTail who walk policy)
        length history view := by
  simpa [compilePlayerPolicy] using
    compileAt_eq_suffixFrom (site := 0) walk who policy history view (by simpa using hpc)

end Prefix

/-- Exact agreement between a completed original-graph prefix and a logical
own-action history. Bind evidence is typed by its graph payload; resolve
evidence is tied to its original site. -/
inductive LogicalHistoryMatches {runtime : GraphRuntime Player L Δ}
    {target : VCtx Player L} (who : Player) (observation : Observation L who target)
    (history : List (Entry runtime)) :
    {Γ : VCtx Player L} → Graph Player L Γ Δ → Nat → Nat →
      List (OwnAction Player L) → Prop where
  | zero {Γ : VCtx Player L} (graph : Graph Player L Γ Δ) (site : Nat) :
      LogicalHistoryMatches who observation history graph site 0 []
  | sample {name : VarId} {payload : L.Ty} {fresh law next site fuel actions}
      (tail : LogicalHistoryMatches who observation history next (site + 1) fuel actions) :
      LogicalHistoryMatches who observation history (.sample name fresh law next)
        site (fuel + 1) actions
  | bind_other {name : VarId} {owner : Player} {payload : L.Ty}
      {fresh next site fuel actions}
      (hne : owner ≠ who)
      (tail : LogicalHistoryMatches who observation history next (site + 1) fuel actions) :
      LogicalHistoryMatches who observation history
        (.bind (payload := payload) name owner fresh next)
        site (fuel + 1) actions
  | bind_self {name : VarId} {payload : L.Ty} {fresh next site fuel actions choice}
      (hchoice : observedBindChoice who observation name payload = choice)
      (tail : LogicalHistoryMatches who observation history next (site + 1) fuel actions) :
      LogicalHistoryMatches who observation history (.bind (payload := payload) name who fresh next)
        site (fuel + 1) (OwnAction.bind who name payload choice :: actions)
  | resolve_other {outputName bindingName : VarId} {owner : Player} {payload : L.Ty}
      {fresh source checks next site fuel actions} (hne : owner ≠ who)
      (tail : LogicalHistoryMatches who observation history next (site + 1) fuel actions) :
      LogicalHistoryMatches who observation history
        (.resolve (payload := payload) outputName owner bindingName fresh source checks next)
        site (fuel + 1) actions
  | resolve_self {outputName bindingName : VarId} {payload : L.Ty}
      {fresh source checks next site fuel actions disclose}
      (hdisclose : (rememberedDisclosure history site).getD false = disclose)
      (tail : LogicalHistoryMatches who observation history next (site + 1) fuel actions) :
      LogicalHistoryMatches who observation history
        (.resolve (payload := payload) outputName who bindingName fresh source checks next)
        site (fuel + 1) (OwnAction.resolve who bindingName disclose :: actions)

/-- Projection of compiler memory and immutable owned fields recovers exactly
the graph own-action history certified by `LogicalHistoryMatches`. -/
theorem projectLogicalHistory_eq {runtime : GraphRuntime Player L Δ}
    {target : VCtx Player L} (who : Player) (observation : Observation L who target)
    (history : List (Entry runtime)) {Γ : VCtx Player L}
    {graph : Graph Player L Γ Δ} {site fuel : Nat} {actions : List (OwnAction Player L)}
    (agreement : LogicalHistoryMatches who observation history graph site fuel actions) :
    projectLogicalHistory who observation history graph site fuel = actions := by
  induction agreement with
  | zero graph site => cases graph <;> rfl
  | sample tail ih => simpa [projectLogicalHistory] using ih
  | bind_other hne tail ih => simp [projectLogicalHistory, hne, ih]
  | bind_self hchoice tail ih => simp [projectLogicalHistory, hchoice, ih]
  | resolve_other hne tail ih => simp [projectLogicalHistory, hne, ih]
  | resolve_self hdisclose tail ih => simp [projectLogicalHistory, hdisclose, ih]

end Vegas.GraphRuntime
