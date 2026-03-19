import Vegas.Examples

/-!
# Action graph semantics for Vegas

A canonical, order-independent representation of Vegas programs as action
graphs.
Two programs that differ only in the ordering of independent events (e.g., two
commits for different players) have the same event graph, making commutativity
structural rather than requiring per-pair theorems.

## Design

Inspired by compiler IRs (Kotlin coroutine state machine). The action graph is
extracted
from a `VegasSimple` by walking its structure and recording dependencies via
`exprVars`/`distExprVars`/`viewCtx`.
-/

namespace Vegas


/-- The kind of event in the action graph. -/
inductive EventKind where
  | letExpr  -- deterministic expression binding
  | sample   -- nature's random choice
  | commit   -- player's strategic choice
  | reveal   -- making a hidden value public
  deriving DecidableEq, Repr

/-- A node in the action graph. -/
structure EventNode where
  id : VarId          -- the variable this node binds
  kind : EventKind    -- what kind of event
  deps : List VarId   -- variables this node reads
  deriving DecidableEq, Repr


/-- A value tagged with its base type. -/
structure TaggedVal where
  base : BaseTy
  val : Val base

instance : DecidableEq TaggedVal := by
  intro ⟨b₁, v₁⟩ ⟨b₂, v₂⟩
  cases b₁ <;> cases b₂
  · -- int, int
    exact if h : v₁ = v₂
      then .isTrue (by subst h; rfl)
      else .isFalse (by intro heq; cases heq; exact h rfl)
  · exact .isFalse (by intro h; cases h)
  · exact .isFalse (by intro h; cases h)
  · -- bool, bool
    exact if h : v₁ = v₂
      then .isTrue (by subst h; rfl)
      else .isFalse (by intro heq; cases heq; exact h rfl)

/-- A partial assignment of variable values. -/
def PartialEnv := VarId → Option TaggedVal

instance : Inhabited PartialEnv := ⟨fun _ => none⟩

/-- The empty partial environment. -/
def PartialEnv.empty : PartialEnv := fun _ => none

/-- Extend a partial environment with a single binding. -/
def PartialEnv.set (pe : PartialEnv) (x : VarId) (v : TaggedVal) : PartialEnv :=
  fun y => if y = x then some v else pe y


/-- State of action-graph execution. -/
structure Config where
  pending : List EventNode   -- events not yet fired
  env     : PartialEnv       -- resolved variable values

/-- A node is ready when all its dependencies are resolved. -/
def EventNode.ready (e : EventNode) (c : Config) : Bool :=
  e.deps.all (fun x => (c.env x).isSome)

/-- The events that can fire right now. -/
def Config.readyEvents (c : Config) : List EventNode :=
  c.pending.filter (·.ready c)

/-- No pending events remain. -/
def Config.terminal (c : Config) : Prop := c.pending = []

instance : Decidable (Config.terminal c) :=
  inferInstanceAs (Decidable (c.pending = []))


/-- One step: fire a ready node, recording its value. -/
structure Step (c₁ c₂ : Config) where
  node : EventNode
  value : TaggedVal
  hmem : node ∈ c₁.pending
  hready : node.ready c₁ = true
  henv : c₂.env = c₁.env.set node.id value
  hpending : c₂.pending = c₁.pending.erase node


/-- A complete execution: a sequence of steps from one config to another. -/
inductive Execution : Config → Config → Type where
  | done {c : Config} : Execution c c
  | step {c₁ c₂ c₃ : Config} : Step c₁ c₂ → Execution c₂ c₃ → Execution c₁ c₃

/-- Length of an execution (number of steps). -/
def Execution.length : Execution c₁ c₂ → Nat
  | .done => 0
  | .step _ rest => 1 + rest.length


/-- Extract the event graph from a VegasSimple. Walks the program structure and
    builds one EventNode per binding site.

    Dependency computation follows the current Vegas protocol structure:
    - `letExpr x e k`: deps = `exprVars e`
    - `sample x τ m D k`: deps = `distExprVars D`
    - `commit x who acts R k`: deps = all vars visible to `who` in Γ
    - `reveal y who x hx k`: deps = `[x]` -/
def VegasSimple.extractEvents : VegasSimple Γ → List EventNode
  | .ret _ => []
  | .letExpr x e k =>
    { id := x, kind := .letExpr, deps := exprVars e } ::
    VegasSimple.extractEvents k
  | .sample x _τ _m D k =>
    { id := x, kind := .sample, deps := distExprVars D } ::
    VegasSimple.extractEvents k
  | .commit x who _acts _R k =>
    { id := x, kind := .commit,
      deps := (viewCtx who Γ).map Prod.fst } ::
    VegasSimple.extractEvents k
  | .reveal y _who x _hx k =>
    { id := y, kind := .reveal, deps := [x] } ::
    VegasSimple.extractEvents k

/-- Build a PartialEnv from a typed EnvSimple by looking up each variable in Γ. -/
noncomputable def initPartialEnv : (Γ : CtxSimple) → EnvSimple Γ → PartialEnv
  | [], _ => PartialEnv.empty
  | (x, τ) :: Γ', env =>
    let rest := initPartialEnv Γ' (fun a b h => env a b (.there h))
    rest.set x ⟨τ.base, env.get .here⟩

/-- Build initial Config from a VegasSimple and an initial EnvSimple.
    The initial partial env is populated from the given EnvSimple Γ
    (the "already bound" variables). -/
noncomputable def VegasSimple.initConfig (p : VegasSimple Γ) (env : EnvSimple Γ) : Config where
  pending := VegasSimple.extractEvents p
  env := initPartialEnv Γ env


/-- A PartialEnv is consistent with an EnvSimple Γ when every variable
    in Γ maps to its correct value. -/
def PartialEnv.consistent (pe : PartialEnv) {Γ : CtxSimple} (env : EnvSimple Γ) : Prop :=
  ∀ x τ (h : HasVarSimple Γ x τ), pe x = some ⟨τ.base, env.get h⟩

/-- Reconstruct a typed EnvSimple from a PartialEnv, if all variables
    in Γ are resolved with the correct base types. -/
noncomputable def PartialEnv.toEnv? (pe : PartialEnv) :
    (Γ : CtxSimple) → Option (EnvSimple Γ)
  | [] => some EnvSimple.empty
  | (x, τ) :: Γ' =>
    match pe x with
    | none => none
    | some ⟨b, v⟩ =>
      match decEq b τ.base with
      | .isTrue h =>
        match pe.toEnv? Γ' with
        | none => none
        | some env' =>
          let v' : Val τ.base := by
            cases h
            exact v
          some (EnvSimple.cons v' env')
      | .isFalse _ => none

-- Commutativity: sets with distinct keys commute
theorem PartialEnv.set_comm (pe : PartialEnv) (x y : VarId)
    (vx vy : TaggedVal) (hne : x ≠ y) :
    (pe.set x vx).set y vy = (pe.set y vy).set x vx := by
  funext z
  simp only [PartialEnv.set]
  split <;> split <;> simp_all

-- Get after set (same key)
@[simp] theorem PartialEnv.set_get_same (pe : PartialEnv) (x : VarId)
    (v : TaggedVal) : (pe.set x v) x = some v := by
  simp [PartialEnv.set]

-- Get after set (different key)
@[simp] theorem PartialEnv.set_get_diff (pe : PartialEnv) (x y : VarId)
    (v : TaggedVal) (hne : y ≠ x) : (pe.set x v) y = pe y := by
  simp [PartialEnv.set, hne]

-- Nodup of mapped list is preserved by erase
private theorem nodup_map_erase [DecidableEq α]
    {f : α → β} {l : List α} {a : α}
    (h : (l.map f).Nodup) : ((l.erase a).map f).Nodup := by
  exact h.sublist (List.erase_sublist.map f)

-- After erasing a node from a nodup-mapped list, its image is gone
private theorem nodup_map_not_mem_erase [DecidableEq α]
    {f : α → β} {l : List α} {n : α}
    (hnd : (l.map f).Nodup) (hmem : n ∈ l) :
    f n ∉ (l.erase n).map f := by
  induction l with
  | nil => contradiction
  | cons b l' ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hfb, hnd'⟩ := hnd
    by_cases hbn : b = n
    · subst hbn; rw [List.erase_cons_head]; exact hfb
    · have hn_in : n ∈ l' := by
        rcases List.mem_cons.mp hmem with rfl | h
        · exact absurd rfl hbn
        · exact h
      have hbeq : (b == n) = false := beq_eq_false_iff_ne.mpr hbn
      simp only [List.erase_cons, hbeq, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.mem_cons] at *
      push_neg
      exact ⟨fun heq => hfb (heq ▸ List.mem_map.mpr ⟨n, hn_in, rfl⟩), ih hnd' hn_in⟩

-- initPartialEnv produces a consistent PartialEnv (requires no shadowing)
theorem initPartialEnv_consistent (Γ : CtxSimple) (env : EnvSimple Γ)
    (hwf : WFCtx Γ) : (initPartialEnv Γ env).consistent env := by
  intro x τ h
  induction Γ with
  | nil => exact nomatch h
  | cons binding Γ' ih =>
    obtain ⟨x', τ'⟩ := binding
    simp only [initPartialEnv]
    cases h with
    | here =>
      simp [PartialEnv.set_get_same]
    | there h' =>
      have hne : x ≠ x' := by
        intro heq; subst heq
        have hnd : (x :: Γ'.map Prod.fst).Nodup := hwf
        rw [List.nodup_cons] at hnd
        exact absurd (HasVar.mem_map_fst h') hnd.1
      rw [PartialEnv.set_get_diff _ _ _ _ hne]
      have hnd : (x' :: Γ'.map Prod.fst).Nodup := hwf
      rw [List.nodup_cons] at hnd
      exact ih (fun a b h => env a b (.there h)) hnd.2 h'


/-- Walk a VegasSimple to compute the weight of assigning `tv` to variable `id`,
    given profile σ and current partial env `pe`. Returns 0 if the node
    is not found or env reconstruction fails. -/
noncomputable def VegasSimple.nodeWeight (σ : ProfileSimple) (pe : PartialEnv) :
    VegasSimple Γ → VarId → TaggedVal → ℚ≥0
  | .ret _, _, _ => 0
  | .letExpr x _ k, id, tv =>
      if x = id then 1 else VegasSimple.nodeWeight σ pe k id tv
  | .sample x τ m D k, id, tv =>
      if x = id then
        match decEq tv.base τ.base with
        | .isTrue h =>
          match pe.toEnv? (distCtx τ m Γ) with
          | some env => (evalDistExpr D env) (h ▸ tv.val)
          | none => 0
        | .isFalse _ => 0
      else VegasSimple.nodeWeight σ pe k id tv
  | .commit x who (b := b) acts R k, id, tv =>
      if x = id then
        match decEq tv.base b with
        | .isTrue h =>
          match pe.toEnv? (viewCtx who Γ) with
          | some view => (σ.commit who x acts R view) (h ▸ tv.val)
          | none => 0
        | .isFalse _ => 0
      else VegasSimple.nodeWeight σ pe k id tv
  | .reveal y _ _ _ k, id, tv =>
      if y = id then 1 else VegasSimple.nodeWeight σ pe k id tv

/-- Weight of a step under a profile σ: looks up the node in the VegasSimple
    and computes the weight from the pre-step partial env. -/
noncomputable def Step.weight (σ : ProfileSimple) (p : VegasSimple Γ)
    (s : Step c₁ c₂) : ℚ≥0 :=
  VegasSimple.nodeWeight σ c₁.env p s.node.id s.value

/-- Weight of a complete execution (product of step weights). -/
noncomputable def Execution.weight (σ : ProfileSimple) (p : VegasSimple Γ) :
    Execution c₁ c₂ → ℚ≥0
  | .done => 1
  | .step s rest => s.weight σ p * rest.weight σ p


/-- Values assigned to each variable id during an execution. -/
def Execution.assignments : Execution c₁ c₂ → VarId → Option TaggedVal
  | .done, _ => none
  | .step s rest, x =>
      if s.node.id = x then some s.value else rest.assignments x

/-- A step with `node.id ≠ x` does not change `env x`. -/
theorem Step.env_unchanged (s : Step c₁ c₂) (hne : s.node.id ≠ x) :
    c₂.env x = c₁.env x := by
  rw [s.henv]
  exact PartialEnv.set_get_diff c₁.env s.node.id x s.value hne.symm

/-- Assignments only touches ids that are in the pending list. -/
theorem Execution.assignments_none_of_not_mem
    (exec : Execution c₁ c₂) (x : VarId)
    (h : x ∉ c₁.pending.map EventNode.id) :
    exec.assignments x = none := by
  induction exec with
  | done => rfl
  | step s rest ih =>
    simp only [Execution.assignments]
    have hne : s.node.id ≠ x := by
      intro heq; exact h (List.mem_map.mpr ⟨s.node, s.hmem, heq⟩)
    rw [if_neg hne]
    exact ih (fun hm => h (by
      rw [s.hpending] at hm
      exact (List.erase_sublist.map EventNode.id).subset hm))

/-- After a complete execution, `env x` equals the assigned value (if any)
    or the initial env (if no node wrote to `x`).
    Requires SSA (unique node ids among pending). -/
theorem execution_env_at {c₁ c₂ : Config}
    (exec : Execution c₁ c₂) (hterm : c₂.terminal)
    (huniq : (c₁.pending.map EventNode.id).Nodup) (x : VarId) :
    c₂.env x = match exec.assignments x with
      | some v => some v
      | none => c₁.env x := by
  induction exec with
  | done => rfl
  | @step _ cmid _ s rest ih =>
    have huniq' : (cmid.pending.map EventNode.id).Nodup := by
      rw [s.hpending]; exact nodup_map_erase huniq
    have ih' := ih hterm huniq'
    -- ih' : c₃✝.env x = match rest.assignments x with ...
    simp only [Execution.assignments]
    by_cases hsx : s.node.id = x
    · -- s.node.id = x: this step assigned to x
      rw [if_pos hsx]
      -- Goal: c₃✝.env x = some s.value
      -- rest.assignments x = none (x was erased from pending)
      have hgone : x ∉ cmid.pending.map EventNode.id := by
        rw [s.hpending, ← hsx]
        exact nodup_map_not_mem_erase huniq s.hmem
      have hnone := rest.assignments_none_of_not_mem x hgone
      rw [hnone] at ih'
      -- ih' : c₃✝.env x = cmid.env x (match on none reduces)
      -- Goal: c₃✝.env x = some s.value
      rw [ih', s.henv, ← hsx, PartialEnv.set_get_same]
    · -- s.node.id ≠ x: this step didn't touch x
      rw [if_neg hsx]
      -- Goal: c₃✝.env x = match rest.assignments x with ...  | none => c₁✝.env x
      -- From ih': c₃✝.env x = match rest.assignments x with ... | none => c₂✝.env x
      -- And c₂✝.env x = c₁✝.env x (step didn't change x)
      rw [s.env_unchanged hsx] at ih'
      exact ih'

/-- Two complete executions that assign the same value at each node id
    produce the same final environment, regardless of firing order.
    Requires SSA (unique node ids). -/
theorem execution_env_unique {c₁ c_term₁ c_term₂ : Config}
    (exec₁ : Execution c₁ c_term₁)
    (exec₂ : Execution c₁ c_term₂)
    (hterm₁ : c_term₁.terminal) (hterm₂ : c_term₂.terminal)
    (huniq : (c₁.pending.map EventNode.id).Nodup)
    (hsame : exec₁.assignments = exec₂.assignments) :
    c_term₁.env = c_term₂.env := by
  funext x
  rw [execution_env_at exec₁ hterm₁ huniq x,
      execution_env_at exec₂ hterm₂ huniq x, hsame]


namespace ActionGraphExamples

open Examples in
/-- Extract event graph from matching pennies. -/
def mpEvents : List EventNode := VegasSimple.extractEvents matchingPennies

example :
    mpEvents.map (fun n => (n.id, n.kind, n.deps)) =
      [(0, EventKind.commit, []), (1, EventKind.commit, []),
        (2, EventKind.reveal, [0]), (3, EventKind.reveal, [1])] := by
  decide

open Examples in
/-- Extract event graph from conditioned game. -/
def cgEvents : List EventNode := VegasSimple.extractEvents conditionedGame

example :
    cgEvents.map (fun n => (n.id, n.kind, n.deps)) =
      [(0, EventKind.commit, []), (2, EventKind.reveal, [0]),
        (1, EventKind.commit, [2]), (3, EventKind.reveal, [1])] := by
  decide

end ActionGraphExamples

end Vegas
