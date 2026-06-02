/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Visibility

/-!
# Context and environment projections

Per-player views (`viewVCtx`) and the public fragment (`pubVCtx`), their
erasures into plain `Ctx`/`Env`, the matching `VEnv` projections, and the
sampling convention. These are the bridges between visibility-aware Vegas
contexts and the plain expression-language contexts consumed by `IExpr`.
-/

namespace Vegas

/-! ## Views and public projection -/

/-- Can player `p` observe a binding of type `τ`? True for public bindings
and for hidden bindings owned by `p`. -/
abbrev canSee {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) (τ : BindTy Player L) : Bool :=
  τ.visibility.canSee p

/-- Player-local visible subcontext. -/
def viewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    (p : Player) : VCtx Player L → VCtx Player L
  | [] => []
  | (x, τ) :: Γ =>
      if canSee p τ then (x, τ) :: viewVCtx p Γ else viewVCtx p Γ

/-- The view's name set is contained in the full context's name set: anything
visible to `p` is in the original context. -/
theorem viewVCtx_map_fst_sub {Player : Type} [DecidableEq Player] {L : IExpr}
    {x : VarId} {p : Player} {Γ : VCtx Player L} :
    x ∈ (viewVCtx p Γ).map Prod.fst → x ∈ Γ.map Prod.fst := by
  induction Γ with
  | nil =>
    intro h
    simp [viewVCtx] at h
  | cons hd tl ih =>
    obtain ⟨y, τ⟩ := hd
    cases hsee : canSee (Player := Player) (L := L) p τ with
    | false =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = viewVCtx p tl := by
        simp [viewVCtx, hsee]
      rw [hview] at h
      exact List.mem_cons_of_mem _ (ih h)
    | true =>
      intro h
      have hview : viewVCtx p ((y, τ) :: tl) = (y, τ) :: viewVCtx p tl := by
        simp [viewVCtx, hsee]
      rw [hview] at h
      simp only [List.map, List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

/-- Every binding in a player's view is either public or owned by that player. -/
theorem viewVCtx_owner {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {p : Player} {x : VarId} {τ : BindTy Player L}
    (h : VHasVar (viewVCtx p Γ) x τ) :
    τ.owner = none ∨ τ.owner = some p := by
  induction Γ with
  | nil => cases h
  | cons hd tl ih =>
      obtain ⟨headName, headTy⟩ := hd
      simp only [viewVCtx] at h
      split at h
      · cases h with
        | here =>
            rename_i hsee
            cases τ with
            | mk base vis =>
                cases vis with
                | pub => simp [BindTy.owner]
                | hidden owner =>
                    simp [canSee, Visibility.canSee] at hsee
                    right
                    simp [BindTy.owner, hsee]
        | there htail => exact ih htail
      · exact ih h

namespace VHasVar

/-- Lift a `VHasVar` proof in `viewVCtx p Γ` to a `VHasVar` in `Γ`. This is the
typed witness bridge used whenever a player-visible context is embedded back
into the full context. -/
def ofViewVCtx {Player : Type} [DecidableEq Player] {L : IExpr}
    {p : Player} {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (viewVCtx p Γ) x τ → VHasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    simp only [viewVCtx]
    split
    · intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    · intro h
      exact .there (ih h)

end VHasVar

/-- Public-only fragment of a visibility context. -/
def pubVCtx {Player : Type} {L : IExpr} : VCtx Player L → VCtx Player L
  | [] => []
  | (x, ⟨τ, .pub⟩) :: Γ => (x, ⟨τ, .pub⟩) :: pubVCtx Γ
  | (_, ⟨_, .hidden _⟩) :: Γ => pubVCtx Γ

/-- Every binding in the public projection is public. -/
theorem pubVCtx_owner {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L}
    (h : VHasVar (pubVCtx Γ) x τ) : τ.owner = none := by
  induction Γ with
  | nil => cases h
  | cons hd tl ih =>
      obtain ⟨headName, headTy⟩ := hd
      cases headTy with
      | mk base vis =>
          cases vis with
          | pub =>
              simp only [pubVCtx] at h
              cases h with
              | here => rfl
              | there htail => exact ih htail
          | hidden owner =>
              simp only [pubVCtx] at h
              exact ih h

namespace VHasVar

def ofPubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (pubVCtx Γ) x τ → VHasVar Γ x τ := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      simp only [pubVCtx]
      intro h
      match h with
      | .here => exact .here
      | .there h' => exact .there (ih h')
    | ⟨υ, .hidden q⟩ =>
      simp only [pubVCtx]
      intro h
      exact .there (ih h)

end VHasVar

/-! ## Erasure to plain `Ctx`

Erasure is the bridge to the embedded language: `IExpr.eval` and
`IExpr.evalDist` consume plain `Env Val (Ctx L.Ty)`s, so every Vegas
construct must erase its visibility-annotated context before evaluating
expressions. Two erasures coexist:

* `eraseVCtx` (full): used by operational kernels and by commit guards after
  projecting to the actor's `viewVCtx`.
* `erasePubVCtx` (public-only): used by samples, payoff expressions, and
  surface deterministic bindings — these may not depend on hidden state.

The composition `eraseVCtx ∘ pubVCtx = erasePubVCtx` is the key
commutation lemma (`eraseVCtx_pubVCtx`) that lets `erasePubVCtx`-shaped
goals be reduced to `eraseVCtx`-shaped reasoning. -/

/-- Erase visibility annotations, keeping variable names and base types. -/
def eraseVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, τ) :: Γ => (x, τ.base) :: eraseVCtx Γ

@[simp] theorem eraseVCtx_nil {Player : Type} {L : IExpr} :
    @eraseVCtx Player L [] = [] := rfl

@[simp] theorem eraseVCtx_cons {Player : Type} {L : IExpr}
    {x : VarId} {τ : BindTy Player L} {Γ : VCtx Player L} :
    eraseVCtx ((x, τ) :: Γ) = (x, τ.base) :: eraseVCtx Γ := rfl

/-- Erasing visibility annotations preserves the variable-name projection. -/
theorem eraseVCtx_map_fst {Player : Type} {L : IExpr} {Γ : VCtx Player L} :
    (eraseVCtx Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
      obtain ⟨x, τ⟩ := hd
      simp [eraseVCtx, ih]

/-- Erase visibility, keeping only public variables. -/
def erasePubVCtx {Player : Type} {L : IExpr} :
    VCtx Player L → Ctx L.Ty
  | [] => []
  | (x, ⟨τ, .pub⟩) :: Γ => (x, τ) :: erasePubVCtx Γ
  | (_, ⟨_, .hidden _⟩) :: Γ => erasePubVCtx Γ

@[simp] theorem erasePubVCtx_nil {Player : Type} {L : IExpr} :
    @erasePubVCtx Player L [] = [] := rfl

@[simp] theorem erasePubVCtx_cons_pub {Player : Type} {L : IExpr}
    {x : VarId} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, .pub τ) :: Γ) = (x, τ) :: erasePubVCtx Γ := rfl

@[simp] theorem erasePubVCtx_cons_hidden {Player : Type} {L : IExpr}
    {x : VarId} {p : Player} {τ : L.Ty} {Γ : VCtx Player L} :
    erasePubVCtx ((x, .hidden p τ) :: Γ) = erasePubVCtx Γ := rfl

/-- Every name in `erasePubVCtx Γ` also appears in any player's view of `Γ`,
since public bindings are visible to everyone. -/
theorem erasePubVCtx_map_fst_sub_viewVCtx
    {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {who : Player} :
    ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst →
      x ∈ (viewVCtx who Γ).map Prod.fst := by
  induction Γ with
  | nil => simp [erasePubVCtx]
  | cons a Γ' ih =>
    intro x hx
    match a with
    | (y, ⟨b, .pub⟩) =>
      simp only [erasePubVCtx_cons_pub, viewVCtx, canSee,
        Visibility.canSee_pub, if_true, List.map_cons, List.mem_cons] at hx ⊢
      exact hx.elim Or.inl (fun h => Or.inr (ih x h))
    | (y, ⟨b, .hidden p⟩) =>
      simp only [erasePubVCtx_cons_hidden, viewVCtx] at hx ⊢
      by_cases h : canSee who (.hidden p b)
      · simp only [h, ite_true, List.map_cons, List.mem_cons]
        right; exact ih x hx
      · simp only [h]
        exact ih x hx

/-- Erasure of pubVCtx equals erasePubVCtx. -/
theorem eraseVCtx_pubVCtx {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} :
    eraseVCtx (pubVCtx Γ) = erasePubVCtx Γ := by
  induction Γ with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨x, τ⟩ := hd
    match τ with
    | ⟨b, .pub⟩ => simp [pubVCtx, erasePubVCtx, ih]
    | ⟨b, .hidden p⟩ => simp [pubVCtx, erasePubVCtx, ih]

namespace HasVar

/-- A public variable is present in every player's erased view. -/
def pubToView {Player : Type} [DecidableEq Player] {L : IExpr}
    {Γ : VCtx Player L} {p : Player} {x : VarId} {τ : L.Ty} :
    HasVar (erasePubVCtx Γ) x τ →
      HasVar (eraseVCtx (viewVCtx p Γ)) x τ := by
  induction Γ with
  | nil =>
      intro h
      cases h
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      cases σ with
      | mk base visibility =>
          cases visibility with
          | pub =>
              simp only [erasePubVCtx_cons_pub, viewVCtx, canSee,
                Visibility.canSee_pub, if_true, eraseVCtx_cons]
              intro h
              cases h with
              | here => exact .here
              | there htail => exact .there (ih htail)
          | hidden owner =>
              simp only [erasePubVCtx_cons_hidden, viewVCtx]
              by_cases hsee : canSee p (.hidden owner base)
              · simp only [hsee, if_true, eraseVCtx_cons]
                intro h
                exact .there (ih h)
              · simp only [hsee]
                intro h
                exact ih h

end HasVar

/-- A VHasVar proof induces a HasVar proof in the erased context. -/
def VHasVar.toErased {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar Γ x τ → HasVar (eraseVCtx Γ) x τ.base
  | .here => .here
  | .there h => .there h.toErased

/-- A HasVar in eraseVCtx lifts back to a VHasVar. -/
def HasVar.toVHasVar {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → {x : VarId} → {b : L.Ty} →
    HasVar (eraseVCtx Γ) x b →
    (τ : BindTy Player L) × VHasVar Γ x τ × PLift (τ.base = b)
  | (_, τ) :: _, _, _, .here => ⟨τ, .here, ⟨rfl⟩⟩
  | _ :: _, _, _, .there h =>
    let ⟨τ', hv, ⟨hb⟩⟩ := toVHasVar h
    ⟨τ', .there hv, ⟨hb⟩⟩

/-- A `HasVar` in `erasePubVCtx Γ` lifts to a `VHasVar` in `pubVCtx Γ` of the
corresponding `pub` binding. The structural inverse to `VHasVar.toErasedPub`. -/
def HasVar.toVHasVarPub {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : L.Ty} :
    HasVar (erasePubVCtx Γ) x τ → VHasVar (pubVCtx Γ) x (.pub τ) := by
  induction Γ with
  | nil => intro h; exact nomatch h
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      simp only [erasePubVCtx, pubVCtx]; intro h
      cases h with
      | here => exact .here
      | there h' => exact .there (ih h')
    | ⟨υ, .hidden p⟩ =>
      simp only [erasePubVCtx, pubVCtx]; intro h; exact ih h

/-- A VHasVar in pubVCtx induces a HasVar in erasePubVCtx. -/
def VHasVar.toErasedPub {Player : Type} {L : IExpr}
    {Γ : VCtx Player L} {x : VarId} {τ : BindTy Player L} :
    VHasVar (pubVCtx Γ) x τ → HasVar (erasePubVCtx Γ) x τ.base := by
  intro h
  have h' := h.toErased
  rw [eraseVCtx_pubVCtx] at h'
  exact h'

/-! ## VEnv projections matching the erasures

Each `VEnv L Γ` admits projections matching the context-level operations
above. `eraseEnv` and `erasePubEnv` are the two consumed by the semantics
(passed to `IExpr.eval`/`evalDist`); the others stay in the `VEnv` world for
intra-Vegas reasoning. -/

namespace VEnv

/-- Erase visibility from a VEnv, producing a plain Env over eraseVCtx. -/
def eraseEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv L Γ →
    Env L.Val (eraseVCtx Γ)
  | [], _ => Env.empty L.Val
  | (_, _) :: _, env =>
    Env.cons (env.get .here) (eraseEnv (fun a b h => env a b (.there h)))

/-- Erase visibility, keeping only public variables. -/
def erasePubEnv {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} → VEnv L Γ →
    Env L.Val (erasePubVCtx Γ)
  | [], _ => Env.empty L.Val
  | ((_, ⟨_, .pub⟩) :: Γ'), env =>
    Env.cons (env.get .here)
      (erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h)))
  | ((_, ⟨_, .hidden _⟩) :: Γ'), env =>
    erasePubEnv (Γ := Γ') (fun a b h => env a b (VHasVar.there h))

/-- Pointwise formula for `erasePubEnv`: looking up at an erased-pub position
equals looking up the original VEnv at the corresponding `pub` binding. -/
@[simp] theorem erasePubEnv_get {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : L.Ty}
    (hx : HasVar (erasePubVCtx Γ) x τ) :
    erasePubEnv env x τ hx =
      env x (.pub τ) (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx)) := by
  induction Γ generalizing x τ with
  | nil => exact nomatch hx
  | cons hd tl ih =>
    obtain ⟨y, σ⟩ := hd
    match σ with
    | ⟨υ, .pub⟩ =>
      cases hx with
      | here => rfl
      | there hx' =>
        simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
          (ih (env := fun a b h => env a b (VHasVar.there h)) hx')
    | ⟨υ, .hidden p⟩ =>
      simpa [VEnv.erasePubEnv, HasVar.toVHasVarPub] using
        (ih (env := fun a b h => env a b (VHasVar.there h)) hx)

/-- Pointwise formula for `eraseEnv`: looking up at the erased position
produced by `VHasVar.toErased` equals the original lookup. -/
@[simp] theorem eraseEnv_get_of_erased {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv (Player := Player) L Γ)
    {x : VarId} {τ : BindTy Player L}
    (hx : VHasVar Γ x τ) :
    eraseEnv env x τ.base hx.toErased = env x τ hx := by
  induction hx with
  | here => rfl
  | there hx ih =>
    simpa [VEnv.eraseEnv] using (ih (env := fun a b h => env a b (VHasVar.there h)))

/-- HEq variant of `eraseEnv_get_of_erased`, going through `HasVar.toVHasVar`:
the erased-env lookup at `hx` is HEq to the lookup along the lifted-and-then-
re-erased proof. Useful where dependent typing makes a strict equality
unstatable. -/
theorem eraseEnv_toErased_eq {Player : Type} {L : IExpr} :
    {Γ : VCtx Player L} →
    (env : VEnv (Player := Player) L Γ) →
    {x : VarId} → {b : L.Ty} →
    (hx : HasVar (eraseVCtx Γ) x b) →
    HEq (env.eraseEnv x
        (hx.toVHasVar (Player := Player) (L := L)).1.base
        (hx.toVHasVar (Player := Player) (L := L)).2.1.toErased)
      (env.eraseEnv x b hx)
  | _ :: _, _, _, _, .here => HEq.rfl
  | _ :: _, env, _, _, .there hx =>
      eraseEnv_toErased_eq (fun a b h => env a b (.there h)) hx

/-- Project a VEnv to the visible subcontext of player `p`. -/
def toView {Player : Type} [DecidableEq Player] {L : IExpr} (p : Player)
    {Γ : VCtx Player L} (env : VEnv L Γ) :
    VEnv (Player := Player) L (viewVCtx p Γ) :=
  fun x τ h => env x τ h.ofViewVCtx

/-- Project a VEnv to the public subcontext. -/
def toPub {Player : Type} {L : IExpr} {Γ : VCtx Player L}
    (env : VEnv L Γ) :
    VEnv (Player := Player) L (pubVCtx Γ) :=
  fun x τ h => env x τ h.ofPubVCtx

end VEnv

/-! ## Sampling convention

A naming layer: sample distributions are evaluated in the public-only
subcontext, because nature has no private knowledge — drawing must depend
solely on observable state. The abbreviation `sampleVCtx := pubVCtx`
documents this design choice; the two functions are definitionally equal. -/

/-- Sampling is public nature: distributions are evaluated in the public
context and the sampled result is bound as a fresh public variable. -/
abbrev sampleVCtx {Player : Type} {L : IExpr} (Γ : VCtx Player L) : VCtx Player L :=
  pubVCtx Γ

namespace VEnv

/-- Erase the public fragment of a VEnv for evaluating a sample distribution. -/
def eraseSampleEnv {Player : Type} {L : IExpr}
    {Γ : VCtx Player L}
    (env : VEnv L Γ) :
    Env L.Val (erasePubVCtx Γ) :=
  VEnv.erasePubEnv env

end VEnv


end Vegas
