import Vegas.WF

/-!
# Surface Vegas language

`VegasLang` is a small surface syntax over the concrete `ExprSimple` language
that lowers to the generic `VegasCore simpleExpr`. This concrete
specialization is deliberate: nullable yields rely on `BaseTy.option`,
`CommitPayloadTy`, and `DefaultVal`.

The surface keeps the existing core actions, adds simultaneous yield phases, and
lowers guarded public `yield`s through internal `option T` commitments.
User-written commit payloads are restricted by `CommitPayloadTy`, so a surface
program cannot explicitly commit an optional value.

This is an elaborated typed layer: yield nodes already name the internal hidden
commitment and the public reveal. A thinner parser-level language can instead
generate the hidden commitment name during elaboration/lowering, translate
ordinary reads to the public reveal, translate owner-private reads to the hidden
commitment, and emit `VegasCore` directly.

Quit handlers are deliberately not part of this syntax yet.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

def Expr.weakenAfterHeadVCtx {P : Type} {Γ : VCtx P simpleExpr}
    {x : VarId} {τ b : BaseTy}
    (pref : VCtx P simpleExpr)
    (e : Expr ((x, τ) :: eraseVCtx Γ) b) :
    Expr ((x, τ) :: eraseVCtx (pref ++ Γ)) b :=
  -- Preserve the proposed action at the head while inserting an accumulated
  -- hidden prefix underneath it.
  match pref with
  | [] => e
  | (y, σ) :: rest =>
      (Expr.weakenAfterHeadVCtx rest e).weakenAfterHead
        (y := y) (σ := σ.base)

/-- A simultaneous yield phase. All guards are typed over the original
pre-phase context `Γ`, not over the hidden-prefix index, so a guard cannot
mention another yield from the same phase. Lowering commits every yielded value
first and only then reveals them. -/
inductive VegasYieldPhase (P : Type) [DecidableEq P]
    (Γ : VCtx P simpleExpr) :
    VCtx P simpleExpr → VCtx P simpleExpr → Type where
  | nil {pref : VCtx P simpleExpr} :
      VegasYieldPhase P Γ pref (pref ++ Γ)
  | yield {pref final : VCtx P simpleExpr}
      (secret pubVar : VarId) (who : P)
      {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
      (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
      (rest : VegasYieldPhase P Γ
        ((secret, ⟨BaseTy.option b, .hidden who⟩) :: pref) final) :
      VegasYieldPhase P Γ pref
        ((pubVar, ⟨BaseTy.option b, .pub⟩) :: final)

namespace VegasYieldPhase

def actors {Γ pref final : VCtx P simpleExpr} :
    VegasYieldPhase P Γ pref final → List P
  | .nil => []
  | @VegasYieldPhase.yield _ _ _ _ _ _ _ who _ _ _ _ rest =>
      who :: actors rest

def DistinctActors {Γ pref final : VCtx P simpleExpr}
    (phase : VegasYieldPhase P Γ pref final) : Prop :=
  phase.actors.Nodup

def carriesPrefix {Γ pref final : VCtx P simpleExpr}
    (phase : VegasYieldPhase P Γ pref final)
    {x : VarId} {τ : BindTy P simpleExpr} :
    VHasVar (pref ++ Γ) x τ → VHasVar final x τ :=
  match phase with
  | .nil => fun h => h
  | @VegasYieldPhase.yield _ _ Γ pref _ _ _ _ _ _ _ _ rest =>
      fun h =>
        VHasVar.there
          (carriesPrefix rest (VHasVar.there h))

/-- Lower a simultaneous yield phase by committing all yielded values first and
then revealing them. Later guards are weakened across earlier hidden
commitments, but their syntax still comes from the original pre-phase context. -/
def lowerWith {Γ : VCtx P simpleExpr} :
    {pref final : VCtx P simpleExpr} →
      VegasYieldPhase P Γ pref final → VegasCore P simpleExpr final →
        VegasCore P simpleExpr (pref ++ Γ)
  | _, _, .nil, k => k
  | pref, _, @VegasYieldPhase.yield _ _ Γ _ _
      secret pubVar who b _ _ R rest, k =>
      .commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard (R.weakenAfterHeadVCtx pref))
        (lowerWith rest
          (.reveal pubVar who secret (carriesPrefix rest VHasVar.here) k))

@[simp] theorem lowerWith_nil {Γ pref : VCtx P simpleExpr}
    (k : VegasCore P simpleExpr (pref ++ Γ)) :
    lowerWith (VegasYieldPhase.nil (P := P) (Γ := Γ) (pref := pref)) k = k :=
  rfl

end VegasYieldPhase

/-- Surface Vegas syntax. This mirrors `VegasCore`, specializes it to
`simpleExpr`, and adds simultaneous yield phases and nullable yield sugar. -/
inductive VegasLang (P : Type) [DecidableEq P] :
    VCtx P simpleExpr → Type where
  /-- Terminate with public payoff expressions. -/
  | ret {Γ : VCtx P simpleExpr}
      (payoffs : List (P × Expr (erasePubVCtx Γ) .int)) :
      VegasLang P Γ
  /-- Deterministic public binding. This lowers to core `letExpr`. -/
  | letExpr {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (e : Expr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, ⟨b, .pub⟩) :: Γ)) :
      VegasLang P Γ
  /-- Public sample. -/
  | sample {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (D : DistExpr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, ⟨b, .pub⟩) :: Γ)) :
      VegasLang P Γ
  /-- Strategic hidden commitment whose guard is accepted as-is. Surface
  payloads cannot be explicitly nullable. -/
  | commit {Γ : VCtx P simpleExpr} (x : VarId) (who : P) {b : BaseTy}
      [CommitPayloadTy b]
      (R : Expr ((x, b) :: eraseVCtx Γ) .bool)
      (k : VegasLang P ((x, ⟨b, .hidden who⟩) :: Γ)) :
      VegasLang P Γ
  /-- Public strategic move, lowered as a nullable hidden commitment followed
  by a public reveal of the optional value. The two names are separate because
  `VegasCore` contexts are SSA-style: the revealed public alias must be fresh
  rather than reusing the hidden commitment name. A source elaborator may
  generate the hidden name and keep it invisible to ordinary source reads. -/
  | yield {Γ : VCtx P simpleExpr} (secret pubVar : VarId) (who : P)
      {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
      (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
      (k : VegasLang P
        ((pubVar, ⟨BaseTy.option b, .pub⟩) ::
          (secret, ⟨BaseTy.option b, .hidden who⟩) :: Γ)) :
      VegasLang P Γ
  /-- Reveal a hidden commitment as a fresh public alias. -/
  | reveal {Γ : VCtx P simpleExpr} (y : VarId) (who : P) (x : VarId)
      {b : BaseTy}
      (hx : VHasVar Γ x ⟨b, .hidden who⟩)
      (k : VegasLang P ((y, ⟨b, .pub⟩) :: Γ)) :
      VegasLang P Γ
  /-- Present a same-phase collection of nullable public yields. Guards are
  checked against the pre-phase context, and distinct actors are required at
  the surface. -/
  | simultaneous {Γ Δ : VCtx P simpleExpr}
      (phase : VegasYieldPhase P Γ [] Δ)
      (hactors : phase.DistinctActors)
      (k : VegasLang P Δ) :
      VegasLang P Γ

namespace VegasLang

/-- Public alias for simultaneous yield phases under the `VegasLang`
namespace. -/
abbrev Phase (P : Type) [DecidableEq P] :
    VCtx P simpleExpr → VCtx P simpleExpr → Type :=
  fun Γ Δ => VegasYieldPhase P Γ [] Δ

/-- Lower surface Vegas to the maintained core syntax. -/
def lower :
    {Γ : VCtx P simpleExpr} → VegasLang P Γ → VegasCore P simpleExpr Γ
  | _, .ret payoffs => .ret payoffs
  | _, .letExpr x e k => .letExpr x e (lower k)
  | _, .sample x D k => .sample x D (lower k)
  | _, @VegasLang.commit _ _ _ x who _ _ R k => .commit x who R (lower k)
  | _, @VegasLang.yield _ _ _ secret pubVar who b _ _ R k =>
      .commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R)
        (.reveal pubVar who secret .here (lower k))
  | _, .reveal y who x hx k => .reveal y who x hx (lower k)
  | _, .simultaneous phase _ k => VegasYieldPhase.lowerWith phase (lower k)

@[simp] theorem lower_ret
    {Γ : VCtx P simpleExpr}
    (payoffs : List (P × Expr (erasePubVCtx Γ) .int)) :
    lower (VegasLang.ret (P := P) payoffs) =
      VegasCore.ret payoffs := rfl

@[simp] theorem lower_simultaneous
    {Γ Δ : VCtx P simpleExpr}
    (phase : VegasYieldPhase P Γ [] Δ)
    (hactors : phase.DistinctActors)
    (k : VegasLang P Δ) :
    lower (VegasLang.simultaneous phase hactors k) =
      VegasYieldPhase.lowerWith phase (lower k) := rfl

@[simp] theorem lower_yield {Γ : VCtx P simpleExpr}
    (secret pubVar : VarId) (who : P) {b : BaseTy}
    [CommitPayloadTy b] [DefaultVal b]
    (R : Expr ((secret, b) :: eraseVCtx Γ) .bool)
    (k : VegasLang P
      ((pubVar, ⟨BaseTy.option b, .pub⟩) ::
        (secret, ⟨BaseTy.option b, .hidden who⟩) :: Γ)) :
    lower (VegasLang.yield secret pubVar who R k) =
      VegasCore.commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard R)
        (VegasCore.reveal pubVar who secret VHasVar.here (lower k)) := rfl

end VegasLang

end Vegas
