import Vegas.Core.WF

/-!
# Surface Vegas language

`VegasLang` is a small surface syntax over the concrete `ExprSimple` language
that lowers to the generic `VegasCore simpleExpr`. This concrete
specialization is deliberate: nullable yields rely on `BaseTy.option`,
`CommitPayloadTy`, and `DefaultVal`.

The surface keeps the existing core actions, adds administrative `let`
bindings, and lowers guarded public `yield`s through internal `option T`
commitments. User-written commit payloads are restricted by `CommitPayloadTy`,
so a surface program cannot explicitly commit an optional value.

This is an elaborated typed layer: yield nodes already name the internal
hidden commitment and the public reveal. A thinner parser-level language can
instead generate the hidden commitment name during elaboration/lowering,
translate ordinary reads to the public reveal, translate owner-private reads to
the hidden commitment, and emit `VegasCore` directly.

Quit handlers are deliberately not part of this syntax yet.
-/

namespace Vegas

variable {P : Type} [DecidableEq P]

/-- Surface Vegas syntax. This specializes the protocol core to
`simpleExpr`, adds administrative `let` bindings, and nullable yield sugar. -/
inductive VegasLang (P : Type) [DecidableEq P] :
    VCtx P simpleExpr → Type where
  /-- Terminate with public payoff expressions. -/
  | ret {Γ : VCtx P simpleExpr}
      (payoffs : List (P × Expr (erasePubVCtx Γ) .int)) :
      VegasLang P Γ
  /-- Deterministic public binding. This is erased by lowering; it is not a
  core protocol event. -/
  | letExpr {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (e : Expr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, .pub b) :: Γ)) :
      VegasLang P Γ
  /-- Public sample. -/
  | sample {Γ : VCtx P simpleExpr} (x : VarId) {b : BaseTy}
      (D : DistExpr (erasePubVCtx Γ) b)
      (k : VegasLang P ((x, .pub b) :: Γ)) :
      VegasLang P Γ
  /-- Strategic hidden commitment whose guard is accepted as-is. Surface
  payloads cannot be explicitly nullable. -/
  | commit {Γ : VCtx P simpleExpr} (x : VarId) (who : P) {b : BaseTy}
      [CommitPayloadTy b]
      (R : Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) .bool)
      (k : VegasLang P ((x, .hidden who b) :: Γ)) :
      VegasLang P Γ
  /-- Public strategic move, lowered as a nullable hidden commitment followed
  by a public reveal of the optional value. The two names are separate because
  `VegasCore` contexts are SSA-style: the revealed public alias must be fresh
  rather than reusing the hidden commitment name. A source elaborator may
  generate the hidden name and keep it invisible to ordinary source reads. -/
  | yield {Γ : VCtx P simpleExpr} (secret pubVar : VarId) (who : P)
      {b : BaseTy} [CommitPayloadTy b] [DefaultVal b]
      (R : Expr ((secret, b) :: eraseVCtx (viewVCtx who Γ)) .bool)
      (k : VegasLang P
        ((pubVar, .pub (BaseTy.option b)) ::
          (secret, .hidden who (BaseTy.option b)) :: Γ)) :
      VegasLang P Γ
  /-- Reveal a hidden commitment as a fresh public alias. -/
  | reveal {Γ : VCtx P simpleExpr} (y : VarId) (who : P) (x : VarId)
      {b : BaseTy}
      (hx : VHasVar Γ x (.hidden who b))
      (k : VegasLang P ((y, .pub b) :: Γ)) :
      VegasLang P Γ
namespace VegasLang

/-- Typed substitution environment used while lowering surface syntax. The
source context may contain administrative lets that do not exist in the target
core context. Public variables therefore translate to expressions; hidden
variables must still translate to hidden core variables because reveals open
stored commitments. -/
structure LowerEnv (P : Type) [DecidableEq P]
    (Γ Δ : VCtx P simpleExpr) where
  pub :
    {x : VarId} → {b : BaseTy} →
      HasVar (erasePubVCtx Γ) x b → Expr (erasePubVCtx Δ) b
  view :
    (who : P) → {x : VarId} → {b : BaseTy} →
      HasVar (eraseVCtx (viewVCtx who Γ)) x b →
        Expr (eraseVCtx (viewVCtx who Δ)) b
  hidden :
    {x : VarId} → {who : P} → {b : BaseTy} →
      VHasVar Γ x (.hidden who b) → VHasVar Δ x (.hidden who b)

namespace LowerEnv

def id (Γ : VCtx P simpleExpr) : LowerEnv P Γ Γ where
  pub := fun {x} {_} h => .var x h
  view := fun _ {x} {_} h => .var x h
  hidden := fun h => h

def expr {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    {b : BaseTy} (e : Expr (erasePubVCtx Γ) b) :
    Expr (erasePubVCtx Δ) b :=
  e.substVars env.pub

def dist {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    {b : BaseTy} (D : DistExpr (erasePubVCtx Γ) b) :
    DistExpr (erasePubVCtx Δ) b :=
  D.substVars env.pub

def actionExpr {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (who : P) {x : VarId} {a b : BaseTy}
    (e : Expr ((x, a) :: eraseVCtx (viewVCtx who Γ)) b) :
    Expr ((x, a) :: eraseVCtx (viewVCtx who Δ)) b :=
  e.substVars (by
    intro y ty h
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.view who htail).weaken)

def consPublic {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) {b : BaseTy} :
    LowerEnv P ((x, .pub b) :: Γ) ((x, .pub b) :: Δ) where
  pub := by
    intro y ty h
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.pub htail).weaken
  view := by
    intro who y ty h
    simp only [viewVCtx, canSee, Visibility.canSee_pub, if_true,
      eraseVCtx_cons] at h ⊢
    cases h with
    | here => exact .var x .here
    | there htail => exact (env.view who htail).weaken
  hidden := by
    intro y who ty h
    cases h with
    | there htail => exact .there (env.hidden htail)

def consHidden {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) (owner : P) {b : BaseTy} :
    LowerEnv P ((x, .hidden owner b) :: Γ) ((x, .hidden owner b) :: Δ) where
  pub := fun h => env.pub h
  view := by
    intro who y ty h
    by_cases hsee :
        canSee who (BindTy.hidden (L := simpleExpr) owner b)
    · simp only [viewVCtx, hsee, if_true, eraseVCtx_cons] at h ⊢
      cases h with
      | here => exact .var x .here
      | there htail => exact (env.view who htail).weaken
    · simp only [viewVCtx, hsee] at h ⊢
      exact env.view who h
  hidden := by
    intro y who ty h
    cases h with
    | here => exact .here
    | there htail => exact .there (env.hidden htail)

def aliasPublic {Γ Δ : VCtx P simpleExpr} (env : LowerEnv P Γ Δ)
    (x : VarId) {b : BaseTy} (e : Expr (erasePubVCtx Δ) b) :
    LowerEnv P ((x, .pub b) :: Γ) Δ where
  pub := by
    intro y ty h
    cases h with
    | here => exact e
    | there htail => exact env.pub htail
  view := by
    intro who y ty h
    simp only [viewVCtx, canSee, Visibility.canSee_pub, if_true,
      eraseVCtx_cons] at h
    cases h with
    | here => exact e.publicToView who
    | there htail => exact env.view who htail
  hidden := by
    intro y who ty h
    cases h with
    | there htail => exact env.hidden htail

end LowerEnv

/-- Lower surface Vegas to core syntax, erasing administrative `let` bindings
through the lowering environment. -/
def lowerWith :
    {Γ Δ : VCtx P simpleExpr} → LowerEnv P Γ Δ →
      VegasLang P Γ → VegasCore P simpleExpr Δ
  | _, _, env, .ret payoffs =>
      .ret (payoffs.map fun payoff => (payoff.1, env.expr payoff.2))
  | _, _, env, .letExpr x e k =>
      lowerWith (env.aliasPublic x (env.expr e)) k
  | _, _, env, .sample x D k =>
      .sample x (env.dist D) (lowerWith (env.consPublic x) k)
  | _, _, env, @VegasLang.commit _ _ _ x who _ _ R k =>
      .commit x who (env.actionExpr who R)
        (lowerWith (env.consHidden x who) k)
  | _, _, env, @VegasLang.yield _ _ _ secret pubVar who b _ _ R k =>
      .commit secret who (b := BaseTy.option b)
        (Expr.nullableCommitGuard (env.actionExpr who R))
        (.reveal pubVar who secret .here
          (lowerWith ((env.consHidden secret who).consPublic pubVar) k))
  | _, _, env, .reveal y who x hx k =>
      .reveal y who x (env.hidden hx)
        (lowerWith (env.consPublic y) k)

/-- Lower surface Vegas to the maintained core syntax. -/
def lower {Γ : VCtx P simpleExpr} (p : VegasLang P Γ) :
    VegasCore P simpleExpr Γ :=
  lowerWith (LowerEnv.id Γ) p

end VegasLang

end Vegas
