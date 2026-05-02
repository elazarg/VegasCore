import Vegas.Config

/-!
# Raw small-step semantics for Vegas

This file defines the first, raw `FDist`-valued small-step layer over the
existing runtime `World` shape from the FOSG bridge. It intentionally uses
`OmniscientOperationalProfile`, matching `outcomeDist`; the checked PMF/FOSG
layer is a separate bridge.
-/

namespace Vegas
namespace SmallStep

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Raw runtime worlds need a classical equality instance to be used as keys in
`FDist`. The fields include dependent programs and environments, so this is
not intended as computational data. -/
noncomputable instance instDecidableEqWorld :
    DecidableEq (World P L) :=
  Classical.decEq _

/-- Observable label for one raw Vegas step.

`tau` covers deterministic administrative steps (`letExpr` and `reveal`).
Sample and commit labels retain the realized value. -/
inductive Label (P : Type) [DecidableEq P] (L : IExpr) where
  | tau : Label P L
  | sample (b : L.Ty) (v : L.Val b) : Label P L
  | commit (who : P) (b : L.Ty) (v : L.Val b) : Label P L

noncomputable instance instDecidableEqLabel :
    DecidableEq (Label P L) :=
  Classical.decEq _

/-- One raw probabilistic small step. Non-terminal worlds have exactly one
outgoing distribution; terminal worlds have none. -/
inductive Step (σ : OmniscientOperationalProfile P L) :
    World P L → FDist (Label P L × World P L) → Prop where
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (env : VEnv L Γ) :
      Step σ
        ({ Γ := Γ, prog := .letExpr x e k, env := env } : World P L)
        (FDist.pure
          (Label.tau,
            ({ Γ := (x, .pub b) :: Γ
               prog := k
               env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub b)
                 (L.eval e (VEnv.erasePubEnv env)) env } : World P L)))
  | sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (env : VEnv L Γ) :
      Step σ
        ({ Γ := Γ, prog := .sample x D k, env := env } : World P L)
        (FDist.bind (L.evalDist D (VEnv.eraseSampleEnv env)) fun v =>
          FDist.pure
            (Label.sample b v,
              ({ Γ := (x, .pub b) :: Γ
                 prog := k
                 env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub b)
                   v env } : World P L)))
  | commit {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (env : VEnv L Γ) :
      Step σ
        ({ Γ := Γ, prog := .commit x who R k, env := env } : World P L)
        (FDist.bind (σ.commit who x R (VEnv.eraseEnv env)) fun v =>
          FDist.pure
            (Label.commit who b v,
              ({ Γ := (x, .hidden who b) :: Γ
                 prog := k
                 env := VEnv.cons (Player := P) (L := L) (x := x)
                   (τ := .hidden who b) v env } : World P L)))
  | reveal {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (env : VEnv L Γ) :
      Step σ
        ({ Γ := Γ, prog := .reveal y who x hx k, env := env } : World P L)
        (FDist.pure
          (Label.tau,
            ({ Γ := (y, .pub b) :: Γ
               prog := k
               env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
                 (show L.Val b from
                   VEnv.get (Player := P) (L := L) (x := x)
                     (τ := .hidden who b) env hx) env } : World P L)))

/-- A concrete labelled target with positive one-step mass from a source
world. -/
def StepSupport (σ : OmniscientOperationalProfile P L)
    (w : World P L) (lw : Label P L × World P L) : Prop :=
  ∃ d, Step σ w d ∧ lw ∈ d.support

/-- Multi-step reachability through supported raw small steps, recording the
realized labels. This is qualitative support reachability; weights are handled
by `labelDist`/`traceDist`. -/
inductive Steps (σ : OmniscientOperationalProfile P L) :
    World P L → List (Label P L) → World P L → Prop where
  | nil (w : World P L) : Steps σ w [] w
  | cons {w mid dst : World P L} {label : Label P L}
      {labels : List (Label P L)} :
      StepSupport σ w (label, mid) →
      Steps σ mid labels dst →
      Steps σ w (label :: labels) dst

/-- Structural core of the raw small-step evaluator. This is intentionally
constructor-for-constructor with `outcomeDist`; the public wrapper below
packages the arguments as a `World`. -/
noncomputable def runSmallStepCore (σ : OmniscientOperationalProfile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → VEnv L Γ → FDist (Outcome P)
  | _, .ret payoffs, env =>
      FDist.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, env =>
      runSmallStepCore σ k
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env)
  | _, .sample x D k, env =>
      FDist.bind (L.evalDist D (VEnv.eraseSampleEnv env)) fun v =>
        runSmallStepCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            v env)
  | _, .commit x who R k, env =>
      FDist.bind (σ.commit who x R (VEnv.eraseEnv env)) fun v =>
        runSmallStepCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who _) v env)
  | _, .reveal y _who _x (b := b) hx k, env =>
      runSmallStepCore σ k
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
          (show L.Val b from
            VEnv.get (Player := P) (L := L) (x := _x)
              (τ := .hidden _who b) env hx) env)

/-- Raw small-step evaluator over packaged worlds. -/
noncomputable def runSmallStep
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    FDist (Outcome P) :=
  runSmallStepCore σ w.prog w.env

/-- Raw small-step evaluator from the initial world of a checked program. -/
noncomputable def runInitialSmallStep
    (σ : OmniscientOperationalProfile P L) (g : WFProgram P L) :
    FDist (Outcome P) :=
  runSmallStep σ (World.initial g)

end SmallStep
end Vegas
