import Vegas.WFProgram

/-!
# Vegas runtime configurations

This file contains the protocol/runtime configuration layer shared by
operational semantics and game-theoretic bridges. It deliberately does not
import FOSG: FOSG is one semantic view of these configurations, not their
definition.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A Vegas runtime configuration: a typed program suffix paired with an
environment for its current context. -/
structure World (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ

namespace World

/-- The initial runtime world associated with a checked Vegas program. -/
def initial (g : WFProgram P L) : World P L where
  Γ := g.Γ
  prog := g.prog
  env := g.env

end World

/-- Vegas terminal configurations are exactly `ret` configurations. -/
def terminal (w : World P L) : Prop :=
  match w.prog with
  | .ret _ => True
  | _ => False

@[simp] theorem terminal_ret
    {Γ : VCtx P L} {env : VEnv L Γ}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    terminal ({ Γ := Γ, prog := VegasCore.ret payoffs, env := env } : World P L) := by
  simp [terminal]

@[simp] theorem terminal_letExpr
    {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    terminal ({ Γ := Γ, prog := VegasCore.letExpr x e k, env := env } : World P L) =
      False := rfl

@[simp] theorem terminal_sample
    {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    terminal ({ Γ := Γ, prog := VegasCore.sample x D k, env := env } : World P L) =
      False := rfl

@[simp] theorem terminal_commit
    {Γ : VCtx P L} {env : VEnv L Γ} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
    terminal ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L) =
      False := rfl

@[simp] theorem terminal_reveal
    {Γ : VCtx P L} {env : VEnv L Γ} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    terminal ({ Γ := Γ, prog := VegasCore.reveal y who x hx k, env := env } : World P L) =
      False := rfl

/-- Number of operational syntax nodes remaining before a Vegas program
reaches `ret`, ignoring probabilistic branching because branching changes only
environments, not the continuation shape. -/
def syntaxSteps :
    {Γ : VCtx P L} → VegasCore P L Γ → Nat
  | _, .ret _ => 0
  | _, .letExpr _ _ k => syntaxSteps k + 1
  | _, .sample _ _ k => syntaxSteps k + 1
  | _, .commit _ _ _ k => syntaxSteps k + 1
  | _, .reveal _ _ _ _ k => syntaxSteps k + 1

@[simp] theorem syntaxSteps_ret
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    syntaxSteps (.ret payoffs) = 0 := rfl

@[simp] theorem syntaxSteps_letExpr
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (.letExpr x e k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_sample
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)} :
    syntaxSteps (.sample x D k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_commit
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
    syntaxSteps (.commit x who R k) = syntaxSteps k + 1 := rfl

@[simp] theorem syntaxSteps_reveal
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)} :
    syntaxSteps (.reveal y who x hx k) = syntaxSteps k + 1 := rfl

/-- A program has no remaining syntax steps exactly at `ret`. -/
theorem terminal_iff_syntaxSteps_eq_zero {w : World P L} :
    terminal w ↔ syntaxSteps w.prog = 0 := by
  cases w with
  | mk Γ prog env =>
      cases prog <;> simp [terminal, syntaxSteps]

end Vegas
