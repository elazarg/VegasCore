import Mathlib.Data.List.Basic

import Vegas.LetProb.WDist
import Vegas.LetCore.Prog
import Vegas.LetCore.Env

namespace Prob

section

variable {L : Language}

attribute [instance] Language.decEqTy Language.decEqVal

variable {W : Type} [WeightModel W]

-- DESIGN NOTE: Kernels are history-dependent via `Env`;
--              strategies and sampling may depend on the current state.
-- DESIGN NOTE: No explicit model of randomness provenance (public/private/shared);
--              this is a parameter of the semantics / compilation layer.
/-- A (finite-support) stochastic kernel from environments. -/
abbrev Kernel (Γ : L.Ctx) (τ : L.Ty) :=
  L.Env Γ → WDist W (L.Val τ)

/-- Effect interface instance for `WDist W`. -/
def EffWDist : Prog.Eff (WDist W) where
  pure := WDist.pure
  bind := WDist.bind
  fail := WDist.zero

@[simp] lemma WDist_pure_weights (x : α) :
  (WDist.pure x : WDist W α).weights = [(x, 1)] := rfl

omit [WeightModel W] in
@[simp] lemma WDist_zero_weights :
  (WDist.zero : WDist W α).weights = [] := rfl

/-- Bind-commands for the probabilistic language: sampling from a kernel. -/
inductive CmdBindP (W : Type) [WeightModel W] : Prog.CmdB (L := L) where
  | sample {Γ : L.Ctx} {τ : L.Ty} (K : L.Env Γ → WDist W (L.Val τ)) : CmdBindP W Γ τ

/-- Statement-commands: hard evidence / rejection. -/
abbrev CmdStmtP : Prog.CmdS (L := L) := Prog.CmdStmtObs

/-- Probabilistic programs are `Prog` instantiated with these commands. -/
abbrev PProg : L.Ctx → L.Ty → Type :=
  Prog.Prog (CB := CmdBindP W) (CS := CmdStmtP)

/-- Pack the semantics as a `LangSem`. -/
def ProbSem : Prog.LangSem (CmdBindP W) (CmdStmtP (L := L)) (WDist W) where
  E := EffWDist
  handleBind
    | .sample K, env => K env
  handleStmt
    | .observe cond, env =>
        -- NOTE: this is *unnormalized* conditioning (hard rejection).
        if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero

@[simp] theorem ProbSem_handleBind_sample
    {Γ : L.Ctx} {τ : L.Ty}
    (K : L.Env Γ → WDist W (L.Val τ)) (env : L.Env Γ) :
    (ProbSem |>.handleBind (CmdBindP.sample (W := W) (Γ := Γ) (τ := τ) K) env) = K env := rfl

@[simp] theorem ProbSem_handleStmt_observe
    {Γ : L.Ctx}
    (cond : L.Expr Γ L.bool) (env : L.Env Γ) :
    ((ProbSem (W := W)) |>.handleStmt (Prog.CmdStmtObs.observe (Γ := Γ) cond) env) =
      (if L.toBool (L.eval cond env) then WDist.pure () else WDist.zero) := rfl

/-- Evaluator for probabilistic programs. -/
def evalP {Γ : L.Ctx} {τ : L.Ty}
    (p : Prog.Prog (CB := CmdBindP W) (CS := CmdStmtP) Γ τ)
    (env : L.Env Γ) : WDist W (L.Val τ) :=
  Prog.evalWith (ProbSem (W := W)) p env

end

end Prob

/-
This module intentionally defines only the *core* probabilistic calculus as an effect-signature
(`sample` + `observe`) and its handler into `WDist`.

A more complete standalone presentation/characterization of the language could additionally include:

* Surface-level primitives for sampling (coin flip, uniform over a finite list, etc.) and a
  compilation from those primitives to `Kernel` (rather than allowing arbitrary Lean functions).
* Convenience constructors / syntax sugar:
    - `sample K` / `observe e` as smart constructors at the `PProg` level,
    - derived forms like `if` / `assert` / `assume` / sequencing notation.
* An explicit equational/rewriting theory for programs (program congruence, β/η-style laws for
  `letDet`, and the intended algebraic laws for `sample`/`observe`), stated at the level of `evalP`
  rather than as extensional measure-theory lemmas.
* Basic structural metatheory for the core syntax (weakening/substitution lemmas for `Prog`/`Expr`,
  and "sanity" lemmas such as `observe false; p` evaluates to `WDist.zero`).
* (If desired) a small-step semantics / evaluation-context machine and a proof that it agrees
  with `evalP` (adequacy), to make operational intuitions explicit.

These are orthogonal to the extensional `toMeasure` bridge; the core here
is kept minimal so that other semantic carriers/handlers (strategic/game semantics, protocol models,
etc.) can reuse the same `Prog` syntax.

## Relationship to Borgström, Gordon, Greenberg, Margetson & Van Gael (2013)

The design of this module follows the *measure transformer semantics* of
Borgström et al., "Measure Transformer Semantics for Bayesian Machine Learning"
(LMCS 9(3:11), 2013), specialized to the discrete (finite-support) setting.

Concretely:
- `WDist` is a finitely supported sub-probability measure, playing the role of
  Fun's measure space `M^τ`.
- `evalP` is the denotation `A⟦M⟧ : M^Γ → M^τ` — a measure transformer that
  maps an input environment measure to an output value measure.
- `sample K` corresponds to Fun's `random` primitive; its semantics is
  `WDist.bind`, the discrete specialization of the `extend` combinator
  (Theorem 3.1 in Borgström et al.).
- `observe` implements *unnormalized* hard conditioning: filtering the measure
  by a boolean predicate.  This is the discrete analogue of Borgström et al.'s
  `observe` combinator (Definition 2.5), where `observe p µ A = µ(A ∩ {x | p x})`.
- Normalization (posterior recovery) is performed externally via
  `WDist.toProbabilityMeasure`, corresponding to `P[value = V | valid]`
  (Theorem 3.3).

The bridging theorems connecting `evalP` to `Measure` / `ProbabilityMeasure`
are stated in `Vegas.ProbLetLemmas` (section MeasureSemantics).  The supporting
`WDist.toMeasure` lemmas (including the key `toMeasure_bind`, which formalizes
the discrete `extend` decomposition) are in `Vegas.WDistLemmas`.
-/

