/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Basic

/-!
# Vegas core syntax

Generic Vegas protocol syntax and finite operational-domain evidence.
-/

namespace Vegas

/-! ## Vegas program syntax -/

/-- Generic Vegas-style protocol syntax over an expression language.

A `VegasCore Player L Γ` is a typed program in context `Γ`. The inductive
is indexed by the visibility context, so every well-formed term is
well-scoped by construction. Strategies do not appear here — the `commit`
constructor holds only its guard, and the choice kernel is supplied
by local strategy carriers in the strategic and machine semantics. The same
program can therefore be evaluated against many strategy profiles.

## Classification

The constructors are **protocol events** that model observable activity in a
multi-party computation:

* `ret` — the protocol terminates and players collect payoffs.
* `sample` — nature draws from a public distribution; every player sees
  the outcome.
* `commit` — a player chooses a value subject to a guard and seals it
  from the others.
* `reveal` — a previously sealed value is disclosed to everyone. This is
  the only way to make sealed data observable; the timing of the reveal
  is under program control, distinguishing open play from sealed commitment.

Administrative deterministic bindings are surface syntax, not core protocol
events. They are erased by the `VegasLang → VegasCore` lowering layer before
event-graph compilation. -/
inductive VegasCore (Player : Type) [DecidableEq Player] (L : IExpr) :
    VCtx Player L → Type where
  /-- Terminate with per-player payoffs. Each payoff expression is over the
  public-only erased context — payoffs cannot depend on sealed state. -/
  | ret {Γ} (payoffs : List (Player × L.Expr (erasePubVCtx Γ) L.int)) :
      VegasCore Player L Γ
  /-- Sample from `D'` and bind the result as a fresh public variable.
  `D'` reads only public state (nature has no private knowledge); the
  sampled value is observable to all. -/
  | sample {Γ} (x : VarId) {b : L.Ty}
      (D' : L.DistExpr (erasePubVCtx Γ) b)
      (k : VegasCore Player L ((x, .pub b) :: Γ)) :
      VegasCore Player L Γ
  /-- Player `who` commits to a value of type `b`, subject to guard `R`.
  The guard is typed over the proposed action together with `who`'s current
  view. The result is bound as `sealed who b`, visible only to `who`. -/
  | commit {Γ} (x : VarId) (who : Player) {b : L.Ty}
      (R : L.Expr ((x, b) :: eraseVCtx (viewVCtx who Γ)) L.bool)
      (k : VegasCore Player L ((x, .sealed who b) :: Γ)) :
      VegasCore Player L Γ
  /-- Disclose a previously sealed variable `x` as a fresh public alias `y`.
  The membership witness `hx` must show `x` is currently sealed, owned by
  `who`. -/
  | reveal {Γ} (y : VarId) (who : Player) (x : VarId) {b : L.Ty}
      (hx : VHasVar Γ x (.sealed who b))
      (k : VegasCore Player L ((y, .pub b) :: Γ)) :
      VegasCore Player L Γ

/-! Finite operational-domain evidence for this syntax lives in
`Vegas.Core.FiniteDomain`; it is kept separate so the load-bearing program
syntax above can be audited on its own. -/

end Vegas
