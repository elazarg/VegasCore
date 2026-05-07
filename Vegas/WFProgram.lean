import Vegas.Scope

/-!
# Well-formed Vegas programs

This file defines `WFProgram`, the bundle that packages a Vegas program with
the static obligations needed to produce a game-theoretic object from it:
`WFCtx` (distinct initial bindings), `WF` (fresh bindings,
reveal-completeness, view-scoping), `NormalizedDists` (sample distributions sum
to 1), and `Legal` (every commit site has a feasible action). User-facing game
APIs downstream — `pmfBehavioralKernelGame`, `pureKernelGame`, `IsNash`,
`IsPureNash`, `IsεNash`,
and the equilibrium-family predicates — consume `WFProgram` rather than a raw
`VegasCore` plus separate side conditions. This is the API boundary where raw,
unchecked syntax becomes a "real" game.

The low-level PMF continuation evaluator used by the observed/FOSG bridge
still operates on raw suffix programs, where constructing fresh bundles for
each recursive subprogram would be painful and irrelevant.

**Strategy-level guard admissibility.** The program-level `Legal`
predicate only promises that every commit site *admits* some guard-
satisfying action. The semantic game APIs close the gap by using reachable
legal strategies of the event-graph machine FOSG: illegal moves are not available in
the carrier quantified over by equilibrium predicates and downstream
corollaries.
-/

namespace Vegas

/-- A Vegas program paired with its initial environment and the static
well-formedness obligations needed to interpret it as a game.

* `wctx`       — the initial context has distinct variable names.
* `wf`         — the program is structurally well-formed: fresh bindings,
  reveal-completeness, and view-scoping (see `WF` in `Vegas.Scope`).
* `normalized` — every sample site's distribution sums to `1`.
* `legal`      — every commit site has at least one action satisfying its
  guard (the game never deadlocks).

`wf` already includes `RevealComplete []`, so the bundle does not carry a
separate `reveals` field. -/
structure WFProgram (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  wctx : WFCtx Γ
  wf : WF prog
  normalized : NormalizedDists prog
  legal : Legal prog

/-- A checked program with finite initial state and finite operational domains.
This is proof/evidence, not a semantic parameter of the game. -/
class FiniteDomains {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L) where
  context : FiniteVCtx g.Γ
  program : FiniteProgram g.prog

instance finiteDomains_of {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L) [FiniteVCtx g.Γ] [FiniteProgram g.prog] :
    FiniteDomains g where
  context := inferInstance
  program := inferInstance

end Vegas
