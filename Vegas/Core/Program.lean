import Vegas.Core.Scope

/-!
# Checked Vegas programs

This file separates the obligations needed for event-graph compilation from
the stronger obligations expected at the checked-game boundary.

`GraphProgram` is the direct graph-construction input: context uniqueness,
fresh bindings, and normalized samples. `WFProgram` adds reveal-completeness
and guard legality. Guard legality is used by checked game construction to
derive graph guard liveness and checkpoint progress. Reveal-completeness is a
checked source invariant: every sealed source value is eventually opened by
the source program. It is not needed for graph progress, because compiled graph
progress is about executing the graph nodes that exist.

Low-level continuation evaluators can operate on raw suffix programs, where
constructing fresh bundles for each recursive subprogram would be painful and
irrelevant.

**Strategy-level guard admissibility.** The program-level `Legal`
predicate promises that every commit site admits some guard-satisfying action
in the source-visible context. Compilation turns this into graph-level
`GuardLive`, which is the nondeadlock fact used by checkpoint models and later
strategic presentations.
-/

namespace Vegas

/-- A Vegas program paired with exactly the static obligations needed to
compile it into an event graph.

* `wctx`       — the initial context has distinct variable names.
* `fresh`      — syntactic binders are SSA-fresh.
* `normalized` — every sample site's distribution sums to `1`.
The compiler does not require reveal-completeness or guard legality. -/
structure GraphProgram (P : Type) [DecidableEq P] (L : IExpr) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  env : VEnv L Γ
  wctx : WFCtx Γ
  fresh : FreshBindings prog
  normalized : NormalizedDists prog

/-- A checked Vegas program at the game boundary.

`core` is the graph-compilable program. `legal` feeds the graph guard-liveness
and progress theorem layer. `reveals` records the source-level commitment
discipline that no committed source value is left unopened by the program. -/
structure WFProgram (P : Type) [DecidableEq P] (L : IExpr) where
  core : GraphProgram P L
  reveals : RevealComplete [] core.prog
  legal : Legal core.prog

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Every source variable introduced by a commit in a checked program is later
opened by a reveal site in that source program. -/
theorem committed_source_revealed (program : WFProgram P L) :
    ∀ x, x ∈ CommittedVars program.core.prog →
      x ∈ RevealedSources program.core.prog :=
  RevealComplete.committed_revealed program.reveals

end WFProgram

/-- A checked program with finite initial state and finite operational domains.
This is proof/evidence, not a semantic parameter of the game. -/
class FiniteDomains {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L) where
  context : FiniteVCtx g.core.Γ
  program : FiniteProgram g.core.prog

instance finiteDomains_of {P : Type} [DecidableEq P] {L : IExpr}
    (g : WFProgram P L)
    [FiniteVCtx g.core.Γ] [FiniteProgram g.core.prog] :
    FiniteDomains g where
  context := inferInstance
  program := inferInstance

end Vegas
