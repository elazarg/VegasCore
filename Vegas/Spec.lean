/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Foundation.Basic
import Vegas.Core.Basic
import Vegas.Language.Basic
import Vegas.Core.WellFormed
import Vegas.EventGraph.Basic
import Vegas.Compile.Compiler
import Vegas.Frontier.Games
import Vegas.Runtime.TraceAdequacy
import Vegas.Theorems.Claims

/-!
# Trusted definition surface

This module **defines no logic.** It is the definition-side analogue of
`Vegas.Theorems.Claims`: where that file curates the main *theorems*,
this file curates the main *definitions* — the load-bearing declarations a
reader should inspect to understand why a Vegas model means what it claims.
Helper definitions, instances, and lemmas are deliberately omitted; they are
machinery, and their correctness is discharged by the proofs, not by reading.

Read the declarations below in order; each entry pins the real, fully qualified
name, so this index fails to compile if a load-bearing definition is renamed or
removed. The `#check`s are wrapped in `#guard_msgs (drop info)` so the manifest
is still build-verified but normal builds stay silent. Jump into the cited
module for the full docstring.

## 1. The expression-language interface

Every program is parameterized over an abstract expression language `L`. This
is the one open interface a concrete runtime must implement; everything else is
generic over it. (`Vegas.Foundation.Basic`)
-/

#guard_msgs (drop info) in
#check @Vegas.IExpr

/-! ## 2. Visibility and typed contexts

A bound variable carries a *visibility* (public, or sealed to one player) and a
base type. Visibility contexts (`VCtx`) are lists of such bindings; `VHasVar`
is the intrinsically-typed membership witness that keeps every term
well-scoped by construction. (`Vegas.Foundation.Basic`)
-/

#guard_msgs (drop info) in
#check @Vegas.Visibility
#guard_msgs (drop info) in
#check @Vegas.BindTy
#guard_msgs (drop info) in
#check @Vegas.VCtx
#guard_msgs (drop info) in
#check @Vegas.VHasVar

/-! ## 3. The core protocol syntax — the heart of the trusted surface

`VegasCore` is *the* load-bearing definition: the four protocol events
(`ret`, `sample`, `commit`, `reveal`) that define what a Vegas game is. If you
inspect one declaration, inspect this one. Indexed by the visibility context, so
every well-formed term is well-scoped. Strategies do not appear here. Finite
operational-domain evidence is kept out, in `Vegas.Core.FiniteDomain`.
(`Vegas.Core.Basic`)
-/

#guard_msgs (drop info) in
#check @Vegas.VegasCore

/-! ## 4. The surface language

`VegasLang` is the human-facing surface syntax (with administrative
deterministic bindings) that lowers to `VegasCore` before compilation.
(`Vegas.Language.Basic`)
-/

#guard_msgs (drop info) in
#check @Vegas.VegasLang

/-! ## 5. Checked programs

`GraphProgram` bundles a program with exactly the static obligations the
compiler needs (context uniqueness, fresh binders, normalized samples).
`WFProgram` adds the game-boundary obligations (reveal-completeness and guard
legality). These structures define what "a program we are willing to reason
about" means. (`Vegas.Core.WellFormed`)
-/

#guard_msgs (drop info) in
#check @Vegas.GraphProgram
#guard_msgs (drop info) in
#check @Vegas.WFProgram

/-! ## 6. The compilation target and its well-formedness

`Graph` is the runtime-general event graph that programs compile to; `Graph.WF`
is the well-formedness predicate the main claims establish. `compile` is the
function from a checked program to its compiled form — the bridge from source
semantics to the runtime surface. (`Vegas.EventGraph.Basic`,
`Vegas.Compile.Compiler`)
-/

#guard_msgs (drop info) in
#check @Vegas.EventGraph.Graph
#guard_msgs (drop info) in
#check @Vegas.EventGraph.Graph.WF
#guard_msgs (drop info) in
#check @Vegas.ToEventGraph.compile

/-! ## 7. Primitive machine execution

`Machine` is the runtime-general operational carrier. `PrimitiveMachine` is the
compiled EventGraph instance, and `EventBatchLaw` is the history-dependent
scheduling surface used by strategic presentations and runtime refinement.
(`Vegas.Machine.Basic`, `Vegas.Frontier.RoundView.Commits`,
`Vegas.Machine.Trace`)
-/

#guard_msgs (drop info) in
#check @Vegas.Machine
#guard_msgs (drop info) in
#check @Vegas.ToEventGraph.PrimitiveMachine
#guard_msgs (drop info) in
#check @Vegas.Machine.EventBatchLaw

/-! ## 8. Completed frontier games

The behavioral frontier game is the checked program's native strategic surface:
bounded frontier execution with the impossible cutoff branch erased.
(`Vegas.Frontier.Games`)
-/

#guard_msgs (drop info) in
#check @Vegas.WFProgram.behavioralFrontierGame

/-! ## 9. Runtime trace adequacy

`StochasticRefinement` relates implementation and specification machines.
`TraceGameSurface`, `TraceSpecEventBatchLaw`, and `RuntimeTraceAdequacy` connect
that primitive refinement to a profile-indexed checked-program game surface.
(`Vegas.Machine.Refinement`, `Vegas.Runtime.TraceAdequacy`)
-/

#guard_msgs (drop info) in
#check @Vegas.Machine.StochasticRefinement
#guard_msgs (drop info) in
#check @Vegas.WFProgram.TraceGameSurface
#guard_msgs (drop info) in
#check @Vegas.WFProgram.TraceSpecEventBatchLaw
#guard_msgs (drop info) in
#check @Vegas.WFProgram.RuntimeTraceAdequacy

/-!
The end-to-end *guarantees* about these definitions — that checked programs
compile to well-formed graphs, that outcomes agree with source payoffs, and the
rest — are stated in `Vegas.Theorems.Claims`.

## Trusted base

Auditing reduces to reading the definitions above and the claim *statements* in
`Vegas.Theorems.Claims`; the proofs are checked by Lean's kernel. The only
remaining trust is the kernel and the axioms the claims invoke. The whole
development adds nothing to classical logic: the flagship claims depend only on
`propext`, `Classical.choice`, and `Quot.sound` — no `sorry` (`sorryAx`), no
custom `axiom`, no `native_decide`.

The `#guard_msgs` pins below assert that exact axiom footprint, so the build
fails the moment it changes (e.g. a stray `sorry` would introduce `sorryAx`).
This is the trusted-base analogue of the definition manifest above.
-/

/-- info: 'Vegas.WFProgram.claim_compiles_to_wellFormed_eventGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.claim_compiles_to_wellFormed_eventGraph

/-- info: 'Vegas.WFProgram.claim_terminal_outcome_is_source_payoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.claim_terminal_outcome_is_source_payoff

/-- info: 'Vegas.WFProgram.claim_runtime_refinement_preserves_behavioral_udist' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WFProgram.claim_runtime_refinement_preserves_behavioral_udist
