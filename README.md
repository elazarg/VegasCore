# StratLet

A Lean 4 formalization providing formal semantics for games expressed as programs.

The repository now has one mainline implementation and one clearly secondary
exploration tree:

- `Vegas/` is the mainline language and backend stack.
- `Explorations/` preserves older design explorations, but is not the primary
  project surface.
- `GameTheory/` is the root-level submodule providing the broader game-theory
  library used by the MAID backend.

## Overview

Games are expressed as programs where:
- Players make **strategic choices** from available actions, restricted by **Views** (observable projections of the environment)
- Outcomes may be **probabilistic** (sampling from finite-support weighted distributions)
- **Strategy profiles** determine how players choose actions at each decision point
- **Conditioning** uses hard rejection (`observe`) on boolean predicates

The mainline `Vegas/` tree is organized around:

1. **Expr** -- the generic expression-language boundary and a concrete instantiation
2. **Protocol** -- Vegas syntax, static side conditions, and examples
3. **BigStep / TraceSemantics / ActionGraph** -- the main semantic presentations and graph IR
4. **Strategic / MAID** -- the strategic semantics and the main backend stack
5. **GameTheory** -- the external submodule providing MAID and general game-theory infrastructure

## Project Structure

```text
Vegas/
  Expr/
    Interface.lean
    Concrete.lean
  Protocol/
    Syntax.lean
    WF.lean
    Examples.lean
  BigStep.lean
  TraceSemantics.lean
  ActionGraph.lean
  Strategic.lean
  MAID/
    Backend.lean
    Compile.lean
    Fold.lean
    Correctness.lean

Explorations/
  LetCore/
  LetProb/
  LetProtocol/
  LetGames/

GameTheory/
```

## Key Concepts

### Strategy Profiles
A `Profile` maps player decisions to probability distributions over actions. Each decision site has a `View` that restricts what the player can observe. Fixing a profile converts a strategic program into a pure probabilistic program.

### Views (Partial Information)
A `View Gamma` projects the full environment `Env Gamma` to a visible sub-environment `Env Delta`. Strategies at a yield site can only depend on the projected environment, enforcing information restrictions structurally.

### Weighted Distributions
`FDist alpha` is the main finitely-supported weighted distribution used in the
mainline semantics. It is implemented with `Finsupp` over `ℚ≥0`.

### Strategic Semantics
`Vegas/Strategic.lean` packages normalized Vegas programs as `KernelGame`s so
general game-theory results can be imported from `GameTheory`.

## Building

Requires Lean 4 and Mathlib.

```bash
git submodule update --init --recursive
lake build
```

## Status

This is research work exploring formal foundations for expressing games as
programs. The mainline repository is now MAID-first. Direct Vegas -> EFG support
is no longer part of the mainline layout; if EFG is needed, the intended route
is through the `GameTheory` MAID -> EFG bridge.
