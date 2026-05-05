# VegasCore

VegasCore is a Lean 4 formalization of finite games written as programs. A
Vegas program combines deterministic computation, finite-support sampling,
strategic commitments, explicit reveals of private values, and payoff
expressions.

The main object a user builds is:

```lean
WFProgram P L
```

A `WFProgram` packages a Vegas program, its initial environment, and the facts
needed to treat it as a finite game: freshness, scoped visibility, complete
reveals, normalized samples, and nonempty legal commit guards.

## Public API

The supported semantic path is:

```text
WFProgram -> ProtocolGraph -> Machine -> FOSG view -> KernelGame
```

The source syntax is a convenient way to define the game. The strategic
semantics are owned by the graph-native machine and its finite FOSG view.

### Strategy And Game Carriers

For a checked finite program `g : WFProgram P L`:

```lean
pureStrategyAt g who
behavioralStrategyPMFAt g who
pureKernelGame g
pmfBehavioralKernelGame g
```

The strategy carriers are reachable-legal information-state strategies of the
finite syntax-graph FOSG. Illegal deviations are excluded by the carrier type.

### Game-Theoretic Vocabulary

`Vegas.Equilibrium`, `Vegas.PureStrategic`, and `Vegas.GameProperties` expose
standard game-theoretic predicates directly on Vegas kernel games:

- expected utility: `eu`, `mixedEu`, `correlatedEu`;
- Nash variants: `IsNash`, `IsStrictNash`, `IsPureNash`;
- best response and dominance: `IsBestResponse`, `IsDominant`,
  `WeaklyDominates`, `StrictlyDominates`;
- correlated and coarse correlated equilibrium;
- Pareto efficiency, social welfare, approximate Nash, potential games,
  zero-sum and constant-sum games, rationalizability, and price-of-anarchy
  style definitions.

The corollary files transport generic `GameTheory` results through these
Vegas-facing wrappers.

### Kuhn Realization

The primary Vegas-facing finite mixed-to-behavioral theorem is:

```lean
kuhn_finite
```

It states that every independent mixed profile over the pure strategy carrier
of `pureKernelGameAt g` has a PMF behavioral profile of
`pmfBehavioralKernelGameAt g` with the same distribution over payoff outcomes.

The protocol-facing proposition is:

```lean
KuhnPMF g
kuhnPMF_finite g
```

These are stated in Vegas kernel-game terms. FOSG appears in the proof layer,
not as a separate user-facing game model.

## Protocol Core

`Vegas/Protocol/` contains the executable protocol semantics:

- `Graph.lean`: proof-carrying dependency and visibility graph.
- `Machine.lean`: probabilistic observation-aware machine carrier.
- `GraphMachine.lean`: interpretation of graph configurations as machine
  states.
- `SyntaxGraph.lean`: compiler from checked Vegas syntax to `ProtocolGraph`,
  plus finiteness and legal-observability facts.
- `Trace.lean`: bounded event/state traces and machine outcome kernels.
- `FOSG.lean`: sequential FOSG views derived from machines.
- `Strategic.lean`: finite syntax-graph kernel-game constructors.
- `Kuhn.lean`: machine-native and Vegas-facing Kuhn realization theorems.
- `Backend.lean`: machine-to-machine backend refinement obligations.

## Repository Map

```text
Vegas/
  Core.lean                -- core language
  ExprSimple.lean          -- concrete expression language
  VegasSimple.lean         -- simple instantiation
  Config.lean              -- runtime worlds and syntax-step measure
  WF.lean                  -- well-formedness, legality, normalization
  WFProgram.lean           -- checked-program bundle
  Finite.lean              -- finite-domain package
  PureStrategic.lean       -- pure syntax-graph strategic-form game
  StrategicPMF.lean        -- PMF behavioral strategic-form game
  Equilibrium.lean         -- Nash, dominance, correlated equilibrium, welfare
  GameProperties.lean      -- approximate Nash, potential games, zero-sum, etc.
  ProtocolSemantics.lean   -- protocol-level Kuhn property
  Protocol.lean            -- protocol entrypoint
  Kuhn.lean                -- Vegas-facing mixed-to-behavioral realization
  Examples.lean            -- small checked examples

  Protocol/
    Graph.lean
    Machine.lean
    GraphMachine.lean
    SyntaxGraph.lean
    Trace.lean
    FOSG.lean
    Strategic.lean
    Kuhn.lean
    Backend.lean

  Corollaries/
    Equilibrium.lean
    PureStrategic.lean
    GameProperties.lean

GameTheory/                -- submodule with the general game-theory library
```

## Building

Requires Lean 4, Mathlib, and the checked-out `GameTheory` submodule.

```bash
git submodule update --init --recursive
lake build Vegas
```

## Status

VegasCore has a single graph-native protocol denotation for checked programs.
Public strategic games and the finite Kuhn theorem are stated over Vegas
kernel-game names. The FOSG construction supplies the finite sequential-game
structure used to prove those results.
