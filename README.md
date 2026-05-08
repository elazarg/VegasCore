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
WFProgram -> EventGraph -> Machine -> Strategic kernel games
```

The source syntax is a convenient way to define the game. The central semantic
object is the event graph; the machine is its operational interpretation.
Vegas-native strategic semantics live under `Vegas/Strategic/`. FOSG and EFG
are bridges under `Vegas/GameBridge/`, not the ownership point of the semantics.

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

`Vegas.Strategic.Equilibrium`, `Vegas.Strategic.Pure`, and
`Vegas.Strategic.Properties` expose
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

These are stated in Vegas kernel-game terms. The finite FOSG view supplies the
information-state strategy spaces and outcome kernels behind those games.

## Semantic Spine

The internal Vegas pipeline uses source-owned `ToX` modules:

- `Lang/ToCore.lean`: surface-to-core lowering.
- `Core/ToEventGraph.lean`: elaborates checked `VegasCore` programs to the
  canonical `EventGraph`; the implementation is split under
  `Core/ToEventGraph/` into nodes, fields, obligations, and construction.
- `EventGraph/ToMachine.lean`: interprets event-graph configurations as the
  operational `Machine`.

Other layers consume that spine:

- `Strategic/`: Vegas-native strategy carriers, kernel games, equilibrium
  vocabulary, dominance, transport, and Kuhn-facing public names.
- `GameBridge/`: FOSG/EFG bridges and FOSG-backed realization machinery.
- `Backend/`: operational/runtime refinement and backend blocked-trace games.

## Repository Map

```text
Vegas/
  Base/                    -- shared weights, expression interface, contexts
  Lang/                    -- concrete/surface language layers
  Core/                    -- VegasCore, WFProgram, checking, ToEventGraph
  EventGraph/              -- central graph object, frontier facts, ToMachine
  Machine/                 -- generic operational carrier and traces
  Strategic/               -- native Vegas strategic semantics
  GameBridge/              -- FOSG/EFG bridges
  Backend/                 -- implementation refinement
  Theorems/                -- project-facing theorem names
  Corollaries/             -- transported GameTheory results
  Examples/                -- checked Prisoners, Pennies, Sexes, Monty Hall

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
kernel-game names. FOSG views supply histories, observations, reachable-legal
strategies, and finite-horizon outcome kernels.
