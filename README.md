# VegasCore

VegasCore is a Lean 4 formalization of the core semantics of
[VEGAS](https://github.com/elazarg/VEGAS): a programming language for writing
finite games with probabilistic computation, partial information, and strategic
choices.

As a Vegas user, the main object you build is a checked program:

```lean
WFProgram P L
```

A `WFProgram` packages a Vegas program, its initial environment, and the facts
needed to treat it as a game:

- variables are fresh, reveals are complete, and commit sites respect player
  views;
- all probabilistic samples are normalized;
- every commit guard admits at least one legal action.

Once you have a `WFProgram`, VegasCore gives you strategic and sequential
game-theoretic views of the same program.

## What You Get

### Legal Strategies

Commit guards constrain the actions available to players. VegasCore reflects
that in the strategy types exposed by the game APIs: behavioral and pure
strategies are guard-legal subtypes, so equilibrium statements quantify over
strategies that are legal for the program, not over arbitrary functions.

The main types are:

- `LegalProgramBehavioralStrategy g who`
- `LegalProgramBehavioralProfile g`
- `LegalProgramPureStrategy g who`
- `LegalProgramPureProfile g`

### Strategic-Form Game APIs

VegasCore turns a checked program into `GameTheory.KernelGame`s:

- `toKernelGame g` for behavioral strategies;
- `toStrategicKernelGame g` for pure strategies.

The wrappers in `Vegas.Equilibrium`, `Vegas.PureStrategic`, and
`Vegas.GameProperties` expose the usual game-theoretic vocabulary directly on
Vegas programs:

- expected utility: `eu`, `mixedEu`, `correlatedEu`;
- Nash and strict Nash equilibria: `IsNash`, `IsStrictNash`;
- pure Nash variants: `IsPureNash`, `IsPureStrictNash`;
- best response and dominance: `IsBestResponse`, `IsDominant`,
  `WeaklyDominates`, `StrictlyDominates`;
- correlated and coarse correlated equilibrium;
- Pareto efficiency and social welfare;
- approximate Nash, potential games, zero-sum/constant-sum games, security
  levels, rationalizability, and price-of-anarchy style definitions.

The corollary files transport standard `GameTheory` results through these
Vegas-facing wrappers.

### Sequential-Game Results

VegasCore also has a canonical sequential denotation for checked Vegas
programs. The public Vegas-facing result is the finite mixed-to-behavioral
realization theorem:

```lean
kuhn_mixedPure_realizedByBehavioralPMF_finite
```

It says that, for a finite checked Vegas program, every independent mixed
profile over legal pure strategies has a legal PMF behavioral profile with the
same distribution over payoff outcomes.

The preservation statement is about the outcome distribution. Expected-utility
equalities are corollaries of that distribution equality.

The proof goes through the FOSG layer from `GameTheory`, but ordinary users of
the Vegas Kuhn theorem receive a native Vegas behavioral witness and do not
need to work with FOSG internals.

### Protocol-Level Statements

`Vegas.ProtocolSemantics` states the same strategic concepts directly in terms
of the program's outcome semantics and proves that they agree with the
`KernelGame` wrappers:

- `ProtocolNash` agrees with `IsNash`;
- `ProtocolBestResponse` agrees with `IsBestResponse`;
- `ProtocolDominant` agrees with `IsDominant`;
- `ProtocolStrictNash` agrees with `IsStrictNash`.

Use these when you want a statement phrased directly over the Vegas protocol
semantics rather than over the strategic-form wrapper.

## Main Files

```text
Vegas/
  Core.lean              -- core language
  ExprSimple.lean        -- concrete expression language
  VegasSimple.lean       -- simple instantiation
  Config.lean            -- neutral runtime worlds and syntax-step measure
  WF.lean                -- well-formedness, legality, normalization
  WFProgram.lean         -- checked-program bundle
  BigStep.lean           -- canonical outcome semantics
  TraceSemantics.lean    -- trace semantics and reachability
  TraceCorollaries.lean  -- trace/outcome corollaries
  SmallStep.lean         -- raw labelled small-step entrypoint
  Strategic.lean         -- behavioral strategic view
  StrategicPMF.lean      -- PMF behavioral strategic view
  PureStrategic.lean     -- pure strategic view
  Equilibrium.lean       -- Nash, dominance, correlated equilibrium, welfare
  GameProperties.lean    -- approximate Nash, potential games, zero-sum, etc.
  ProtocolSemantics.lean -- protocol-level definitions and correspondence
  Kuhn.lean              -- Vegas-facing mixed-to-behavioral realization
  FOSG.lean              -- sequential denotation entrypoint
  Examples.lean          -- small checked examples

  SmallStep/
    Defs.lean
    Agreement.lean
    Properties.lean

  FOSG/
    Runtime.lean         -- active players and broad action availability
    Action.lean          -- program-local finite action alphabet
    Basic.lean           -- suffix/cursor checked-state machinery
    Observation.lean     -- observed FOSG target
    SmallStep.lean       -- checked PMF small-step bridge
    Observed/

  Corollaries/
    Equilibrium.lean
    PureStrategic.lean
    GameProperties.lean

Explorations/
  LetCore/
  LetProb/
  LetProtocol/
  LetGames/

GameTheory/              -- submodule with the general game-theory library
```

`Explorations/` preserves older design experiments. The supported sequential
game view is `Vegas/FOSG.lean`.

## Building

Requires Lean 4, Mathlib, and the checked-out `GameTheory` submodule.

```bash
git submodule update --init --recursive
lake build Vegas
```

## Status

VegasCore provides a checked-program boundary, legal strategic strategy
spaces, canonical outcome semantics, trace and small-step semantics,
strategic-form game APIs, protocol-level correspondence theorems, and a finite
sequential mixed-to-behavioral realization theorem that preserves outcome
distributions.
