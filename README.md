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

### Feasible Strategies

Commit guards constrain the actions available to players. VegasCore reflects
that in the strategy types exposed by the game APIs: behavioral and pure
strategies are guard-respecting subtypes, so equilibrium statements quantify
over strategies that respect the program's guards, not over arbitrary
functions. (FOSG-side joint-action *legality* is a separate concept;
guard-respecting strategy carriers are named `Feasible*` to disambiguate.)

The main types are:

- `FeasibleProgramBehavioralStrategy g who`
- `FeasibleProgramBehavioralProfile g`
- `FeasibleProgramPureStrategy g who`
- `FeasibleProgramPureProfile g`

### Strategic-Form Game APIs

VegasCore turns a checked program into `GameTheory.KernelGame`s:

- `behavioralKernelGame g` for behavioral strategies;
- `pureKernelGame g` for pure strategies.

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

VegasCore has a machine-derived sequential FOSG denotation for checked Vegas
programs. Checked syntax elaborates to `syntaxActionGraph`, then to
`graphMachine`. `toGraphFOSG` is the direct sequential view of that graph
machine, and `toFiniteFOSG` is its syntax-horizon finite view. `toFOSG` and
`toBoundedFOSG` are aliases for the same graph-machine carrier.

The primary Vegas-facing finite sequential realization theorem is:

```lean
kuhn_mixedPureRealization_finite
```

It says that, for a finite checked Vegas program, every independent mixed
profile over feasible (guard-respecting) pure strategies has a reachable legal
PMF behavioral profile in the syntax-horizon graph-machine-derived FOSG with
the same distribution over payoff outcomes.

The preservation statement is about the outcome distribution. Expected-utility
equalities are corollaries of that distribution equality.

The underlying machine-derived finite FOSG theorems are:

```lean
toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_runDist
toFiniteFOSG_reachableMixedPure_realizedByLegalBehavioral_mappedRunDist
toFiniteFOSG_vegasMixedPure_realizedByLegalBehavioral_mappedRunDist
```

The last theorem transports product-mixed Vegas feasible pure strategies
directly into the finite graph-machine-derived FOSG reachable pure strategy
space and collapses the pure side to the native `pureKernelGame` outcome
kernel.
The local bridge behind this collapse is:

```lean
toFiniteFOSG_vegasPure_runDist_eq_pureKernelGame
```

The IR-side checked-program PMF behavioral profile type is
`SequentialBehavioralProfilePMF g hctx`, which wraps a reachable legal
behavioral profile of `toFiniteFOSG g hctx`. The syntax-recursive presentation
is named `FeasibleProgramBehavioralProfilePMF`; it is a presentation that
should be proved equivalent to the IR carrier when exposed to clients.

The cursor-world observed adapter remains as a syntax-projection layer. It is
not a second semantics; its run and outcome laws are used only through
machine-derived bridge theorems.

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

### Protocol Carrier

`Vegas/Protocol/` holds the executable protocol carrier. `ActionGraph` records
the finite dependency and visibility language; its structural execution order
is frontier resolution, where all currently ready actions form one layer. The
graph-level frontier sequence is deterministic; schedulers only appear when a
later view serializes or refines a frontier layer. The Kotlin `../vegas`
frontier design is useful design evidence, not a specification imported as
ground truth; the Lean carrier is justified by the interpretation and
projection theorems stated here.
`Machine` is the single probabilistic, observation-aware execution carrier:
one primitive step is one enabled player move or one internal protocol event.
`ActionGraph.Semantics.toMachine` is the source denotation from graph
configuration to machine. Runtime configurations use bounded histories, so the
state carrier is finite under finite action, field, and value domains.
`Vegas/Protocol/Trace.lean` defines the canonical trace semantics:
`Machine.traceDist` enumerates bounded event/state runs under a scheduling
`EventLaw`, and `Machine.outcomeKernel` is the terminal-outcome marginal.
`Vegas/Protocol/FOSG.lean` derives sequential FOSG views directly from the
carrier through `Machine.FOSGView`: FOSG worlds are `Machine.RunPrefix`
event/state prefixes, and `Machine.FOSGView.transition_map_lastState_eq_step`
projects each derived FOSG transition back to the selected `Machine.step`.
`Machine.FOSGView.legalActionLaw_bind_transition_lastState_eq_machine_stepDist`
is the corresponding one-step profile-induced law.
`Vegas/Protocol/Kuhn.lean` exposes a Kuhn realization theorem stated natively
on `Machine.FOSGView` (witness type, mixed-profile input, and outcome equality
all in machine-side observables).
Checked Vegas programs expose `graphMachine`, its direct graph-machine FOSG
view, and projection lemmas showing that available graph steps agree with the
cursor transition. The observed cursor-world adapter is retained only as a
syntax-facing projection layer and is related back to the checked transition
by direct bridge lemmas.
`Vegas/Protocol/EventLaw.lean` adapts pure, FDist behavioral, and PMF
behavioral Vegas profiles to graph-machine `LegalEventLaw`s, and
`Vegas/Protocol/Strategic.lean` packages those event laws as machine-backed
`KernelGame` constructors. The public `pureKernelGame g` /
`behavioralKernelGame g` / `pmfBehavioralKernelGame g` defined in
`Vegas/{PureStrategic,Strategic,StrategicPMF}.lean` are thin reductions to
these constructors; their outcome kernels are *definitionally* the graph
machine's outcome kernels.
Runtime distribution-preservation should use
`Machine.StochasticStepRefinement`; the weak refinement relation is only
support-level.

## Main Files

```text
Vegas/
  Core.lean                -- core language
  ExprSimple.lean          -- concrete expression language
  VegasSimple.lean         -- simple instantiation
  Config.lean              -- neutral runtime worlds and syntax-step measure
  WF.lean                  -- well-formedness, legality, normalization
  WFProgram.lean           -- checked-program bundle
  PureStrategic.lean       -- pure strategic-form game (machine-backed)
  Strategic.lean           -- FDist behavioral strategic-form game
  StrategicPMF.lean        -- PMF behavioral strategic-form game
  Equilibrium.lean         -- Nash, dominance, correlated equilibrium, welfare
  GameProperties.lean      -- approximate Nash, potential games, zero-sum, etc.
  ProtocolSemantics.lean   -- protocol-level definitions and correspondence
  Protocol.lean            -- executable protocol carrier entrypoint
  Kuhn.lean                -- Vegas-facing mixed-to-behavioral realization
  FOSG.lean                -- checked FOSG entrypoint
  Examples.lean            -- small checked examples

  Strategy/
    Pure.lean              -- guard-respecting pure strategy carriers
    Behavioral.lean        -- FDist behavioral strategy carriers
    PMF.lean               -- PMF behavioral strategy carriers
    PMFSemantics.lean      -- PMF outcome evaluator
    Conversions.lean       -- pure/behavioral/PMF lifts and bridges

  FOSG/
    Runtime.lean           -- active players and broad action availability
    Action.lean            -- program-local finite action alphabet
    Basic.lean             -- suffix/cursor checked-state machinery
    Observation.lean       -- finite observed FOSG adapter
    SmallStep.lean         -- checked PMF small-step bridge
    Cursor/                -- cursor-world step utilities (strategy
                              lookup at cursors, CheckedWorld step
                              kernel, commit-continuation helpers)

  Protocol/
    ActionGraph.lean       -- proof-carrying dependency/visibility graph
    Machine.lean           -- probabilistic observation-aware machine carrier
    Trace.lean             -- bounded event/state traces and outcome kernel
    FOSG.lean              -- machine-derived sequential FOSG views
    Checked.lean           -- checked Vegas programs as machines
    EventLaw.lean          -- strategy-profile to event-law adapters
    Strategic.lean         -- machine-backed KernelGame constructors
    StrategicCompatibility.lean -- legacy/machine kernel-game bridges
    Kuhn.lean              -- Machine-native Kuhn realization theorem
    Backend.lean           -- machine-to-machine backend refinement obligations

  Corollaries/
    Equilibrium.lean
    PureStrategic.lean
    GameProperties.lean

Explorations/
  LetCore/
  LetProb/
  LetProtocol/
  LetGames/

GameTheory/                -- submodule with the general game-theory library
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

VegasCore provides a checked-program boundary, guard-respecting (feasible)
strategy spaces, a single executable protocol carrier (`Machine`) with
PMF-valued steps and observation-aware state, machine-backed strategic-form
game APIs, protocol-level correspondence theorems, a Machine-native Kuhn
realization theorem, and a finite sequential mixed-to-behavioral realization
theorem on the graph-machine FOSG that preserves outcome distributions.
