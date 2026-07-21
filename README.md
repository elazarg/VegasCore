# VegasCore

VegasCore is a Lean 4 project for describing games with partial information as
programs and compiling those programs to explicit protocol/event structures.
The abstractions are runtime-general. Blockchain runtimes are an intended
backend family, but the language and event graph do not encode
blockchain-specific concepts.

## Main Objects

`GraphProgram P L` is the direct event-graph compiler input. It contains a
`VegasCore` program, an initial visibility context/environment, and the static
facts needed for graph construction: distinct context names, fresh binders, and
normalized samples.

`WFProgram P L` is the checked-game boundary. It wraps a `GraphProgram` and adds
reveal-completeness and guard-legality obligations. Those obligations are used
above raw graph construction: guard legality gives graph guard liveness and
checkpoint progress, while reveal-completeness records the source commitment
discipline that committed source values are eventually opened.

`ToEventGraph.CompiledProgram P L` is the compiler output: an
`EventGraph.Graph P L`, a graph well-formedness proof, and terminal payoff
projections.

## Semantic Path

```text
GraphProgram
  -> ToEventGraph.CompiledProgram
  -> EventGraph primitive execution / primitive Machine adapter
```

For checkpoint models, the checked-program layer can take an explicit
checkpoint presentation, or use the primitive downset presentation derived from
source guard legality:

```text
WFProgram + EventGraph.CheckpointPresentation
  -> ToEventGraph.CheckpointModel

WFProgram
  -> ToEventGraph.CheckpointModel
```

A checkpoint presentation chooses which reachable graph checkpoints count as a
single observation step and carries the progress obligation for those
checkpoints. For the primitive downset policy, compilation proves source
`Legal` guards become graph `GuardLive`, and graph well-formedness plus
`GuardLive` gives checkpoint progress. This policy is an operational
schedule-abstraction layer; strategic frontier semantics are built separately.

The primitive machine adapter in `Vegas.Machine.Adapter.ToMachine` is an operational
protocol adapter. It is useful for execution and refinement reasoning, but it
is not the final strategic game presentation.

For bounded strategic analysis, finite checked programs can be compiled through
the native frontier round view:

```text
WFProgram + FiniteDomains
  -> canonical frontier checkpoint semantics
  -> ToEventGraph.CompletedFrontierPureKernelGame
  -> ToEventGraph.CompletedFrontierBehavioralKernelGame
```

The frontier action carrier is graph-local: a player action assigns values only
at graph nodes, and each assigned value is typed by that node's declared output
type. Finite action alphabets are derived from the source finite-domain proof;
the compiled graph remains the semantic object.

Default compiled frontier games use the graph node count as their completion
bound. Certified frontier histories with one supported round per graph node
are terminal, because every supported round strictly advances the completed
node downset. The canonical frontier constructors expose concrete `KernelGame`s
over the compiled outcome type directly. Internally, the bounded construction
passes through an option-valued kernel with an unreachable cutoff branch, and
the completed frontier API erases that branch using support-totality proofs.

The current behavioral frontier game uses semantic PMF-valued behavioral
strategies. That is distinct from a finite enumerated behavioral-strategy
carrier. The canonical package exposes finite pure-strategy carriers and their
mixed extension as the finite analysis surface; Kuhn realization transports
between mixed-pure and behavioral outcome kernels.

`ToEventGraph.canonicalFrontierGameSemantics` is the program-facing package
for finite checked programs. It exposes the completed pure game, completed
behavioral game, Kuhn bridge, and source-payoff adequacy theorems, including
option-kernel equality with the completed run distribution pushed through the
source payoff projection, while keeping the event graph itself source-free.
The same surface is available by dot notation on `WFProgram` values:
`program.pureFrontierGame`, `program.behavioralFrontierGame`,
`program.mixedPureFrontierGame`, and the terminal-public mixed game expose the
default user-facing game objects directly.
History and public-observation game forms are exposed the same way, for
example `program.pureFrontierHistoryGameForm` and
`program.behavioralFrontierPublicHistoryGameForm`.

`Vegas.Presentation.FOSG` gives any native `Machine.RoundView` a bounded
`GameTheory.FOSG` denotation, and exposes checked programs as
`program.frontierFOSG`. The payoff-faithful FOSG strategic object is
`program.frontierFOSGMachinePayoffHistoryKernelGame`: its outcomes are FOSG
histories and its utility is the final compiled-machine payoff.
`Vegas.Presentation.EFG` serializes finite-state bounded round views through the
shared FOSG-to-EFG bridge. Checked finite programs expose the serialized
frontier EFG as `program.frontierPlainEFG`, the payoff-facing EFG kernel game
as `program.frontierPlainEFGMachinePayoffKernelGame`, and the FOSG/EFG utility
distribution bridge as
`program.frontierPlainEFGMachinePayoffKernelGame_udist_eq_fosg`. The finite
state presentation is derived from canonical reachable graph snapshots, so the
serialized game surface is independent of source syntax and raw store
representations.

`Vegas.Export.KernelGame` packages finite-strategy kernel games as in-Lean
strategy tables for solver or serializer adapters. Checked finite programs
expose pure frontier and pure terminal-public frontier export tables through
`Export.pureFrontierGame` and `Export.pureTerminalPublicFrontierGame`.
`Vegas.Export.EFG` packages the checked serialized EFG together with its source
FOSG presentation, payoff-facing kernel game, and certified profile-translation
adequacy law as `Export.frontierPlainEFG`; behavioral EFG strategies are not
enumerated as a finite table. The export API also exposes the payoff-parity
theorems tying both the raw serialized EFG and that payoff kernel back to the
native behavioral frontier game and the FOSG presentation.
`Vegas.Export.FOSG` packages the checked bounded FOSG denotation, completion
horizon, boundedness proof, and payoff-faithful history kernel as
`Export.frontierFOSG`, with utility-distribution and Kuhn-compatibility
theorems available from the export namespace.

`Vegas.Frontier.SolutionConcepts` adds the matching program-facing
solution vocabulary for these games, including ε-Nash, best response,
dominance, dominance solvability, security/maximin guarantees,
two-player saddle-point vocabulary, Pareto efficiency, individual rationality,
rationalizability, potential-game predicates, social welfare, zero-sum,
constant-sum, and team properties for the completed frontier games. Finite
enumerative concepts such as finite security levels, welfare optimum,
best/worst Nash welfare, and price-of-anarchy/stability helpers are exposed on
the finite pure completed-frontier game. Preference-parametric handles such as
`PureFrontierNashFor`, `PureFrontierBestResponseFor`,
`PureFrontierCorrelatedEqFor`, `PureFrontierCoarseCorrelatedEqFor`,
`BehavioralFrontierNashFor`, `BehavioralFrontierDominantFor`,
`BehavioralFrontierCorrelatedEqFor`, and
`BehavioralFrontierCoarseCorrelatedEqFor` delegate to the underlying
`KernelGame` `*For` predicates; the theorem index records that the ordinary
frontier predicates are their expected-utility specializations.
The strategy/deviation-level Kuhn package is exposed as
`program.frontierKuhnStrategicEquivalence`.  It records the canonical
mixed-pure-to-behavioral and behavioral-to-mixed-pure profile translations,
outcome-kernel preservation in both directions, and one-player deviation
matching across the two presentations.  The Nash-safe mixed-pure-to-behavioral
simulation remains available as
`program.canonicalMixedPureToBehavioralFrontierDeviationSimulation`; Nash
transport is a downstream use of the deviation-level Kuhn facts.
It also exposes `GameForm`s whose outcomes are completed frontier histories,
public checkpoint-observation histories, and terminal public graph
observations, so protocol observations can be analyzed without immediately
choosing a payoff utility. The completed-history forms also have
`KernelGame` versions whose utility is the compiled payoff projection at the
history endpoint; these games preserve the joint utility distribution of the
payoff-outcome games. The terminal-public observation form is finite whenever
the checked program has finite value domains. The finite existence theorems
therefore live on the pure terminal-public game and its mixed extension:
mixed Nash, correlated equilibrium, and coarse-correlated equilibrium are
available without an additional payoff-bound hypothesis. The behavioral
terminal-public game is still exposed for stating predicates and comparing
outcome kernels, but its PMF-valued behavioral strategy carrier is not a
finite enumeration surface.

The Kuhn-facing API pairs the canonical pure and behavioral completed frontier
games as `ToEventGraph.CompletedFrontierKuhnGames`. The proved bridge
`ToEventGraph.MixedPureToBehavioralOutcomeKernelRealizable.canonical` turns the generic
Kuhn adapter theorem into an equality of concrete completed-game outcome
kernels for the mixed-pure-to-behavioral direction. The companion
product-mixed bridge
`CompletedFrontierKuhnGames.behavioralToProductMixedOutcomeKernel` and the
program-facing `FrontierGameSemantics.behavioralToMixedPureOutcomeKernel`
convert native behavioral profiles to independent mixed pure-strategy profiles
with the same completed-game outcome kernel. The weaker joint-distribution
bridge
`CompletedFrontierKuhnGames.behavioralToCorrelatedPureOutcomeKernel`
exposes the behavioral-to-correlated-pure direction for native behavioral
profiles of the completed behavioral game, and
`ToEventGraph.behavioralToCorrelatedPureOutcomeKernel`
packages that direction for canonical compiled frontier games. Finite adapter
information states are derived from the finite graph action/observation
surface. Local support for the mixed-to-behavioral direction and the
no-repeated-nontrivial-info-state condition for behavioral-to-product-mixed
and behavioral-to-correlated-pure are proved generically for native round
views. `CompletedFrontierKuhnGames.completeOutcomeKuhn` and
`program.frontierCompleteOutcomeKuhn` package the two product-mixed/behavioral
directions together as the generic `GameTheory.Theorems.KuhnCompleteViaOutcome`
schema.

Outcome-kernel equality gives expected-utility equality for the transported
profiles. The mixed-pure-to-behavioral Kuhn theorem is also packaged as a
`KernelGame.ProfileRealization` by
`FrontierGameSemantics.mixedPureToBehavioralProfileRealization`, which records
the profile-level outcome-law relation in standard `GameTheory` form.  The
stronger non-equilibrium API is `FrontierGameSemantics.KuhnStrategicEquivalence`
and the program-facing `program.frontierKuhnStrategicEquivalence`; individual
deviation facts include
`program.mixedPureFrontier_behavioralDeviation_to_mixedPure`,
`program.mixedPureFrontier_mixedDeviation_to_behavioral`, and
`program.behavioralFrontier_deviation_to_mixedPure`.  Nash transport uses these
deviation facts through the existing deviation-simulation wrappers, including
`FrontierGameSemantics.behavioralToMixedPureNashDeviationSimulation` and
`program.behavioralToMixedPureFrontierNashDeviationSimulation`.

`Vegas.Frontier.Transport` provides EU-preserving morphisms and
isomorphisms between completed frontier games. It also exposes the canonical
pure-to-behavioral embedding as an EU-preserving morphism from a checked
program's pure frontier game to its behavioral frontier game.

`Vegas.Theorems` is the theorem index for the current architecture. It
groups the intended public theorem surface by topic: compiled graph validity,
execution/frontier behavior, progress, visibility/observations, outcome adequacy,
strategy locality, nullable lowering, Kuhn realization, FOSG adequacy, runtime
refinement, and solution-concept vocabulary.

`import Vegas` also exposes the core kernel-game solution concepts and mixed
extension tools from the `GameTheory` library. The canonical pure frontier
game has finite, nonempty strategy carriers and is the intended finite mixed
analysis surface. The behavioral frontier game is semantic and PMF-valued; it
is connected to the finite pure surface by the Kuhn realization theorems rather
than by enumerating behavioral strategies. Mixed Nash existence is available
directly for the finite terminal-public observation game. The payoff-vector
game also exposes a bounded-utility variant; its concrete outcome carrier is
an integer payoff map, so finiteness is a semantic payoff fact rather than a
typeclass consequence on that surface.

`import Vegas.Examples` exposes checked example programs and end-to-end
frontier game smoke tests.

The examples are also imported by `VegasTests`, so the default build checks the
main semantic paths:

| Module | What It Exercises |
| --- | --- |
| `Vegas.Examples.DependencySemantics` | compiler dependency footprints, commit choice footprints, raw graph validation |
| `Vegas.Examples.MatchingPennies` | simultaneous hidden commits, finite frontier games, zero-sum payoff table |
| `Vegas.Examples.MontyHall` | staged information flow, relevant reveal timing, FOSG/EFG payoff adequacy |
| `Vegas.Examples.SolutionConcepts` | Nash, mixed Nash, dominance, security, potential-game bridges, Vickrey truthfulness |
| `Vegas.Examples.EFGTranslation` | FOSG-to-EFG serialized decision-spine shape |
| `Vegas.Examples.Claims` | paper-facing checked-program claim theorems on concrete games |
| `Vegas.Examples.Refinement` | a compiled constant-payoff trace law, audited runtime adequacy, and encoded non-identity refinement checks |

## EventGraph Model

An event graph is the canonical protocol dependency object produced by
compilation. Nodes are protocol events, fields are typed values, and node reads
are the scheduling/information dependency footprint.

Primitive execution is schedule-agnostic. Available events are exposed with
evidence, and schedules/checkpoint policies are external semantic choices. The
public observation records completed nodes and public available field values;
player observations record the ready commit frontier and the information
visible at commit sites. The ready frontier is part of the observation so
empty-read commit menus are observable as menus, not inferred from guard data.

The default frontier round semantics closes currently-ready internal graph
work before offering strategic commit choices, executes the selected commit
frontier, and then closes newly-ready internal work before emitting the next
checkpoint observation.

The primitive downset checkpoint policy allows exactly strict completed-node
downset advances that are realizable by some primitive event batch. The ordered
batch witness is proof data, not public or player observation history.

Surface-language `let` bindings are lowered away before core graph
compilation. Core graph nodes represent material protocol activity rather than
administrative aliases.

## Runtime Refinement Boundary

Lower runtimes refine primitive EventGraph/Machine execution rather than the
frontier game presentation. `Machine.StochasticRefinement` records the
probability-preserving machine-to-machine projection, including state, event
batches, observations, terminal outcomes, and payoffs. `Machine.AvailableStep`
is the support-level vocabulary used by runtime constructions that expose
administrative or message-in-flight transitions.

Target runtimes must supply their own value codecs, message formats, concrete
commitment representation, and realization policy for abstract samples. Those
are backend proof obligations; they are not part of the language or EventGraph
IR. `Runtime.ValueCodec` records the encoding required to place typed values on
a backend wire without choosing a wire format. `Machine.RefinementKernelGame`
lifts a stochastic machine refinement to bounded event-batch trace kernel
games: profile-indexed
specification laws and compatible implementation laws induce a game morphism,
and bounded payoff hypotheses give the EU-preserving morphism needed for Nash
pullback.
`Machine.audited` is a generic non-identity wrapper used as a refinement smoke
surface: it adds administrative audit ticks and an audit counter, then proves
those implementation events erase back to the original machine. The checked
runtime bridge exposes audited adequacy constructors for behavioral, pure, and
product mixed-pure frontier strategy surfaces.
The checked-program runtime bridge deliberately requires a trace-adequate
specification event-batch law. Machine traces do not by themselves reconstruct
the full frontier round-view strategy history, so a general law remains a
backend or analysis obligation. `Vegas.Examples.Refinement` constructs the law
for a concrete compiled terminal game and carries it through the audited
runtime, establishing the base case without an assumed law.

## Repository Map

The directory layout follows the dependency pipeline: each directory is a single
layer, and imports flow strictly downward (`Frontier` imports `Compile`, never the
reverse; nothing under `EventGraph` imports `Machine`).

```text
Vegas/
  Foundation/              -- expression interface, values, visibility contexts
  Core/                    -- the VegasCore source language and checked-program boundary
  Language/                -- surface language and lowering to Core
  EventGraph/              -- source-free graph IR: execution, frontiers, batching
  Machine/                 -- operational machine, round views, kernel-game bridge
  Machine/Adapter/         -- EventGraph <-> Machine adapters
  Machine/Kuhn/            -- Kuhn-theorem adapter for native round views
  Compile/                 -- checked-program -> EventGraph compiler + checkpoint model
  Frontier/                -- canonical strategic semantics over compiled graphs
  Presentation/            -- FOSG/EFG presentations of native round views
  Export/                  -- finite kernel-game export tables
  Runtime/                 -- runtime-general codec and trace-adequacy proof interfaces
  Theorems/                -- theorem index over the checked-program semantics
  Spec.lean                -- research-spine definition and theorem index
  Examples/                -- build-tested example modules
docs/semantics-spine.md    -- theorem-name map for paper-facing claims

Vegas.lean                 -- build-all root: every module in dependency-layer order
VegasTests.lean            -- regression target imported by the default build
GameTheory/                -- submodule with the general game-theory library
```

## Building

Requires Lean 4, Mathlib, and the checked-out `GameTheory` submodule.

```bash
git submodule update --init --recursive
lake build
```

`lake build` builds both the main `Vegas` library and `VegasTests`, which checks
the event-graph compiler regression examples. Use `lake build Vegas` only when
you intentionally want to skip regression modules.
