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

The primitive machine adapter in `Vegas.EventGraph.ToMachine` is an operational
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

`Vegas.GameBridge.FOSG` gives any native `Machine.RoundView` a bounded
`GameTheory.FOSG` denotation, and exposes checked programs as
`program.frontierFOSG`. The payoff-faithful FOSG strategic object is
`program.frontierFOSGMachinePayoffHistoryKernelGame`: its outcomes are FOSG
histories and its utility is the final compiled-machine payoff.
`Vegas.GameBridge.EFG` serializes finite-state bounded round views through the
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

`Vegas.Core.ToEventGraph.SolutionConcepts` adds the matching program-facing
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
The Nash-safe mixed-pure-to-behavioral Kuhn simulation is packaged there as
`program.canonicalMixedPureToBehavioralFrontierDeviationSimulation`; the API
transports mixed-pure Nash results to behavioral Nash results through that
canonical deviation simulation.
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
the profile-level outcome-law relation in standard `GameTheory` form. Nash
transport uses the stronger
`FrontierGameSemantics.MixedPureToBehavioralDeviationSimulation`, whose
canonical construction proves that every unilateral behavioral deviation from
the canonical realization is matched by a one-player product mixed-pure
deviation. The behavioral-to-product-mixed deviation simulation is packaged as
`FrontierGameSemantics.behavioralToMixedPureNashDeviationSimulation` and
`program.behavioralToMixedPureFrontierNashDeviationSimulation`: it is the
Nash-safe ingredient for proving that if the induced product mixed-pure profile
is Nash, then the original behavioral profile is Nash.

`Vegas.Core.ToEventGraph.Transport` provides EU-preserving morphisms and
isomorphisms between completed frontier games. It also exposes the canonical
pure-to-behavioral embedding as an EU-preserving morphism from a checked
program's pure frontier game to its behavioral frontier game.

`Vegas.Core.Theorems` is the theorem index for the current architecture. It
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
| `Vegas.Examples.SolutionConcepts` | Nash, dominance, welfare, security, saddle-point, Vickrey truthfulness |
| `Vegas.Examples.EFGTranslation` | FOSG-to-EFG serialized decision-spine shape |
| `Vegas.Examples.Claims` | paper-facing checked-program claim theorems on concrete games |
| `Vegas.Examples.Refinement` | identity and encoded non-identity runtime refinement smoke tests |

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

Lower runtimes should refine primitive EventGraph/Machine execution, not the
frontier game presentation. The generic hook for this is
`Machine.AvailableStep`: an implementation step is relevant to the abstract
protocol only when it projects to a semantically available primitive graph step
or to an explicit stutter/administrative step.

Target runtimes must supply their own value codecs, message formats, concrete
commitment representation, and realization policy for abstract samples. Those
are backend proof obligations; they are not part of the language or EventGraph
IR. `Runtime.ValueCodec` records the value/wire round-trip and soundness
obligations without choosing a wire format. `Machine.StepRealizer` records the
deterministic transcript replay theorem needed when a concrete runtime realizes
an abstract PMF-valued step. `Machine.StochasticRefinement` records the
probability-preserving machine-to-machine projection, including state, batch,
observation, terminal outcome, and payoff preservation. Its support-level view
is `Machine.AvailableStepSimulation`, where administrative implementation
events may project to stutter. `Machine.RefinementKernelGame` lifts such a
machine refinement to bounded event-batch trace kernel games: profile-indexed
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
the full frontier round-view strategy history, so that law is a backend or
analysis obligation unless a later adapter supplies a canonical policy.

## Repository Map

```text
Vegas/
  Base/                    -- expression interface, values, visibility contexts
  Lang/                    -- surface language and lowering to VegasCore
  Core/                    -- VegasCore, GraphProgram/WFProgram, compiler input
  Core/ToEventGraph/       -- graph compiler, checkpoint models, round views
  Core/Theorems/           -- theorem index over the checked-program semantics
  EventGraph/              -- graph semantics, execution, frontiers, batching
  Machine/                 -- operational machine, round views, kernel-game bridge
  GameBridge/              -- FOSG/EFG presentations of native round views
  Export/                  -- finite kernel-game export tables
  Examples/                -- build-tested example modules
  Runtime/                 -- runtime-general value codec proof interfaces
docs/semantics-spine.md    -- theorem-name map for paper-facing claims

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
