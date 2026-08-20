# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial
information. A checked source program has one semantic compilation, with two
consumers: GameTheory analysis and gradual lowering toward concrete runtimes.

## Architecture

```text
                              ┌─→ ExecutionProtocol + InformationModel
VegasCore source              │        └─→ FOSG / strategic forms / analysis
      │                       │
      └─→ Machine.Program ────┤
          typed EventGraph    │
          + reified node code └─→ System₀ → System₁ → … → backend artifact
                                      small certified lowering passes
```

`Machine.Program` is the first backend-neutral machine IR. It contains:

- typed initial and event storage fields;
- dependency-derived sample, guarded commit, and reveal nodes;
- reified typed expression/distribution code with every variable mapped to a
  graph field;
- exact `FinDist` denotations for execution and analysis;
- terminal payoff code;
- graph well-formedness and guard-liveness proofs.

Retaining code is essential. Evaluator closures alone can define semantics but
cannot be traversed by a Solidity, EVM, native, SMT, or circuit backend.

The GameTheory view is derived from this machine program. It is not the final
runtime model, and concrete implementation details are not added to the game in
one jump.

## Gradual lowering

`Machine.System` represents one operational stage. Its commands are indexed by
the state from which they are valid. `Machine.Refinement abstract concrete`
projects concrete states and decodes each concrete command as either:

- one abstract command with exactly the projected stochastic transition; or
- an administrative command whose projection stutters.

Refinements compose. This supports small passes such as adding bookkeeping,
choosing an order, introducing an encoding, or splitting one logical operation
across transactions.

This step projection is intentionally not called game preservation. A pass
that adds observations, scheduling choices, timing, or adversarial behavior
must also prove the relevant information or strategic theorem.
`Runtime.DeviationAdequacy` is one narrow such criterion: target strategies are
back-translated one unilateral deviation at a time, which is sufficient to
preserve and reflect Nash at compiled profiles. It is not a general
secure-compilation theorem.

`Runtime.Implementation` is only the terminal special case where the runtime
has exactly the source strategy carrier and decoded outcome-law equality holds
for every profile. It derives deviation adequacy automatically. It must not be
used to skip intermediate scheduler or information proofs.

## Path to a blockchain backend

An EVM-class compiler can grow as a sequence like this:

1. lower `Machine.Program` node code to a backend expression and storage IR;
2. add an explicit dependency-respecting scheduler or callable-node ABI;
3. choose storage layout, role authentication, calldata, receipts, and revert
   behavior;
4. refine semantic sealed values to commitments and reveal verification;
5. implement chance with an oracle, VRF, multi-party protocol, or another
   mechanism whose actual law and adversarial assumptions are stated;
6. add time, nonparticipation, abort/timeout, and settlement behavior;
7. lower the concrete contract IR to EVM bytecode and relate transaction traces
   back through the preceding layers.

The repository provides the first machine IR, composable operational projection,
and a narrow unilateral strategic certificate. It does not yet have an EVM IR,
emitter, cryptographic commitment refinement, exact on-chain chance
implementation, timeout/abort game semantics, or an end-to-end secure
compilation theorem. Those are VegasCore gaps, not features supplied by
GameTheory.

## Game semantics

The canonical strategic denotation is GameTheory's
`ExecutionProtocol + InformationModel`, packaged as a FOSG. It is not a MAID.
State-dependent guards determine native legal menus, simultaneous ready
commitments form one joint frontier action, chance is a `FinDist` transition,
and policies depend only on a player's information state.

`Vegas.Game` adds terminal utility and a proved finite horizon. Its pure,
behavioral, and mixed-pure forms are direct GameTheory views. Vegas does not
define competing strategy, deviation, equilibrium, or history types.

GameTheory's opponent-preserving Kuhn laws are packaged in
`Vegas.Game.Kuhn` as deviation-adequacy certificates in both directions between
behavioral policies and mixed pure policies. They require perfect recall.

The current information state is the latest public/private graph snapshot.
Menu adequacy is proved. Perfect recall of the compiled model is not yet
proved, so Kuhn results may be used only when their stated recall hypotheses
have separately been established.

## Source language

The typed core has four protocol constructors:

- `ret`: terminate with public-state payoff expressions;
- `sample`: draw a public value from an exact finite probability law;
- `commit`: let a player choose a sealed value satisfying a guard over that
  player's view;
- `reveal`: publish a previously sealed value.

Visibility is carried in the context type. A commit guard cannot read data its
owner cannot observe, and terminal payoff expressions cannot mention sealed
state. `WFProgram` proves fresh bindings, reveal completeness, and live guards.

The language does not yet express deposits, transfers, participant addresses,
timeouts, aborts, or failure to reveal. A blockchain backend cannot silently
invent those behaviors and still claim exact game preservation.

## Probability

There is one semantic probability type: GameTheory's `FinDist`.
`RationalLaw` is exact source syntax for a normalized finite table of
nonnegative rational masses. Its denotation combines repeated entries and
works over arbitrary value carriers.

Subprobability is unnecessary for the checked language because every compiled
game has a uniform finite horizon. Divergence would require a separate language
feature and semantic design.

Exact source probabilities do create a backend obligation. Common blockchain
entropy constructions can be manipulable or biased, and modulo reduction is
not in general an exact implementation of a rational law. Any approximation or
trust assumption must be represented explicitly rather than hidden by code
generation.

## GameTheory boundary

GameTheory supplies the canonical probability, utility, deviation,
equilibrium, informed-protocol, FOSG, behavioral/mixed, unilateral Kuhn,
assessment, backward, and FOSG-to-EFG machinery used here. The unilateral Kuhn
results live on the underlying `InformationModel`; Vegas uses them directly
rather than waiting for an additional FOSG convenience wrapper.

Secure compilation, scheduler hyperproperties, strong linearizability, and
adversarial runtime refinement are runtime-specific and have no general
GameTheory abstraction. Also, GameTheory's fixed-domain MAID surface cannot
directly represent Vegas's guarded state-dependent menus without a strategic
encoding theorem.

VegasCore owns the latter boundary and must add only the certificate justified
by each lowering pass.

## Build

```text
lake build
```

The public roots are `Vegas`, `Vegas.Core`, `Vegas.EventGraph`,
`Vegas.Language`, `Vegas.Compile`, `Vegas.Machine`, `Vegas.Game`,
`Vegas.Game.Kuhn`, and `Vegas.Runtime`.
