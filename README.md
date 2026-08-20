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

The event-graph compilation result also retains its terminal source context,
proof-indexed source-to-field map, and original source payoff expressions.
`Machine.compile_sourcePayoffOfTerminal` proves that every terminal reachable
machine store reconstructs a typed source environment in which source and
machine payoff evaluation agree exactly, including sealed source bindings.
`Machine.compile_sourceStar` strengthens this at support level: the
reconstructed draws, commitments, and reveals form an actual written-order
`SmallStep.Star` from the program's initial source environment to that terminal
environment.

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

`Machine.AdministrativeLayer` is the first such pass. It attaches arbitrary
machine metadata and permits exact stochastic metadata-only commands. Its
generated refinement proves that semantic steps retain their abstract law,
administrative steps stutter after projection, and terminality is unchanged.
It can also lift an abstract observation by hiding the metadata; using that
lift is a modeling choice, not a proof that a real runtime keeps it secret.

`Machine.Instrumentation` is the adjacent non-stuttering pass: metadata is
updated atomically with every realized semantic successor. It covers target-
neutral completion counters, receipts, and explicit execution-order records.
The supplied `executionLog` is a proof-facing reference instance; a contract
backend can lower its records to stable action ids and completion storage one
representation decision at a time.

`Machine.Contract.Manifest` is the first emitter-facing inventory. It finitely
enumerates typed value slots, per-action completion slots, stable logical
actions, direct dependencies, logical authority, player input types, and the
original reified node code. It is lossless and adds no behavior. Physical
storage, ABI triggering of internal actions, role addresses, entropy,
commitment cryptography, timeouts, settlement, and target arithmetic are later
passes with separate obligations.

`Machine.Contract.Layout` makes the next decision independently: it maps the
logical slots to bounded natural-number keys and requires injectivity. The
canonical layout is proved collision-free and dense, with value slots followed
by completion slots. It does not yet encode a typed language value into a
target storage word.

`Machine.Contract.Request` is the logical ABI envelope: stable node id,
logical authority, and optional typed payload. `Request.accepts` executably
checks bounds, authority/payload shape, readiness, typed reads, and commit
guards, and is proved to accept exactly envelopes represented by currently
valid proof-carrying machine commands. The classical reference decoder has the
same acceptance boundary. Concrete address authentication, calldata/storage
decoding, revert behavior, gas, transaction ordering, and permission to
trigger internal actions remain explicit backend obligations.

`Machine.Contract.StorageCodec` is the target-word boundary. Combined with a
certified layout, it gives typed sparse-storage reads and writes with proved
round trips, distinct-slot noninterference, and separation between graph
values and completion bits. The included reference codec is semantic and
lossless, not a finite serialization. In particular, the current `simpleExpr`
integers denote unbounded Lean `Int`; an exact EVM-word codec therefore needs a
bounded source integer type, a proved range invariant, or chosen
modular/checked-overflow semantics. GameTheory does not decide that compiler
policy.

`Machine.Contract.RawStore.encodeSnapshot` bridges finite semantic graph state
to canonical contract storage: optional typed field words followed by explicit
completion bits. Its executable decoder is a proved left inverse, and the
resulting raw-store encoding is injective on reachable machine states. An
arbitrary decoded snapshot is not automatically reachable; preserving that
invariant is an obligation of each lowered runtime transition.

`Machine.Contract.Request.acceptsStore` connects those boundaries: it decodes
canonical raw storage and runs the executable logical request checks over the
resulting snapshot. On storage encoded from a reachable machine state, its
answer is proved identical to semantic command availability. This is still a
logical ABI over typed payloads; concrete calldata decoding and caller
authentication remain later passes.

`Machine.Contract.Request.executeConfig?` is the adjacent logical executor. It
rejects exactly the requests rejected by `acceptsConfig`; on an encoded valid
command, its next-configuration law is exactly `Machine.step` with reachability
proofs erased. This executor is a semantic reference, not an extracted random
sampler: GameTheory's canonical `FinDist` is PMF-based and noncomputable. A
backend can still lower the retained `EventDist` code to an oracle, VRF, or
other entropy mechanism, but an executable Vegas interpreter would need an
additional finite-law/sampler interface that GameTheory does not currently
provide.

`Machine.Contract.Request.executeStore?` carries the same reference law across
canonical storage: decode the snapshot, execute, and re-encode every successor.
For an encoded reachable state and valid command envelope, the resulting raw-
store law is proved exactly equal to `Machine.step` mapped through
`RawStore.encodeState`.

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

1. lower the `Machine.Contract.Manifest` code and logical slots to a backend
   expression and physical storage IR;
2. lower the executable logical request validator to a
   dependency-respecting scheduler or callable-node ABI over decoded target
   state;
3. choose storage layout, role authentication, calldata, receipts, and revert
   behavior;
4. refine semantic sealed values to commitments and reveal verification;
5. implement chance with an oracle, VRF, multi-party protocol, or another
   mechanism whose actual law and adversarial assumptions are stated;
6. add time, nonparticipation, abort/timeout, and settlement behavior;
7. lower the concrete contract IR to EVM bytecode and relate transaction traces
   back through the preceding layers.

The repository provides the first machine IR, composable operational projection,
an exact terminal source-payoff certificate, certified logical contract
inventory/layout/storage/state boundaries, and a narrow unilateral strategic
certificate. It does not yet have an EVM IR, emitter, finite EVM value codec,
cryptographic commitment refinement, exact on-chain chance implementation,
timeout/abort game semantics, or an end-to-end secure compilation theorem. The
source-star theorem is about possible terminal runs and payoff equality; it
does not equate probability laws, intermediate information histories,
schedules, or target strategy spaces. Those are VegasCore gaps, not features
supplied by GameTheory.

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
behavioral policies and mixed pure policies. The compiled information model
proves perfect recall. With finite source domains, a locally full-support policy
enumerates a finite counterfactual site cover, yielding Nash preservation and
reflection at the translated profiles without requiring the entire information
carrier to be finite.

The information state retains the latest public/private graph snapshot plus the
player's own earlier decision snapshots and actions. It deliberately does not
retain unrelated transition ordering. Menu adequacy, policy inhabitation, and
perfect recall are proved.

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
