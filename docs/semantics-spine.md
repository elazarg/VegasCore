# Semantics spine

This document states the semantic ownership and proof boundaries of VegasCore.

## Objects and ownership

| Layer | Canonical object | Owns |
|---|---|---|
| Source | `VegasCore P L Γ` | typed protocol syntax and visibility |
| Checked source | `WFProgram P L` | freshness, reveals, live guards |
| Machine IR | `Machine.Program P L` | typed graph, reified node/payoff code, first operational semantics |
| Payoff compilation | `Machine.compile_sourcePayoffOfTerminal` | exact terminal source/machine payoff equality |
| Source support | `Machine.compile_sourceStar` | terminal graph runs reconstruct written-order source runs |
| Strategic execution | `ExecutionProtocol P` | active players, legal joint actions, chance, terminality |
| Strategic information | `InformationModel execution` | signals, local information, local menus |
| Vegas game | `Vegas.Game P` | FOSG arena, history utility, bounded horizon, pure/behavioral/mixed-pure forms |
| Kuhn bridge | `Vegas.Game.Kuhn` | opponent-preserving behavioral/mixed deviation certificates |
| Lowering stage | `Machine.System` | one concrete operational command/state surface |
| Step projection | `Machine.Refinement` | visible abstract steps and administrative stuttering |
| Contract manifest | `Machine.Contract.Manifest` | finite lossless storage/action inventory for emitters |
| Storage layout | `Machine.Contract.Layout` | bounded collision-free physical keys for logical slots |
| Logical ABI | `Machine.Contract.Request` | executable raw-envelope and valid-command acceptance |
| Storage words | `Machine.Contract.StorageCodec` | typed target-word round trips and slot noninterference |
| Stored state | `Machine.Contract.RawStore` | executable snapshot round trip and reachable-state injectivity |
| Strategic certificate | `Runtime.DeviationAdequacy` | unilateral target-strategy back-translation |
| Same-strategy endpoint | `Runtime.Implementation` | decoded trace-law equality |

The machine IR is shared input, not a second strategic semantics. GameTheory
analysis interprets it as an informed protocol. Runtime compilation lowers its
reified code through explicit operational stages.

## Reified code and denotation

Every sample, commit guard, and payoff retains the typed embedded-language term
and a proof-indexed mapping from its variables to graph storage fields. The same
node also exposes a dependency-local denotation used by graph proofs.

The event-graph compilation result retains the terminal source context and
payoff expressions rather than discarding them after code generation. At every
terminal reachable machine store, store coherence and the compiler field map
reconstruct a complete typed source environment, including sealed bindings.
Compiled payoff evaluation is proved equal to source `evalPayoffs` in that
environment.

This separation permits a backend to translate syntax while correctness proofs
relate the translated code to the existing denotation. The abstract `IExpr`
interface does not promise that every embedded language has every backend; a
backend provides a lowering for the concrete expression language it supports.

`Machine.compile_sourceStar` additionally proves support-level adequacy. From
the semantic validity invariant of every completed graph node, it reconstructs
a written-order `SmallStep.Star`: samples remain in source support, commitments
satisfy their source guards, reveals copy the same sealed values, and the final
payoff agrees. This coarsens away the graph schedule. It does not prove equality
of quantitative run laws, intermediate observations, or strategic behavior.

## Probability

`FinDist` is the probability monad throughout graph execution, protocol
transitions, strategic play, machine refinement laws, and runtime adequacy.
`RationalLaw` is an intrinsically normalized rational source table whose
denotation uses `FinDist.ofWeights`.

There is no subprobability in the semantic spine. Checked programs terminate
within a proved bound. A concrete chance mechanism must nevertheless prove its
law; on-chain entropy is not exact merely because the source law is exact.

## Graph-to-protocol interpretation

The execution state is a reachable graph configuration. Internal sample and
reveal nodes execute as idle protocol rounds. At a strategic checkpoint, each
active player supplies a `FrontierAction` containing values for its ready commit
nodes. The joint frontier is simultaneous in the strategic semantics; its
independent writes commute.

Availability is state- and guard-dependent. Illegal values are absent from the
menu and therefore absent from the strategy and deviation space. Guard
liveness proves progress. Every realized round strictly grows the completed
downset, so `graph.nodeCount` is a uniform `BoundedHorizon`.

Public/private snapshots prove menu adequacy: indistinguishable states have the
same activity and legal options. The information state retains the latest
snapshot and exactly the player's own earlier decision record, not unrelated
transition ordering. This representation has proved perfect recall. Menus at
unreachable information values use an idle fallback so total policy carriers
remain inhabited.

## Why MAID is not the denotation

Vegas decision sites have state-dependent guarded menus and may combine several
ready commitments in one simultaneous joint decision. A fixed-domain MAID node
does not natively express that surface. Totalizing invalid choices would change
the strategy and deviation spaces.

A MAID can be an export for a fragment with a proved strategic correspondence;
it is not the canonical denotation. The FOSG is exact because it packages the
accepted execution and information objects directly.

## Gradual runtime interpretation

A lowering pass should introduce one implementation concern at a time.
`Machine.Refinement` proves only the functional stochastic projection:
concrete commands decode to an abstract command or to an abstract stutter, and
the projected laws agree exactly. These certificates compose.

`Machine.AdministrativeLayer` realizes the first reusable pass in this chain.
It adds a metadata component and metadata-only stochastic commands, while
deriving exact step projection and terminality preservation. An optional lifted
observation hides the metadata by construction. That lifted model applies only
when the intended runtime exposure really omits the metadata.

`Machine.Instrumentation` handles metadata changed atomically by semantic
steps, rather than by target-only commands. Its exact projection covers such
concerns as completion flags, sequence counters, and receipts. The reference
`executionLog` records realized step order; exposing that log would change the
observation model and therefore requires an explicit companion theorem.

`Machine.Contract.Manifest` then exposes the lossless logical inventory an
emitter needs: typed value slots, completion slots, stable actions, direct
dependencies, authority, player input types, and node code. It intentionally
stops before choosing physical storage, ABI scheduling, participant addresses,
entropy, cryptography, timeout behavior, settlement, or bounded target
arithmetic.

`Machine.Contract.Layout` isolates the physical-key decision. Its canonical
instance is dense and injective, placing typed value slots before action
completion slots. A target value codec and its arithmetic semantics are still
required before these keys describe executable EVM storage.

`Machine.Contract.Request` erases a valid dependent command to a stable node
id, logical authority, and optional typed value. `Request.accepts` computes
node bounds, authority/payload shape, readiness, typed-read availability, and
commit guards. Its adequacy theorem says that it accepts exactly the envelopes
represented by currently valid machine commands, matching the classical
reference decoder. Address authentication, concrete calldata/storage decoding,
revert traces, gas, and internal-action triggering remain unmodeled.

`Machine.Contract.StorageCodec` isolates target-word encoding. Typed reads and
writes over any certified layout have same-slot round trips; writes to distinct
value or completion slots are proved noninterfering. Its reference codec is a
lossless semantic model rather than a serializable backend format. Since
`simpleExpr` interprets integers as unbounded Lean `Int`, VegasCore cannot
provide an exact 256-bit EVM codec without adding bounded integers, proving a
range restriction, or selecting modular/checked-overflow behavior. That is a
source/compiler design obligation, not functionality inherited from
GameTheory.

`Machine.Contract.RawStore.encodeSnapshot` stores the finite graph snapshot in
the canonical layout, leaving absent graph values uninitialized and writing
every completion bit explicitly. `decodeSnapshot` is executable and a proved
left inverse; `encodeState` is injective on reachable machine states. Decoding
arbitrary storage establishes structural well-typedness, not semantic
reachability, which remains a transition invariant for a concrete runtime.

That law alone is insufficient when a pass changes what a player or scheduler
can do or observe. Required companion results depend on the pass:

- added deterministic bookkeeping: stuttering projection may suffice;
- added randomness/noise: independence and observation laws are required;
- chosen ordering or concurrency: linearizability and schedule-information
  results are required;
- added target actions: a strategy/context back-translation is required;
- cryptographic hiding: a computational or idealized noninterference theorem is
  required;
- timeouts and nonparticipation: liveness and utility semantics are required.

`Runtime.DeviationAdequacy` is one exact, deliberately limited game-level
certificate. Honest compiled profiles preserve decoded laws, and every
unilateral target replacement has a law-equivalent source replacement. This
proves Nash equivalence at compiled profiles. It says nothing about
coalitions, arbitrary linked contexts, or scheduler hyperproperties.

`Runtime.Implementation` applies only when no new strategy carrier remains. Its
profile-uniform decoded-law equality is then a special case of deviation
adequacy, not a substitute for earlier pass proofs.

## Blockchain obligations

A concrete chain path still needs certified layers for expression lowering,
target-level scheduling/ABI lowering, a finite target codec, authentication,
commitment/reveal, randomness, time and failure, settlement, and bytecode. The
core source language currently lacks participation failure, timeout, and
monetary-transfer semantics, so those behaviors cannot yet be introduced with
an exact source game theorem.

The existing readability-fence theorem constrains the order of readable output
values. It explicitly does not prove indistinguishability of complete observed
traces, whose event occurrences remain public. It is useful groundwork for a
strong-linearizability proof, not that final proof.

## Upstream boundary

GameTheory supplies the strategic objects and exact transformations used by
Vegas. In particular, its `InformationModel` has opponent-preserving
unilateral Kuhn laws. `Vegas.Game.Kuhn` packages those laws as deviation
adequacy in both directions. Compiled programs discharge perfect recall.
Finite source domains also construct a full-support finite counterfactual site
cover, so the unilateral certificates apply without assuming a globally finite
information-history carrier.

GameTheory does not supply a general secure-compilation or runtime
hyperproperty framework; that boundary is domain-specific and remains in
VegasCore. Its MAID surface also uses fixed decision domains, so exporting a
guarded Vegas game to MAID requires a fragment restriction or a proved
strategic encoding.
