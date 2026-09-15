# Typed protocol interface

## Decision

This is a proposed interface, not an implemented model or preservation theorem.
The Lean-shaped declarations are schematic dependency sketches, not checked APIs.

Generate one graph-relative, dependently typed protocol which executes
`G.nodeOrder` with a public program counter. Transport remains unrestricted:
off-order, malformed, replayed, or adversarial calls may be submitted and
observed, but they do not change application state. Only a successful action or
an authorized resolution for the current operation advances the counter.

This conservative compiler policy matches the canonical order already used by
the source-to-declared-read graph theorem and avoids another induction over
partial graph frontiers. Parallel admission can later be proved as an
optimization/refinement. It is not part of the minimum interface.
Private values may affect guards; source chance reads only public values.
Neither changes the operation sequence: compilation has already fixed `nodeOrder`.

The proposed interface replaces `SealedShape G ty` and `SealedFragment G ty`. It has no
global value type, `noSamples`, or universally accepting `commitGuard` premise,
and introduces neither a second source semantics nor a whole-run simulation
certificate.

## Public code and private setup

`Graph.initialFields` currently contains values. Those values must not be copied
into public generated code. Compilation erases them to a layout; deployment
supplies them separately:

```lean
structure InitialSlot (Player : Type) (L : IExpr) where
  ty : L.Ty
  owner : Option Player

def InitialLayout (G : Graph Player L) : List (InitialSlot Player L) :=
  G.initialFields.map fun field => ⟨field.ty, field.owner⟩

structure InitialInput (layout : List (InitialSlot Player L)) where
  value : (slot : Fin layout.length) -> L.Val (layout.get slot).ty

structure InitialRealization (G : Graph Player L) where
  input : InitialInput (InitialLayout G)
  realizes : forall slot,
    input.value slot = cast (by simp [InitialLayout])
      (G.initialFields.get slot).value
```

These declarations are proof-facing specifications, not serialized code:
indexing by `G` may mention the source graph and its initial constants. The
executable public artifact is a separate erasure containing the layout,
operation code, and public metadata, but neither `G.initialFields[*].value` nor
`InitialRealization.input`. Initialization consumes setup once:

```lean
def initialize (spec : TypedProtocolSpec G)
    (input : InitialInput spec.initialLayout) : ProtocolState G
```

The compiler emits a proof-facing realization for the checked source run. A
real deployment obtains secrets through an explicitly named authenticated
private-input capability and proves correspondence without publishing
owner-private values. Ordinary EVM storage is observable and does not supply
that capability. Embedding the witness or private constants in bytecode or
public storage is forbidden. A
raw initializer may refuse while decoding or authenticating setup; that occurs
before a corresponding source execution starts, not as a source default. Once
`InitialRealization` holds, initialization is total and later failure cannot
replace those already-realized source inputs.

## Values, raw traffic, and operations

All Lean-shaped declarations below are schematic, unimplemented interface
sketches. They specify dependency and separation requirements, not promised
exact signatures; names such as `ProtocolState`, projections, and correspondence
relations stand for interfaces the implementation must define.

```lean
abbrev NodeValue (G : Graph Player L) :=
  (node : Fin G.nodeCount) × L.Val (G.nodeRow node).ty

structure TypedCodec (L : IExpr) (Raw : Type) where
  encode : (ty : L.Ty) -> L.Val ty -> Raw
  decode? : (ty : L.Ty) -> Raw -> Option (L.Val ty)
  decode_encode : forall ty value, decode? ty (encode ty value) = some value

structure CandidateId (Player : Type) where owner : Player; nonce : Nat
structure MessageId where senderNonce : Nat

inductive RevealOrigin (G : Graph Player L) (ty : L.Ty) where
  | initial (field : Fin G.initialFields.length)
      (type_eq : (G.initialFields.get field).ty = ty)
      (sealed : (G.initialFields.get field).owner.isSome)
  | committed (producer : Fin G.nodeCount) (owner : Player)
      (guard : EventGuard L)
      (producerRow : (G.nodeRow producer).sem = .commit owner guard)
      (type_eq : (G.nodeRow producer).ty = ty)

def RevealOrigin.field : RevealOrigin G ty -> Nat
  | .initial field .. => field.val
  | .committed producer .. => G.nodeTarget producer

inductive Operation (G : Graph Player L) :
    (node : Fin G.nodeCount) -> Type where
  | chance (dist : EventDist L)
      (row : (G.nodeRow node).sem = .sample dist) : Operation G node
  | commit (owner : Player) (guard : EventGuard L)
      (row : (G.nodeRow node).sem = .commit owner guard) : Operation G node
  | reveal (origin : RevealOrigin G (G.nodeRow node).ty)
      (row : (G.nodeRow node).sem = .reveal origin.field) :
      Operation G node

structure TypedProtocolSpec (G : Graph Player L) where
  graphWF : G.WF
  initialLayout : List (InitialSlot Player L)
  initialLayout_eq : initialLayout = InitialLayout G
  operation : (node : Fin G.nodeCount) -> Operation G node
```

`TypedProtocolSpec G` is schematic and proof-facing. Reveal-origin construction
must inspect `G.field? source` and retain its type and sealed-owner witness; it
must not classify an arbitrary numeric field as revealable. A separate real
`PublicArtifact` representation erases `G` and its initial values and is
connected to the specification by a representation refinement. Equality proofs
erase. `Graph.WF` supplies reveal origins and dependencies: an initial origin publishes an already-realized input,
while a committed origin goes through opening validation. At the current
`nodeOrder[pc]`, prerequisites are already satisfied. Raw
payloads never inhabit `NodeValue`: wrong-type traffic simply fails decoding.
Source-site, candidate, and message identities remain distinct, so several
candidates may be prepared for one site while acceptance binds at most one.

## Attempt and default APIs

```lean
inductive RejectReason where
  | offOrder | replay | malformed | wrongType | unauthorized
  | wrongCandidate | invalidOpening | guardUnavailable

inductive AttemptResult (State : Type) where
  | rejected (reason : RejectReason) (same : State)
  | applied (next : State)

inductive ResolutionCause where
  | deadline | authenticatedInvalidOpening | authenticatedGuardRejection

structure SourceAlternative (G : Graph Player L)
    (node : Fin G.nodeCount) where
  next : ProtocolState G
  source : SourceContinuationAt G node
  legal : SourceAlternativeLegalAt G node source
  corresponds : ProtocolStateCorresponds G next source
  preservesPrior : PriorKnowledgeAndResultsPreserved G node next

structure Resolvable (G : Graph Player L) (node : Fin G.nodeCount) where
  causeAllowed : ResolutionCause -> Prop
  alternative : forall cause, causeAllowed cause ->
    ProtocolState G -> SourceAlternative G node

structure DefaultResolver (G : Graph Player L) where
  resolvable? : (node : Fin G.nodeCount) -> Option (Resolvable G node)
```

Every `rejected` result is a retryable application stutter: it preserves the
counter, bindings, store, chance cells, and source continuation. Rejection may
remain visible in transport history, but an outsider's malformed packet cannot
make another player quit.

Only an authenticated protocol transition or deadline authority may invoke a
present resolver with a proved allowed cause. Resolution installs a *legal,
specified source alternative* and
advances to its certified continuation. There is no raw `failed reason` terminal
state and no global `nullValue`. Chance, successful initial publication, and
every other node without a certified alternative have `resolvable? = none`; the
backend cannot invent quitting behavior. An authenticated bad opening or guard rejection
may either remain retryable or invoke a named resolution transition; generated
code must choose explicitly. Candidate acceptance does not imply openability:
the existing fresh/openable/accepted-but-unopenable meanings are retained.

## Reveal validation

This section applies to `.committed` reveal origins. An `.initial` origin has no
candidate, guard, or player-controlled publisher: the protocol automatically
reads the already-realized typed sealed slot, publicly publishes it, and
advances. Supporting player withholding here would require an explicit source
contract extension; it must not be invented by the backend.

```lean
structure GuardInputs (G : Graph Player L) (producer : Fin G.nodeCount)
    (guard : EventGuard L) where
  reads : ReadEnv L guard.choiceReads
  sourceDecisionInputs : AgreesWithSourceDecisionInputs G producer reads

inductive VerifiedOpening (G : Graph Player L)
    (producer : Fin G.nodeCount) where
  | value (value : L.Val (G.nodeRow producer).ty)

def verifyOpening? (codec : TypedCodec L Raw)
    (candidate : AcceptedCandidate Player Raw)
    (raw : Raw) : Option (VerifiedOpening G producer)

def validateGuard (inputs : GuardInputs G producer guard)
    (opening : VerifiedOpening G producer) : Bool
```

The order is authorization/selected-candidate check, commitment verification,
typed decoding, then guard evaluation. This is deferred checking of
*commit-time legality*: the source admits the action at the commit choice, while
the target may discover illegality only on opening. A guard-invalid raw
candidate therefore never corresponds to a legal source commit choice. Its
backtranslation or authorized default must use a separately certified legal
source alternative at that commit checkpoint, not reinterpret rejection as an
ordinary source reveal failure. A successful block writes precisely the
producer's typed value and advances. Ordinary failures stutter; only an
explicit authorized resolution selects the source alternative.

Guard legality uses the source decision inputs, not a later default-modified
store. `GuardInputs` is proof-facing unless the runtime really possesses those
values. A realistic host must provide either public availability of all guard
dependencies or a sound authenticated proof/ideal verifier for private inputs.
Merely storing a captured private context in the model is not a realization. If
neither capability exists, that backend cannot host the program, although the
source and typed protocol remain valid.

## Chance and observations

Chance is internal and uses the retained conditional distribution:

```lean
structure ChanceService (G : Graph Player L) where
  sampleOnce : forall node dist,
    (G.nodeRow node).sem = .sample dist ->
    ReadEnv L dist.reads -> ChanceCell G node ->
    FinDist (ChanceCell G node × L.Val (G.nodeRow node).ty)
  first_law : ... = dist.eval reads
  replay_law : Cached cell value ->
    sampleOnce ... cell = FinDist.pure (cell, value)

structure ProtocolObservation (G : Graph Player L) (who : Player) where
  pc : Nat
  publicStore : PublicProjection G
  privateStore : PrivateProjection G who
  acceptedSites : PublicAcceptedBindings G
  publishedOpenings : PublicOpenings G
  resolutions : PublicResolutions G
  transport : ObservableTransportHistory who
```

Dependent reads are the actual earlier graph values; no independence assumption
is introduced. For source-compiled graphs, `VegasCore.sample` reads only public
state and produces a public value. The protocol-controlled chance service must
sample once and publicly publish that value as the same atomic logical
operation; lower service steps may refine it, but neither player nor scheduler
selects, withholds, or republishes the result. The compiler must not invent a
private sampler or strategic publisher. Visibility is observer-relative: the
environment sees a submission when it enters the pending pool; a player sees
its own sent payloads and those delivered to its inbox, potentially before
inclusion. These local observations are not assumed common knowledge.
`publishedOpenings` records payloads visible to that observer and distinguishes
pending claims from authenticated accepted openings. Ledger inclusion has its
separate public observation. Private candidate preparation and unreleased
chance cells remain absent from other players' observations.
Rejected traffic remains observable, including any cleartext it contains, but
does not install an accepted binding, authenticated opening, source result,
or resolution.

## Proof boundary and module impact

The implementation first proves one uniform current-operation block law:

```lean
typedBlockLaw :
  currentOperation spec state = operation ->
  HostBlock spec state calls =
    -- visible rejected stutters, followed by exactly one of:
    successStep operation ∨ chanceStep operation ∨ authorizedDefault operation
```

Advancing cases respectively match the graph typed step, retained dependent
kernel, or resolver's certified source alternative. That operational law is
necessary but does not establish arbitrary-deviation simulation. The compiler
must separately prove observation/history correspondence and a causal joint-law
backtranslation: each unilateral native policy, jointly with the adaptive
environment and unchanged opponents, induces a legal graph/source comparison
without unavailable information or factoring dependent choices. A third,
separate incentive edge applies the program's source-derived continuation
inequality to authorized resolutions. Only these results together yield the
existing simulation/utility certificates and then Nash. No interface field
may assume whole-run simulation, policy extraction, utility domination, or Nash.

The public counter removes the current backend's ability to *apply*
prerequisite-ready nodes out of numeric order. It does not restrict the
environment: off-order submission, delivery, pending observation, replay, and
attempted inclusion remain available. Serial blocking changes timing and
information—an earlier withheld operation must be authoritatively resolved
before later application—so the observation and causal joint-law results are
new obligations, not corollaries obtained by restricting the existing runtime.

Reuse `EventGraph.Basic`, `Execution`, `GuardValidation`, `Compile.Compiler` and
`BuildResult`, `Interaction.CommitmentCandidates`, the message/pending/replay/
clock runner, and existing `FinDist`, dependent-kernel, and source-to-graph
results. Replace homogeneous sealed rules/state/decoding, `SealedShape`,
`SealedFragment`, `SealedCompilation`, and `nullValue`. Port the host through one
adapter; do not create a second runner or duplicate source/native inductions.

## Capabilities, not conveniences

Runtime-inherent assumptions are authenticated authority, immutable candidate
meaning and site binding, sound opening verification, a real public/private
guard-verification capability, unbiased sample-once entropy, private setup for
secret inputs, idempotent effects and stable identities, and the
ledger/finality/liveness and settlement expressiveness used by the theorem.
Cryptographic implementations state their computational error; gas and fees
enter utilities when relevant.

The following are conveniences, not admission restrictions: one value type,
total guards, public-only inputs, independent chance, no initial fields, one
candidate per site, guaranteed openability, fixed-size encoding, parallel
frontier execution, one deadline, or one transaction ordering. Concrete
bytecode bounds belong to the later representation refinement.

## Discriminating acceptance test

Compile one nonconstant game with an initial `.sealed Alice Bool` named
`secret`, a public positive
`Nat bound`, an Alice `Nat bid` guarded at reveal by `bid <= bound` and a
predicate depending on `secret`, a Bob
`Bool` commitment/reveal, and a later distribution whose weights depend on both
accepted values. A later source `reveal` explicitly publishes the initial-field
origin for `secret`, so the private setup and initial-origin reveal paths are not
vacuous. That publication is automatically serviced, not a new player choice.
Its source settlement supplies the legal commit-checkpoint alternatives used
for deadline or authenticated invalid-opening resolution and proves the
continuation inequality needed for Nash.

The test must deploy public code without either initial value and realize them
through separate setup; submit off-order/replayed/wrong-type traffic and observe
only retryable stutters; prepare multiple Alice candidates, accept one, and
reveal a typed bid above `bound`, showing that the original decision inputs,
including `secret` through a real verifier capability, are used and only
authorized resolution installs the source fallback; execute the explicit
initial-origin publication; then, in a
successful run, reveal heterogeneous `Nat`/`Bool` values and trigger chance
twice, obtaining one cached draw with exactly the source conditional law.
Finally it establishes nonconstant source outcome/settlement correspondence and
the resulting target Nash theorem under the stated service assumptions.

The test fails if malformed traffic itself quits, guard rejection writes the
candidate, defaults leave continuation uninterpreted, chance resamples, private
initial constants occur in public code, or equilibrium relies on an invented
runtime-checkpoint inequality.
