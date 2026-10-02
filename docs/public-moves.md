# Public moves: a source `yield` versus a fused commit–reveal

## Status

This is a design note; nothing in it is checked in Lean. It compares two ways
of sending a public move as one runtime message instead of a commitment
followed by an opening, and recommends the source-level construct.

## The problem

The source language has no public move. A player who chooses a value that
everyone should see writes

```text
commit x by A; reveal x
```

and the compiled runtime sends two envelopes: a commitment and, once the
reveal event is ready, an opening. Nothing happens between the two source
instructions. The reveal's `DecisionView` is the commit's view plus A's own
commit action, so no new information reaches A between the decisions. By the
criterion in [action boundaries](action-coalescing.md), the two decisions can
be coalesced into one. The question is where to perform the coalescing without
weakening any pinned result in `Paper.lean`.

## Option 1: fuse `commit x; reveal x` in the compiler

Keep the source unchanged, recognize an adjacent pair, and let one envelope
complete both the binding event and the resolve event. The pinned statements
can survive, but only under three conditions.

### 1. The fused envelope must be sent at the reveal's barrier

In concurrent mode, `barrierOrder` (`Vegas/EventGraph/Barriers.lean`) lets A's
binding for `x` complete before an earlier, other-owner binding `y` by B. That
is harmless while `x` is sealed. A cleartext `x` at that point can reach B
through passive observation, and B may still submit a fresh candidate for `y`
([message runtime §5](network-and-compilation.md)). Then `y` depends on `x`,
which the source forbids.

Against compiled opponents the honest law survives, because they ignore
leaked traffic. The sequential-equilibrium result does not: on the
equilibrium path B has seen `x`, and B's source strategy need not be
sequentially rational there. The runtime would also author an opening before
its predecessors complete, contradicting the
[dependency-authorized submission contract](dependency-authorized-submission.md).

The fix is to give the fused binding every earlier event as a predecessor,
which is what the reveal already has. This adds no latency, since the reveal
waited for the same barrier. Extra edges keep `BarrierOrdered`
(`Vegas/EventGraph/BarrierInformation.lean`), which is only a lower bound on
the order, so the generic graph theorems still apply.

### 2. Withholding must still bind a hidden value

The honest and deviation laws, and the sequential-equilibrium joint law, are
stated over the full typed terminal source state (`terminalState`,
`protocolReadout`). That state includes the commitment cell. The source action
`commit (success v); reveal false` publishes failure but leaves `success v` in
the cell. A fused withholding envelope that carries no private meaning cannot
reproduce this state. Only the Nash equivalences, which are stated over the
public outcome, would survive unchanged.

The fused envelope therefore has to be the existing commitment payload, a
handle with an ideal private meaning, plus a disclosure flag that attaches the
raw opening in the clear. With that encoding `native_commitment_binding` still
holds as stated.

### 3. Both graph fields must be written and the guard checks run

An event graph has one output per event, and the terminal readout needs both
the binding and the publication. The least disruptive encoding keeps the two
graph events and lets one inclusion complete the bind and then, immediately,
the resolve. Under condition 1 the resolve is ready at that point, and its
checks run as usual. Every event-graph theorem stays untouched.

### Cost

The work lands in the runtime-to-graph refinement: every lemma assuming that
one inclusion causes at most one graph step, service turns for a resolve that
is already complete, deadlines and `ServiceFeasible`, the honest and deviation
chains under `Vegas/Pending`, the audit's permitted-envelope predicate, and
the reveal-service sequential-equilibrium development, which models the
owner's opening as its own invocation.

### Why a default hidden value does not help

Condition 2 looks like an artifact: the hidden value in the withholding case
has no public consequence. Writing a default into the cell instead does not
remove the difficulty. The source still leaves `success v` there, so a runtime
that stores a default no longer has the source terminal-state law for honest
profiles that commit and then withhold. The statements would have to forget
these cells, or the source semantics would have to special-case a commitment
by its position. It would also rewrite a private binding after a failed
disclosure, which [immutable private bindings](source-design-rationale.md#immutable-private-bindings)
rules out.

The hidden value is required only because a public move is encoded as a
private move followed by a disclosure. Removing the encoding removes the value.

## Option 2: a source `yield` (recommended)

Add a source instruction by which the owner publishes a value directly:

```text
yield x by A
```

Its action is `PublicationResult (L.Val τ)`: a value, or failure for declining
or silence. It extends the context with `(x, .publication τ)` directly. No
commitment cell exists, so there is nothing hidden to preserve.

| Fused `commit; reveal` | `yield` |
|---|---|
| Needs extra edges so the envelope is sent at the reveal's barrier | Automatic: a public event already waits for every earlier event, and every later event waits for it |
| Withholding must carry a hidden meaning | No hidden state: failure is the published result |
| One inclusion completes two graph events | One event, one output, one packet with no handle or candidate catalogue; one inclusion still causes at most one graph step |

### Cost

- A new `SourceProgram` constructor adds a case to every induction over it.
  About 56 files match on the reveal constructor today: 28 under
  `Vegas/Source`, 18 under `Vegas/Game`, 7 under `Vegas/Compile`.
- A new graph node kind and a new runtime payload need cases under
  `Vegas/Pending` and in the sequential-equilibrium development. Each case is a
  plain public event, so none needs a two-step refinement.
- The pinned statements quantify over programs and stay textually unchanged.

### Points to settle

- **Finiteness remains.** `CoversBindingValues`
  (`Vegas/Pending/ReactiveCompiledMenu.lean`) exists because every value a
  player may choose must fit within the wire's value bounds. A yielded value
  travels on the wire too, so the condition extends to yield events. It should
  be generalized and renamed rather than dropped.
- **Guards.** The simplest rule lets a yield guard read only public data and
  results that are already published, and checks it immediately. Allowing it to
  read the owner's unrevealed commitments requires generalizing
  `SourceProgram.Obligation`, whose subject must currently be a commitment
  cell.
- **Guard coverage.** `source_guards_hold` quantifies over commitment
  obligations. It stays true but says nothing about yield guards. A companion
  theorem keeps the guard guarantee complete.
- **Several values.** `yield x y z` as sugar for consecutive single yields is
  sound but produces one event and one envelope per value. A single envelope
  for several values needs either a product-typed payload, when the expression
  language has products, or events with several outputs, which is a larger
  graph change. The recommended core is a single-cell `yield`, with the
  multi-value form expressed through a product payload.

### Existing `commit x; reveal x` programs

The compiler should not rewrite `commit x; reveal x` into `yield x`. The
rewrite drops a cell, so it does not preserve terminal states and would need
its own equivalence theorem. Programs should use `yield` for public moves; a
lint can suggest it. A source-level theorem that the two forms induce
equivalent games over public outcomes would be a useful paper result, but
nothing depends on it.

### Relation to the early-opening obstruction

The [early-opening witness](early-opening-and-spe.md)
(`honest_source_early_opening_blocked`) is a `commit x; reveal x` program: a
stale withholding envelope and an early opening both address the separate
disclosure event, and readiness tokens make both inert. A `yield` program has no
separate disclosure event, so that witness has no counterpart there. This is
not a subgame-perfection result.
