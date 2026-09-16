# Source to event graph

The compiler lowers the complete failure-aware `SourceProgram` language to
`Vegas.EventGraph`. The graph retains typed node code, immutable binding and
publication fields, conditional chance kernels, and terminal payoff expressions.
Concrete initial values are separate inputs, so one graph and one strategy
space serve an entire private setup law.

The source-order execution theorem concerns the graph's canonical scheduler.
The asynchronous theorem additionally accounts for the scheduling information
available to a deviating player. Both use the same graph executor.

## Operations and guards

A binding chooses an ordinary payload or unopenability and stores it privately.
It does not execute its deferred guard. An atomic resolution chooses disclosure
or withholding, evaluates the retained checks, and publishes a typed success or
failure. It preserves the original disclosure Boolean in the actor's history:
a rejected `true` and a withheld `false` can have the same public result.

The shared `DeferredGuardCode` evaluator gives failure precedence over pending,
and executes ordinary guard code only when every required operand has a payload.
The guard subject is required even for a constant expression. No satisfying-value
or finite-payload assumption is imposed.

The compiler tracks each private resource as pending until resolution, then as
its immutable public result field. At a resolution it specializes the retained
guard registry with the current proposal and prior results. This includes guards
whose subject is another resource. For example:

```text
commit P.x;
commit P.y where x = y;
reveal P.y;
reveal P.x;
```

With P's mismatching bindings, disclosing y first
can succeed while x is pending; the later x disclosure fails its retained
relation. Exchanging the resolutions can change which publication fails.
The compiler therefore preserves their order. Rejection replaces only the
current proposal with failure, not an earlier successful publication.

Typed source-to-graph references and local evaluation proofs are in
`Vegas.Compile.EventGraphLayout`, `EventGraphCompiler`, `EventGraphEvaluation`,
and `EventGraphReadout`. Whole-program graph assembly is in
`Vegas.Compile.EventGraphAssembly`.

## Dependencies and observations

An event is ready when its predecessors have completed. Numeric event IDs
provide a topological rank, not an imperative program counter. Source lowering
requires:

- every earlier event before a public event;
- every earlier public event before any later event;
- each player's earlier bindings before that player's later bindings.

Independent bindings owned by different players may therefore commute. These
edges protect policy observations, not only expression reads. A constant guard
does not prevent a player from using an earlier public coin in its strategy.

The `BarrierOrdered` certificate requires these edges and permits extra ones.
Sequential compilation adds every earlier event as a predecessor without changing
node code, payloads, or payoffs. Ready sequential events have precisely their
source prefix completed.

Graph observations include visible fields, public completion order, and original
own actions. Compiled source policies use the source-ranked logical view.
Arbitrary graph deviations may also use completion-order information.

## Canonical and asynchronous correspondence

`EventLowering.canonical_setup_law` proves exact decoded terminal-state laws for
the canonical source-order execution. The state decoder reconstructs publication
status and public aliases from the immutable graph fields, without inventing
payload defaults.

`EventLowering.canonical_deviation_terminalState_law` gives every canonical
graph replacement one source-policy backtranslation, uniformly over concrete
initial states. `canonical_setup_deviation_law` packages this result over
distributed private setup. Same-error Nash follows by specializing the graph
scheduling theorem to canonical execution. Backtranslation need
only agree on actual canonical decision observations; a global identity on
arbitrary, inconsistent graph observations is not required.

`EventLowering.scheduled_setup_law` gives the same honest terminal-state law under
adaptive public graph scheduling. `scheduled_setup_deviation_law` represents
each unilateral asynchronous graph replacement by a finite mixture of source
policies. The mixture is chosen before private setup is sampled and leaves
opponents unchanged. `Vegas.Game.EventCompilation` supplies the strategic
certificate and equilibrium consequences.

None of these laws identifies execution traces. Payoffs and arbitrary utilities
of decoded source outcomes are transported by their outcome laws.

## Public-message lowering

Graph resolution exposes the accepted result; a public-message runtime also
exposes opening traffic before inclusion. An unchanged compiled player
prevalidates its proposed disclosure using its own binding and public guard
inputs. Rejection emits failure without exposing the rejected raw value, while
private own-action memory retains the original disclosure decision.

A deviator may still send raw or malformed openings. The unchanged opponents
follow their compiled observation-local policies; the native proof accounts for
delivery, histories, retries, and environment reactions. These are proved
backend obligations, not consequences of graph syntax alone. See the
[pending-message proof](event-pending-deviation.md) and
[service contract](event-service.md).
