# Source-to-typed-graph edge

This note specifies the failure-aware source-to-graph edge. The shared guard
evaluator, typed graph semantics, compiler, and strategic correspondence are
checked. The certificate proves exact decoded outcome laws, gives every
unilateral graph deviation one exact source-policy preimage against unchanged
opponents, and derives same-error Nash equivalence. It requires neither failure
dominance nor finite payload or action domains.
The target here is `Vegas.Graph`. The candidate-message backend still consumes
`Vegas.EventGraph.Graph`; adapting the backend to the typed graph and proving
its strategic law remain necessary for the complete native theorem.

## Objective

Compile a structurally accounted `SourceProgram` to an immutable typed graph
without changing its moves, observations, failure behavior, chance law, or
payoffs. The graph must support heterogeneous payload types and explicit
`PublicationResult` values.

For every source behavioral profile, decoding the graph execution must give
exactly the source outcome law. For every unilateral graph deviation, the
decoded law must be an exact source unilateral-deviation law, or the stated
finite mixture required by the surrounding simulation interface. Opponents'
source strategies and the exogenous chance contract remain fixed.

## Representation requirements

Binding admits both ordinary and unopenable choices, including when the
ordinary payload type is empty or its guard is unsatisfiable. Resolution is a
strategic disclosure decision followed by deferred checking, rather than an
internal copy. The two operations therefore need different action types.
Policies also retain their own-action history: public results alone do not
determine which disclosure choices produced them.

These requirements concern the graph's operations and observations; they do
not require Boolean equivalences or expression constructors in `IExpr`.

## Typed immutable graph

`Graph Player L Γ Δ` is a typed sequence of SSA nodes, in canonical
topological order. Each node appends one immutable field; its typed references
point to earlier fields. The initial and terminal field contexts are both type
indices, so execution and outcome decoding need no terminal-layout casts.
The sequence order is part of this graph's semantics. Reordering is a separate
compiler transformation, not an implicit scheduling freedom in this edge.

The graph stores typed expression/distribution code, field references, and
specialized guard code. It contains no source program, source-state interpreter,
mutable publication cells, or dynamic guard registry. Initial values are inputs
to the graph executor, separate from the public graph code.

## Graph-native source operations

The strategic nodes have operation-specific action types.

### Bind

A `bind who A` node chooses a `PublicationResult (L.Val A)`, in bijection with
the source's unopenable-or-ordinary binding choices. Its owner-private output
field has type `Result A`. The node writes through
`IExpr.ResultTypes.valueEquiv`: the failure constructor encodes unopenability,
and success encodes an ordinary binding. This field is private representation;
the resource's publication status remains pending until resolution.

No source guard runs at bind time. Initial private inputs use the same private
field representation.

### Atomic resolve

A `resolve who A` node chooses Lean `Bool`, reads the immutable binding field
and the required prior public-result fields, and atomically writes a public
field of type `Result A`.

Withholding or an unopenable binding writes failure. Disclosure proposes the
bound value; retained deferred guards either accept that value or turn this
resolution into failure. Earlier successful publications are never retracted.

This is not commitment/reveal fusion: binding and resolution remain distinct
source moves. Atomic resolution prevents an intermediate graph state from
turning disclosure choice and its public result into separate source stages.

## Typed deferred guards

`DeferredGuardCode` in `Foundation` supplies one shared source-independent
evaluator. The source adds a source-read adapter; the graph adds typed field
references and literal pending operands. The retained code contains:

* ordinary typed Boolean expression code;
* its exact `exprDeps` support;
* a typed mapping from each schema binding to an ordinary public field, a
  public `Result` field, or literal pending; and
* an executable lifted evaluator.

The evaluator gives failure precedence over pending, calls ordinary guard code
only when every supported input has a payload, and treats the subject as a
required component even for constant code. Backends lower this explicit
metadata and the graph-native resolve primitive.

## Guard specialization at resolution

The compiler tracks where each private resource's publication is represented:
literal pending until reveal, then its immutable public result field. At a
resolve node, specialize the entire retained guard registry through this map.
Guard code is scoped over a temporary proposed-result field plus the previous
graph fields. The temporary field is available only to the atomic checker;
players observe only the accepted public result.

This matters when the current resource is a dependency of another commitment's
guard. For `commit y where x = y; reveal y; reveal x`, the `x` resolution must
check the retained relation about `y`, not only guards whose subject is `x`.
Substituting the current proposal in every relevant guard reproduces the
source's tentative-state check directly. A rejection replaces only the current
proposal with failure; earlier public results and raw private bindings remain.

Checking a guard only at its last required disclosure is a possible code-size
optimization. Its proof would show that earlier checks cannot reject and later
checks remain satisfied. The first exact compiler does not need this pass:
specializing the full registry avoids a separate placement proof and gives a
direct local correspondence with the source rule.

## Observations and own memory

Choice footprints expose exactly the source observation at each occurrence.
The graph strategic information state must additionally retain the acting
player's own ordered `bind` and `resolve` actions. Extending policy observation
with authenticated own-action history is preferable to extra log nodes or
multi-output resolution nodes.

A minimal counterexample shows why. Bind an unopenable value, then choose
`disclose = true`; alternatively choose `false`. Both public resolutions are
failure, but a later source action may depend on which Boolean was chosen.
A graph policy that sees only the failure field merges these source histories,
so direct observation correspondence fails. Outcome-law preservation without
that memory would need a separate policy-realization argument; equality of
failure fields does not establish it.

## Chance, sequencing, and decoding

Source samples retain their exact `DistExpr` code and public field map.
Graph order follows canonical source order, including between strategic and
chance operations. Decoding maps private binding fields back to bound source
cells, atomic resolve fields to both derived private publication status and the
corresponding public alias, and terminal public fields to payoff environments.

The implementation proves exact honest-profile laws, observation
correspondence with own recall, and exact unilateral-deviation laws. Graph
well-formedness or matching terminal stores alone would not have sufficed.

## One execution proof and a strategy retraction

Let `C` compile a source policy and `B` backtranslate a graph policy. Each
operates playerwise. Graph observations encode exactly the source-visible
fields, omitting the redundant private publication status reconstructed from
public result fields. Encoding a decoded graph observation returns the original
observation; own-action histories have the same round trip.

Consequently `C (B q) = q` for every graph policy, including off-path inputs.
The reverse identity is unnecessary: source policies can differ on inconsistent
observations which source execution never produces.

One induction proves the honest law for every source profile. For an arbitrary
graph deviation `q` by player `i`, apply that law to the source profile with
`B q` at `i`. Playerwise compilation leaves opponents unchanged and the
retraction identifies the compiled replacement with `q`. This yields an exact
single-policy deviation law, without a second whole-program probability proof.
The generic simulation interface then derives Nash and same-error approximate
Nash correspondence for source-outcome utilities.

The checked implementation is organized around three results:

* `compileGraphPolicy_backtranslate` in
  [GraphPolicy.lean](../Vegas/Compile/GraphPolicy.lean) is the policy retraction.
* `Initial.graph_honest_law` and `Initial.graph_payoff_law` in
  [GraphLaw.lean](../Vegas/Compile/GraphLaw.lean) prove the decoded state law and
  correctness of the graph's executable payout projection.
* `Initial.graph_deviation_law`, `Initial.graphSimulation`, and the Nash
  corollaries in [GraphCompilation.lean](../Vegas/Game/GraphCompilation.lean)
  supply the strategic certificate. `Paper.lean` delegates its source-to-graph
  capstones directly to these results.

## Observation obligation for public-message lowering

Atomic graph resolution publishes only the accepted result. A public-message
backend must also account for the candidate visible before admission. In
particular, an opening rejected by a guard can reveal a private raw value even
though its graph result is failure. Equality of ledger results does not hide
that value.

For compiled play, the resolver can compute the check before sending: it knows
its own binding, and the specialized guard inputs are public fields, the
current proposal, or literal pending. A rejected proposal can therefore be
represented by failure without publishing its raw value. The policy must
retain its logical disclosure choice in its own memory; an eventual failure
receipt alone does not distinguish disclosure followed by rejection from
withholding. This is an implementation obligation, not a pending-message
theorem established by the source-to-graph edge.

The open protocol must still permit a deviator to transmit a rejected raw
opening. For unilateral-deviation simulation, the unchanged compiled opponents
must ignore that extra content in their decision policies. The deviator already
knows its own candidate; the proof must account for its extra traffic and
receipts without assuming that malformed traffic is invisible. A theorem about
arbitrary target contexts would require a stronger observation contract.
