# Source-to-event-graph edge

This note specifies the next compiler edge to implement. It is a design, not a
checked compiler, execution theorem, or backend result.

## Objective

Compile a structurally accounted `SourceProgram` to an immutable event graph
without changing its moves, observations, failure behavior, chance law, or
payoffs. The graph must support heterogeneous payload types and explicit
`PublicationResult` values.

For every source behavioral profile, decoding the graph execution must give
exactly the source outcome law. For every unilateral graph deviation, the
decoded law must be an exact source unilateral-deviation law, or the stated
finite mixture required by the surrounding simulation interface. Opponents'
source strategies and the exogenous chance contract remain fixed.

## Current API blockers

The current `EventGraph.NodeSem` has only `sample`, guarded `commit`, and raw
copying `reveal` nodes.

* `commit` accepts an `L.Val` only after immediately evaluating an ordinary
  `EventGuard`. A source binding is not immediately guarded and also admits an
  unopenable choice without requiring an inhabitant of its payload type.
* `reveal` is internal and copies one field. It cannot retain a strategic
  disclosure `Bool`, compute failure, or check deferred guards.
* `CommitAction` and `CommitPolicy` assume homogeneous `L.Val` actions.
* `CommitPolicy` receives only a `ReadEnv`; it explicitly receives no own-action
  history. A final publication result does not always reconstruct that history.

These are graph-shape limitations. The compiler must not compensate by adding
Boolean equivalences or expression constructors to `IExpr`.

## Graph-native source operations

Add operation-specific strategic nodes with a dependent action family.

### Bind

A `bind who A` node chooses a graph-native value
`BoundChoice (L.Val A) = unopenable | value a`. Its owner-private output field
has type `Result A`. The node writes through
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

EventGraph should define source-independent retained metadata, not import
`Vegas.Source` and not store an opaque semantic closure. A deferred guard
contains:

* ordinary typed `GuardCode`;
* its exact `exprDeps` support;
* a typed mapping from each schema binding to either an ordinary field or a
  `Result` field; and
* an executable lifted evaluator.

The evaluator gives failure precedence over pending, calls ordinary guard code
only when every supported input has a payload, and treats the subject as a
required component even for constant code. Backends lower this explicit
metadata and the graph-native resolve primitive.

## Last-resolver placement

Traverse source operations in their canonical order and record the unique
reveal occurrence for each open private resource. For each guard, collect its
subject and every private publication in the guard's static support. The
resource-accounting proof supplies a later unique reveal for each such open
resource. Choose the maximum reveal position.

Attach that guard to the atomic resolve at this maximum position. Before that
point at least one required component is pending, unless a failure has already
waived the guard. At the chosen resolve all components are terminal: a failure
waives the guard, while all-success values run the ordinary relation. Therefore
only this resolve can newly reject, matching canonical source execution and
making the current publication fail without modifying prior SSA fields.

The compiler proof must establish this placement property from source order,
freshness, ownership, and open-obligation accounting; it must not assume it as
an unchecked lookup invariant.

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

Source samples remain exact `EventDist` nodes mapped from `DistExpr`. Generated
prerequisites enforce canonical source order, including between strategic and
internal operations. Decoding maps private binding fields back to bound source
cells, atomic resolve fields to both derived private publication status and the
corresponding public alias, and terminal public fields to payoff environments.

The implementation is complete only after proving exact honest-profile laws,
observation correspondence with own recall, and exact unilateral deviation
laws. Graph well-formedness or matching terminal stores alone is insufficient.
