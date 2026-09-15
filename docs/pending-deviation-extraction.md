# Pending-deviation extraction

At a focal player's bind or resolve node, a native service block is not itself
one source-language move. It may contain private preparation, submission,
delivery, rejected inclusion, clock ticks, and even actions belonging to later
graph phases. The relevant stopping time is therefore the first individual
native transition whose graph program counter increases.

For a native path

\[
  s_0 \xrightarrow{a_0} s_1 \xrightarrow{a_1} \cdots,
\]

starting at phase \(k\), `FirstPhaseChange` selects the least \(j\) such that
`phase(s_{j+1}) > k`. Monotonicity of native execution proves that this prefix
exists whenever the whole path ends beyond \(k\). This avoids attributing later
phase changes in the same nominal block to the focal decision.
`FirstPhaseChange.before_reachable` also exposes the actual action-list prefix
reaching \(s_j\), so public agreement and binding soundness transport from the
initialized state to the extraction point.

`State.RealizesOwnAction before action after` records the graph-semantic
effect: the immutable typed environment is extended exactly as the graph
semantics extends it for `action`. Message-pool state, receipts, preparation
caches, and disclosure markers do not occur in this relation.

- At `bind`, accepted inclusion extracts the value actually frozen into the
  immutable cell. Fresh, unopenable, ill-typed, or expired candidates extract
  `failure`.
- At `resolve`, an accepted verified opening extracts `true`; authenticated
  withholding or expiry extracts `false`. Public agreement identifies concrete
  guard evaluation with graph evaluation. `State.BindingSoundness` proves that
  any verified typed opening equals the immutable bound source value.

The resolve Boolean cannot be reconstructed from the residual published value:
`true` can still publish `failure` when the bound value is failure or a guard
rejects. Extraction consequently inspects the admitted packet/tick, while its
meaning is justified from immutable state and binding soundness.

The extracted Boolean is the effective wire action, not a cached intention:
accepted opening is `true`, and withholding or expiry is `false`. Thus a cached
`true` followed by canonical withholding after guard failure extracts `false`;
an adversarial cached `false` followed by a valid opening extracts `true`.
Future simulation cannot identify arbitrary native markers with this extracted
history. It must either carry native memory separately or establish that the
effective graph view determines the later native response on initialized
support.

## Locality boundary

Equality of `Graph.DecisionView` alone does not imply equality of arbitrary
native commands. A native player policy additionally sees its message inbox,
sent traffic, receipts, prepared slots, and authenticated command history; an
environment policy sees the public pool and receipts. Thus an unrestricted
policy can distinguish two native states with the same graph view and change
submission timing or payload.

For initialized supported runs, the following proposed induction should
establish the required locality statement for a fixed deterministic focal
response and deterministic service-compatible environment response. Opponent
policies and chance draws do not have to be identified. Compare two prefixes at
the same invocation index, ending at focal phase `k`, and assume their focal
`Graph.DecisionView`s agree. Use this endpoint-parameterized prefix relation.

1. Each current graph environment is the restriction of its endpoint
   environment, so equality of the endpoint focal observation restricts to
   equality of focal observations at every earlier context. In particular all
   earlier public samples and resolution outputs agree, as do focal-owned
   sealed values. Foreign sealed values may differ.
2. The native cursors agree on the graph suffix, context, public values, `pc`,
   `clock`, `enteredAt`, bindings, the complete pool (including message
   counters), receipts, invocation index, and remaining schedule. Environment
   histories agree exactly. Native action traces need not agree and are not
   policy inputs.
3. The focal principal's full authenticated history, current message view, and
   prepared-slot catalogue agree. These facts are maintained forward from equal
   initial focal inputs: equal full inputs and the fixed response yield the same
   arbitrary focal command, including malformed submissions, replay, unrelated
   preparation, and dishonest markers. They are not inferred from the extracted
   graph action or endpoint observation. In particular an effective bind value
   does not determine which raw values were prepared, and an effective resolve
   Boolean does not authenticate a remembered marker.
4. For each nonfocal compiled owner, retain only equal phase status: whether its
   private cache/marker is occupied and whether the phase packet was submitted.
   The compiled policy tail is the same because the graph suffix and unchanged
   opponent profile are the same. Candidate meanings, source-policy draws, and
   authenticated histories need not agree.

This is not a purely forward invariant: it is a bridge relation parameterized
by the common endpoint observation. At an earlier phase the endpoint determines
the public result that the phase must eventually append. The phase cases are:

- A public sample has the same value because that value occurs in the endpoint
  observation, although the two chance kernels remain live.
- A nonfocal bind may prepare different hidden raw values, but preparation is
  invisible and both runs submit the same canonical `(owner, prepared site)`
  handle on the same invocation. Acceptance therefore has the same public
  shape, receipt, and timing.
- A nonfocal resolve may remember different Booleans. The compiled second step
  computes the accepted proposal first and `disclosureCommand` is canonical in
  that publication result: failure emits `withhold`, while success emits the
  unique typed opening of the published value. Equality of the endpoint public
  result therefore gives equal visible packets, receipts, and timing.
- At every invocation of the focal principal, regardless of who owns the graph
  phase, equality of its complete native input makes the arbitrary fixed
  response emit the same command. The focal replacement is not assumed to be a
  compiled policy and need not wait at nonowner phases.
- The deterministic environment receives equal public pool, application view,
  receipts, and history, hence emits the same service command.

The important memory ambiguity is intentional. A nonfocal `true` whose value or
guard yields failure and a nonfocal `false` both emit canonical `withhold`; their
private remembered Booleans differ. Requiring equal nonfocal histories would
make the relation false. Later nonfocal source choices may consequently differ,
but the endpoint result again canonicalizes their visible traffic. This is why
the induction must retain phase occupancy/timing while allowing private
contents to differ.

Initial states start this relation when their focal graph observations agree:
public projections and canonical initial binding addresses agree, focal
prepared slots are fresh, and foreign private initial candidates remain hidden.
A finite private initial law is used to choose one response-function mixture
before sampling the initial state. It is not needed for the pointwise locality
argument and does not license conditioning the source policy on hidden setup
data.

At phase `k`, the proposed relation gives equality of the focal policy's
complete native input, not merely its graph projection. Determinism would then
give the same native response sequence through the first actual phase change,
and the checked extraction lemmas turn that transition into the same effective
graph action. This bridge induction is not yet a Lean theorem in
`MessageDeviationExtraction`; that module proves the stopping/extraction facts
it consumes. The intended claim is only action locality. Residual outcome laws
still contain independent opponent and chance continuations.
