# Pending-deviation extraction

This document describes the extraction used by the checked pending-message
deviation law. The replay-locality theorem proves that each reached focal
observation determines one normalized graph action; completion extends that
partial relation to a total behavioral policy without consulting own-action
history.

At a focal player's bind or resolve node, a native service block is not itself
one source-language move. It may contain private preparation, submission,
delivery, rejected inclusion, clock ticks, and even actions belonging to later
graph phases. The relevant stopping time is therefore the first individual
native transition whose graph program counter increases.

For a native path

\[
  s_0 \xrightarrow{a_0} s_1 \xrightarrow{a_1} \cdots,
\]

starting at phase \(k\), `exists_first_phaseChange_invocation` selects the first
invocation that advances the graph phase. Its supported prefix retains actual
policy histories and the continuation to the endpoint. Monotonicity guarantees
such an invocation when the endpoint is beyond \(k\), without attributing later
phase changes in the same nominal service block to this decision. Initialized
reachability carries public agreement and binding soundness to the selected step.

`State.RealizesOwnAction before action after` records the graph-semantic
effect: the immutable typed environment is extended exactly as the graph
semantics extends it for `action`. Message-pool state, receipts, preparation
caches, and disclosure markers do not occur in this relation.

- At `bind`, accepted inclusion extracts the value actually frozen into the
  immutable cell. Fresh, unopenable, ill-typed, or expired candidates extract
  `failure`.
- At `resolve`, a successful accepted publication extracts `true`; every
  failure result, including withholding, expiry, bound failure, and guard
  rejection, extracts `false`. Public agreement identifies concrete guard
  evaluation with graph evaluation. `State.BindingSoundness` proves that any
  verified typed opening equals the immutable bound source value.

The original disclosure intention cannot be reconstructed from the published
value: `true` can still publish `failure` when the bound value is failure or a
guard rejects. The extracted action uses a canonical representative of this
effect, justified from immutable state and binding soundness.

The extracted Boolean is the canonical effective result, not a cached intention
or merely the packet constructor: success is `true` and failure is `false`.
Thus a cached `true` followed by canonical withholding after guard failure
extracts `false`; an adversarial opening that is accepted but guard-rejected
also extracts `false`. Future simulation cannot identify arbitrary native
markers with this extracted history. It must either carry native memory
separately or establish that the immutable focal observation determines the
later native response on initialized support.

## Locality boundary

Equality of `Graph.DecisionView` alone does not imply equality of arbitrary
native commands. A native player policy additionally sees its message inbox,
sent traffic, receipts, prepared slots, and authenticated command history; an
environment policy sees the public pool and receipts. Thus an unrestricted
policy can distinguish two native states with the same graph view and change
submission timing or payload.

For initialized supported runs, the checked replay induction establishes
locality for a fixed deterministic focal
response and deterministic service-compatible environment response. Opponent
policies and chance draws do not have to be identified. Compare two prefixes at
the same invocation index, ending at focal phase `k`, and assume their focal
graph observations agree. Use this endpoint-parameterized prefix relation.

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

At phase `k`, the replay relation gives equality of the focal policy's complete
native input, not merely its graph projection. Determinism gives the same native
response sequence through the first actual phase change, and the extraction
lemmas turn that transition into the same effective graph action.
`Vegas.Pending.DeviationActionLocality` packages this replay as
`servicePlan_reachedOwnAction_locality_pure`. If two reached actions occur at
unequal schedule indices, phase monotonicity and endpoint ownership force the
earlier run to advance before the later focal-owned endpoint, contradicting the
shared typed cursor; equal indices use the paired invocation replay laws. The
conclusion is action locality only. Residual outcome laws still contain
independent opponent and chance continuations.

## Coupling at actual invocations

`ReachedOwnAction` records an initialized supported schedule prefix, its next
supported invocation, and the normalized graph action realized by that
invocation. Observation-locality makes this relation single-valued at each
focal graph decision. Its totalization chooses failure at unreached binding
observations and withholding at unreached resolution observations.

The residual graph law ignores the deviator's untrusted native cache and uses
this extracted policy. It retains every other player's actual compiled cache
and logical history. Focal stuttering steps preserve that law; effective focal
steps must agree with the extracted action. Nonfocal steps retain their original
policy kernels, including hidden remembered intentions.

For focal inclusion, conservation is required only for commands actually in
the environment invocation's support. Requiring it for every pending packet
would be false: the focal player can submit competing commitments whose
contents differ. The fixed environment response selects the effective one.
An unselected packet is not a second action of that same execution.
