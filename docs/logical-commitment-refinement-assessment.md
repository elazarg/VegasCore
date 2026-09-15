# Candidate-to-logical refinement assessment

## Recommendation: change the proposed boundary

The literal projection into the current one-binding
`Interaction.LogicalCommitment` should **not** be used as an intermediate
policy-simulation edge. A useful terminal-state classifier can be defined, and
honest generated traffic is close to its transition system, but the proposed
local step projection fails on the native cases analyzed below. The prerequisite
rejection mismatch is checked in
`InteractionTests/LogicalCommitment.lean` by
`incomplete_prerequisite_breaks_literal_projection`. The same test module's
`no_view_only_owner_opening` checks the missing private recall in a view-only
logical policy interface. The clock-erasure obstruction is checked separately
in `InteractionTests/LogicalCommitmentClock.lean`. Other examples below are
code-inspected; none establishes impossibility of a coarser strategic simulation.

This does not refute a logical-protocol boundary in general. The counterexample
establishes that graph-relative admission gates and owner preparation recall
are necessary additions to this particular kernel. It does not establish that
message identifiers, numerical clocks, or every rejected-payload distinction
must be copied into a future logical layer. Whether those observations can be
erased depends on the preservation theorem: uniform policy-local simulation
needs a sufficient logical observation, while a fixed-honest-opponent coupling
may instead use conditional laws or predrawn responses.

The kernel remains independently useful for local facts about first selection,
openability, public rejection, and attributed fallback. The recommendation is
to keep it in that role and change, rather than promote, the proposed boundary.

## The strongest plausible one-binding projection

Fix a compiled commitment node `c`, its reveal node `r`, and their common
owner `p`. Instantiate the logical handle type with
`CommitmentHandle Principal Nat` and `handleOwner := Prod.fst`. For a candidate
application state `native`, the natural state projection is:

```text
meanings(h) := native.application.service.lookup(h)
selected    := SealedProgram.accepted?(native.application.visible.events, c)

result :=
  if c is in timeouts or r is in timeouts then quit
  else if published?(events, r) = some v then opened(v)
  else pending
```

The timeout test must precede the `published?` test. Sent, inbox, and ledger
would be occurrence-preserving maps of native messages to logical claims, and
logical receipts would pair each projected included occurrence with the native
receipt boolean. Such receipt pairing needs the reachable invariant that every
successful pending inclusion appends one ledger message and one `(id, Bool)`
receipt; `MessageApplication.includePending` does not append either for a
missing identifier.

A proposed action projection would map:

- the owner's private `(slot, value)` command to `prepare(p, (p, slot), value)`;
- native submission to logical `submit`;
- replay to another logical `submit` by the broadcaster;
- successful delivery to `expose`;
- successful pending inclusion to `include`; and
- a clock step that first times out `c` or `r` to `settleQuit(p)`.

Other principals' preparations and clock steps irrelevant to this binding
would stutter. This is a precise candidate projection, but it does not commute
with all native steps.

## Concrete operational obstruction

`Interaction/SealedCandidateResolution.lean` declaration
`SealedProgram.candidateMessage?` checks more than the logical kernel:

```text
selection: sender/handle owner, node not done, all rule prerequisites done
opening:   the same checks, accepted source handle, and candidate verification
```

The same module's `SealedResolution.candidateHandle` additionally rejects a
payload naming an already timed-out node. By contrast,
`Interaction/LogicalCommitment.lean` declaration
`LogicalCommitment.State.applyClaim?` knows only whether this binding is
pending, whether it has a selection, the owner of the handle, and the candidate
meaning. It has no graph node, prerequisite state, or native timeout gate.

Therefore an owner-authored selection included before a graph prerequisite is
ready is publicly rejected natively but accepted by `recordInclusion`
logically. The checked example submits the second of two commitment nodes while
its predecessor is incomplete: the actual `candidateMessage?` validator returns
`none`, whereas the logical kernel selects the handle and records an accepting
receipt. The same mismatch occurs for an otherwise valid opening whose extra
graph prerequisites are incomplete. The receipt boolean exposes the mismatch.
Mapping that included payload to `Claim.malformed` would not repair a trace
projection: the sent and delivered occurrences exposed the original selection
or opening, and `Action.RealizableAt` requires an included logical claim to
have that provenance. It would also make the payload abstraction depend on
the later admission result.

Honest generated traffic avoids the main early-submission case. The compiled
policy emits openings only after its public publication barrier, and
`Vegas/Compile/SealedResolutionPolicy.lean` declaration
`resolvingPolicy_submission` restricts generated submissions to cached
commitments or ready openings. This supports an honest-trace use of the
kernel. It does not remove the gate needed to interpret an arbitrary owner
policy.

## Synthetic defaults

The timeout behavior in `Interaction/SealedResolution.lean` confirms that
ordinary logical opening is the wrong classification for defaults:

- `SealedResolution.expire` on a commitment appends the node to `timeouts` and
  creates no `.accepted` event.
- When the scan reaches a reveal whose source commitment timed out,
  `SealedResolution.visit` appends `.opened r nullValue` without adding `r` to
  `timeouts` and without creating an accepted handle.
- `SealedResolution.expire` on the reveal itself appends both
  `.opened r nullValue` and the reveal timeout.

Thus a naive projection can produce `selected = none` together with
`result = opened nullValue`, a state unreachable through logical `open`, which
requires a selected openable handle. The timeout-priority result definition
above instead maps both commitment and reveal defaulting to `quit`. This is a
sound settlement classifier when combined with the existing settlement
invariant: an opening whose reveal or source timed out equals `nullValue`.

That classifier is not by itself an exact observation projection. Native
players see the synthetic `.opened r nullValue` event and the precise timeout
list in `SealedResolution.PublicState`; the current logical view sees only an
attributed `quit` and selection. No synthetic `.accepted` event exists. A
future graph-logical gate could carry the default fact and value without
classifying it as a verified opening; the present kernel does not.

## Rejected payload observations

`Interaction/MessagePool.lean` declarations `MessagePool.View` and
`MessagePool.observe` expose exact `Message` values in local `sent` and `inbox`
lists and in the shared ledger. A message retains its sender-local identifier
and the full `SealedProgram.Payload` from `Interaction/SealedProgram.lean`:
commitment node and handle, opening node/handle/claimed value, cleartext
node/value, or malformed. `Interaction/MessageApplication.lean` adds public
identifier/acceptance receipts, while `MessagePool.replay` can create multiple
observable occurrences of the same envelope.

The logical claim quotient drops identifiers and collapses every unsupported
payload shape to `malformed`. Two natively distinguishable rejected payloads
can therefore have the same logical view. An unrestricted native policy may
branch later on their node, claimed value, identifier, multiplicity, clock, or
receipt identity. This is not hypothetical authority: `PlayerPolicy` receives
the complete prior list of player entries and the current full message view.

For honest compiled continuations much of this data is irrelevant. In
`Vegas/Compile/SealedResolutionPolicy.lean`, `resolvingPolicy_no_timeout`
reduces the policy before any timeout to the event/history projection, and
`resolvingPolicy_no_cleartext` proves that it does not emit cleartext traffic.
Those are honest-policy facts. They do not establish that the current quotient
is sufficient for an arbitrary replacement policy. Conversely, they leave
open whether a coupling specialized to fixed compiled opponents can erase
more information than a uniform policy simulation can. The current
`resolvingAcceptanceLaw` in
`Vegas/Compile/SealedResolutionReadBound.lean` conservatively retains the focal
player's complete history and view, including messages and receipts.

## Private preparation memory

The candidate service table is absent from every native player view because
`SealedResolution.host` in `Interaction/SealedResolution.lean` exposes only
`PublicState`. But `MessageInterface.PlayerPolicy` in
`Interaction/MessageApplicationPolicies.lean` receives its complete command
history, and `PreparedCandidateOwner.memory` in
`Interaction/SealedCandidateMemory.lean` identifies the owner's catalog
entries with the first-value cache computed from that history. An owner can
prepare `h` with `v` in two executions having identical public and message
views, then later submit the correct opening by recalling `v`.

The logical `State` updates the private `meanings` table but `State.observe`
does not expose it, and the kernel defines no policy history carrying private
preparations. Consequently a policy whose input is only the logical `View`
cannot reproduce even this ordinary owner behavior. Some owner-local recall,
either a projected command history or an equivalent first-preparation cache,
is therefore necessary. This conclusion is independent of whether public
clock and identifier observations are later retained or erased.

## What conditional randomization would require

Pointwise constancy of the abstract next-command law on every logical-view
fiber would be sufficient for a uniform policy-local backtranslation, but it
is false for arbitrary native policies because of the forgotten observations
above. Defining a logical response by averaging conditionally on a logical
view is a different route. It requires a proved conditional-independence or
state-sufficiency property under the same fixed honest opponents and
environment responses. Without it, a forgotten native observation can be
correlated with graph state; averaging may destroy that correlation and change
outcome laws. A predrawn-response construction is another way to retain the
needed correlation without declaring every clock or identifier part of the
logical protocol.

The current graph/candidate coupling keeps the full stopped native information
needed for its conditional reasoning. No theorem currently shows that the
one-binding quotient is a sufficient smaller statistic, especially when other
graph sites can place distinguishable traffic in the same player view. This is
an evidence-based uncertainty, not a proof that no smaller statistic exists.

## Relation to the strategic theorem

These failures concern particular operational and observation interfaces. They
do not rule out a fixed-profile expected-utility bound. That bound asks for a
legal graph deviation whose expected utility is at least the native deviation's;
it does not ask a logical policy to reproduce every native command.
`CandidateRoundModel.deviation_bound_of_support_floor` in
`Vegas/Game/SealedCandidate.lean` proves this weaker statement using the full
native-information coupling. Normal completed pairs agree on public utility;
timeout pairs satisfy the graph quitting cap and the fixed-opponent graph
support floor. The source theorem in `Vegas/Game/SourceCandidate.lean`
transports those conditions through the separate source/graph edge.

A logical intermediate game remains a possible factoring of that argument,
but its missing strategic certificate must not be confused with a missing
source-to-candidate payoff theorem.

## Criterion for further implementation

The [gated single-site analysis](logical-commitment-gated-experiment.md)
contains the transition table for graph admission, owner recall, exposure,
selection, rejection, and defaults. It identifies a local operational
projection with certified gate and settlement events; it does not establish an
autonomous logical game. Gates plus recall do not determine deadline progress.

Implementing that projection is worthwhile only with a concrete proof consumer:
name the existing native proof it will replace, the smaller interface it will
provide, and the observation law still required by the strategic argument.
A certified event projection that merely repeats the native handler's result
would establish state bookkeeping without simplifying policy extraction or
probability laws. There is currently no demonstrated replacement of those
parts of the active proof by this kernel.

## Decision

There is a valid local **outcome classifier**:

```text
normal verified event  -> opened(value)
commit or reveal default -> quit, with selected retained if one existed
```

There is also a useful honest-trace interpretation under the compiler's
prepared/readiness discipline. For the current kernel, the literal projection
fails through public receipt disagreement on prerequisite rejection and the
absence of owner preparation recall. Its present observation quotient is also
insufficient for a uniform arbitrary-policy simulation. Synthetic defaults
remain manageable as a timeout-priority settlement classification, not as
logical openings.

Accordingly, do not promote the current object unchanged. Keep it as a small
runtime-general safety model. A broader logical-protocol approach remains open,
but further implementation should require a demonstrated simplification under
the intended fixed-opponent preservation theorem.
