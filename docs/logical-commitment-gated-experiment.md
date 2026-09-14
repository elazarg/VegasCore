# Gated single-site logical commitment experiment

## Decision

**Change and continue only as an operational factorization.** Adding exact
graph-supplied admission gates and owner preparation recall removes the two
definite defects of the current one-binding kernel. It supports a small
stuttering projection of one candidate site if logical events are certified
facts about native transitions. It does not yet support an autonomous logical
game or a fixed-honest-opponent strategic simulation.

The concrete obstruction to the stronger claim is deadline phase. Current
eligibility booleans do not determine the next timeout: for `window >= 2`, two
reachable native states can have the same selected handle, projected candidate
meanings, readiness gates, and owner recall, but respectively two and one units
remaining before expiration. The same environment clock action leaves the
first pending and expires the second. Absolute clocks might still be erasable,
but only if the logical boundary treats timeout as a certified exogenous event
or retains a sufficient relative deadline phase. Gate plus recall alone is not
a Markov state for the native clock transition. This is a paper counterexample,
not a Lean-mechanized theorem.

This finding does not rely on assuming that a fixed response chooses the same
action on different native histories. That assumption is false in general.
The operational table below projects realized before/after transitions. The
later strategic question is whether their conditional law can be reproduced
with fixed honest opponents and the existing predrawn responses.

## Proposed minimal operational boundary

Fix one commitment node `c`, one reveal node `r`, their owner `p`, and the
reveal's source relation `r -> c`. Handles remain native owner/slot pairs.
The logical state needs only:

```text
candidate(h), h.1=p: fresh | openable(value) | unopenable
selected           : Option Handle
ownerRecall(slot)  : Option Value from p's first attempted private command
selectEnabled      : Bool
openEnabled        : Bool
settlement         : pending | opened(value) | defaulted
sent/inbox/ledger  : occurrence lists of site claims
receipts           : occurrence list of acceptance booleans
```

`ownerRecall` records the first attempted private preparation command by `p`;
it is not public to other players. It need not equal `candidate`: an accepted
unprepared handle is permanently unopenable, and a later private prepare
command is remembered even though it cannot revive the catalog entry.
`candidate` is restricted to handles owned by `p` and remains proof-facing
private state. Other principals' catalog changes are outside this site's
projection. The two gates are supplied by the graph/public-state projection,
not recomputed by the binding:

```text
selectEnabled :=
  c is not timed out
  and c is not done in events
  and every prerequisite of c is event-done or timed out

openEnabled :=
  r is not timed out
  and r is not done in events
  and every prerequisite of r is event-done or timed out
```

These formulas match the combination of
`SealedResolution.candidateHandle` and the discharged-rule checks in
`SealedProgram.candidateMessage?`, both in
`Interaction/SealedCandidateResolution.lean`. Selection additionally checks
the sender and handle owner. Opening additionally checks the selected source
handle and candidate verification.

The boundary should consume certified transition labels rather than implement
transport or time:

```text
prepare(p, h, v)
freeze(h)                         -- acceptance at another site owned by p
submitted(broadcaster, claim)
exposed(recipient, claim)
included(claim, accepted)
gates(selectEnabled, openEnabled)
defaulted(owner, cause = commitment | reveal)
```

For `included(_, true)`, the logical validator checks the appropriate gate,
authority, selection, and candidate meaning before changing semantic state.
For `included(_, false)`, it records the ledger occurrence and rejection
receipt without pretending the reduced kernel can derive every rejection.
The candidate-runtime refinement must prove that each supplied boolean equals
the actual `MessageApplication.includePending` receipt. This is smaller than a
message runtime: it has no identifiers, pending-copy operations, clock, or
service policy. It is also weaker than an autonomous executable game because
gate updates and defaults arrive with native/graph certificates.

## State and observation projection

For a reachable candidate execution `e`, project the semantic fields by:

```text
candidate(h) := e.native.application.service.lookup(h), only for h.1 = p
selected     := SealedProgram.accepted?(e.native.application.visible.events, c)
ownerRecall  := first attempted private value per slot in p's command history

settlement :=
  if c is in timeouts or r is in timeouts then defaulted
  else if published?(events, r) = some v then opened(v)
  else pending
```

For compiled prepared traffic, `PreparedCandidateOwner.memory` in
`Interaction/SealedCandidateMemory.lean` relates the successful first-value
cache to the catalog. That theorem is conditional on its owner-prepared
invariant and must not be applied to an arbitrary owner that first gets an
unprepared handle accepted. In that counterexample, acceptance changes the
catalog entry to `unopenable`; a later private command records an attempted
value in `ownerRecall`, while `CommitmentCandidates.prepare` leaves the catalog
unopenable. The proposed boundary retains both facts rather than conflating
them.

For observations, project only occurrences belonging to this site plus native
`.malformed` payloads:

- local native `sent` occurrences become logical `sent` occurrences;
- successful native delivery occurrences become local logical `inbox`
  occurrences;
- successful pending inclusions become logical ledger occurrences paired with
  the actual receipt boolean; and
- selection, opening, gates, and settlement come from the public application
  state.

This is an operational site projection, not an assertion that the resulting
view is strategically sufficient. Exact message values and sender-local
identifiers are exposed by `MessagePool.View` and `MessagePool.observe` in
`Interaction/MessagePool.lean`; the logical occurrence map deliberately
forgets identifiers. Traffic for other sites is filtered rather than
misclassified as malformed. Such filtering is acceptable for this local state
theorem but remains a strategic information obligation.

## Transition table

| Native realized transition | Required before-state facts | Projected logical transition | Result check |
|---|---|---|---|
| Owner private command `(slot, v)` | actor is `p`; `h = (p, slot)` | update attempted `ownerRecall` on its first occurrence; apply candidate preparation separately | `CommitmentCandidates.prepare` makes a fresh `h` openable and cannot change a fixed `h`; recall still records a later failed attempt |
| Other principal's private command | catalog update is outside the restricted `h.1 = p` projection | stutter | Candidate admission at `c` requires the selected handle owner to equal `p` |
| Submit relevant commitment/opening | native submit creates an exact pending message and local sent occurrence | `submitted(actor, claim)` | No selection or opening occurs at submission |
| Replay relevant claim | broadcaster knows the exact native message | another `submitted(broadcaster, claim)` occurrence | Native replay changes pending/sent only; semantic state stutters |
| Deliver relevant pending claim | `MessagePool.lookup id = some message` | `exposed(recipient, claim)` | Claimed value may become locally visible, but selection/result do not change |
| Include missing identifier | lookup is `none` | stutter | `MessageApplication.includePending` appends neither ledger nor receipt |
| Include malformed payload | lookup succeeds | `included(malformed, false)` | `candidateMessage?` rejects it; public ledger and false receipt remain |
| Include selection while `selectEnabled = false` | relevant commitment payload, correct owner possible | `included(select(h), false)` | Native prerequisite/done/timeout gate rejects; semantic state unchanged |
| Include first authorized selection | `selectEnabled = true`; sender and `h.1` are `p`; no prior selection | `included(select(h), true)`, then project all `refresh false` effects | Native and logical states select `h`; fresh `h` becomes unopenable, prepared `h` keeps its value; downstream gates may change |
| Include competing selection | a first selection already made, hence `c` is event-done | gate update to false, then `included(select(h2), false)` | First accepted handle remains selected |
| Include opening before selection | no accepted handle at `c` | `included(open(h, v), false)` | Claimed value remains visible in ledger, but result stays pending |
| Include opening after selection but with `openEnabled = false` | graph prerequisites incomplete or `r` timed out/done | `included(open(h, v), false)` | Public rejection; no semantic opening |
| Include valid opening | `openEnabled = true`; selected `h`; owner-authored; `candidate(h) = openable(v)` | `included(open(h, v), true)`, then `opened(v)` and all `refresh false` effects | Matches `candidateMessage?_opening_sound` in `Interaction/SealedCandidateOpening.lean`; downstream gates/default metadata may change |
| Include an accepted event at another site | its traffic occurrence is filtered from this site's claim lists | project gate/default changes and any `freeze(h)` for an accepted handle owned by `p` | Acceptance can freeze a fresh entry in the shared owner catalog; `refresh false` can stamp this site or propagate an existing source timeout |
| Clock step with no new local timeout | realized refresh leaves `c` and `r` out of timeouts | gate update or stutter | Semantic state unchanged even though hidden deadline phase changes |
| Clock step expires `c` | `c` ready, incomplete, and past its relative deadline | `defaulted(p, commitment)`; selection remains `none` | `SealedResolution.expire` adds timeout `c` and no accepted event |
| Same scan propagates source default to `r` | `c` just timed out and `r` is ready | retain `defaulted`; record graph default value `nullValue`, not a verified logical opening | `SealedResolution.visit` appends `.opened r nullValue` without a reveal timeout or accepted handle |
| Clock step expires `r` | selection exists; `r` ready, incomplete, and past deadline | `defaulted(p, reveal)` with the selected handle retained | `expire` appends `.opened r nullValue` and timeout `r`; private candidate meaning is unchanged |

The inclusion receipt is interpreted from the actual atomic result, and gates
and default metadata are then projected from the post-state. This mirrors
`candidateHandle`, which appends an accepted event and calls
`SealedResolution.refresh false` atomically. A rejected handler does not run
that refresh. An application-accepted inclusion at any graph site can change
this site's gates or propagate a default, even when its transport occurrence is
filtered from the one-site claim lists. Tick separately increments the clock
and runs `refresh true`.

The owner catalog is shared across that owner's sites. Accepting an unprepared
handle at another site changes its projected entry from `fresh` to `unopenable`,
even when no claim for the current site is recorded. The operational projection
must retain this `freeze` effect; per-site catalogs cannot be assumed independent.
It remains proof-facing state, not an additional logical player observation.

## Required traces

### Competing commitments

```text
prepare h1 = v1
prepare h2 = v2
selectEnabled = true
include select(h2) -> true
gate update: selectEnabled = false
include select(h1) -> false
include open(h1, v1) -> false
include open(h2, v2) -> true when openEnabled
```

The catalog laws in `Interaction/CommitmentCandidates.lean` establish that
accepting `h2` cannot change either prepared value, while the public event log
establishes first-selection stability. This trace factors operationally.

### Early pending opening

```text
submit open(h, v)
deliver it to q                  -- q sees the claim
include select(h) -> true
include the still-pending open -> true when openEnabled
```

Validation occurs at inclusion, so an opening submitted or delivered before
selection can still be accepted later if that same copy remains pending until
selection and all gates hold. This is only an operational possibility, not a
claim that early submission is strategically harmless. If the environment
includes it early, the receipt is false and that pending copy is consumed; a
replay or new submission is needed for a later attempt. The occurrence table
represents both branches without equating visibility and acceptance.

### Malformed traffic followed by commitment timeout and propagated default

```text
include malformed -> false
clock step expires c
same source-ordered refresh appends opened(r, nullValue)
```

The logical result is `defaulted(commitment)` with no selected handle. It must
not be `opened(nullValue)`: no handle was accepted or verified. The public
graph-default fact is retained separately for continuation/settlement.
`SettlementInvariant.opened_eq_null_of_timeout` in
`Interaction/SealedResolutionSettlement.lean` supplies the value check.

### Malformed traffic followed by reveal timeout

```text
include select(h) -> true
include malformed -> false
clock step expires r and appends opened(r, nullValue)
```

The logical result is `defaulted(reveal)` and retains `selected = some h` and
the immutable candidate meaning. Again, the synthetic public default is not a
verified opening of `h`.

## Counterexample to gates-plus-recall as an autonomous state

Assume `window >= 2`. Start from a reachable state in which the site's public
prerequisites have just become complete and `refresh false` has stamped it at
clock `t`; the site is still incomplete. From this common state, run respectively
`window - 2` and `window - 1` clock steps that do not yet expire it. The first
prefix has clock `t + window - 2` and two units remaining; the second has clock
`t + window - 1` and one unit remaining. Because intermediate `tick`s make the
strictly pre-deadline comparisons fail, both prefixes are pending and have
identical projected claims, selection, candidate meanings, owner recall,
`selectEnabled`, and `openEnabled`.

`PublicState` stores both `readyAt` and `clock` in
`Interaction/SealedResolution.lean`. `SealedResolution.tick` first replaces
the clock by `clock + 1` and then calls `refresh true`; inside that refresh,
`SealedResolution.visit` tests

```text
firstReady + window <= clock
```

on the incremented state. Apply one further identical environment application
command, whose kernel is `SealedResolution.tick`. The two-unit prefix advances
to one remaining unit and stays pending. The one-unit prefix reaches equality
and expires. No transition function of the proposed gate-and-recall state alone
can match both. A pending zero-slack state is not used in this construction.

This counterexample proves that the two booleans plus recall are insufficient
for a step-by-step autonomous abstraction. It does not prove that the absolute
clock must be public in a logical game. Three possibilities remain logically
distinct: retain relative slack, consume certified timeout events as above, or
derive a conditional timeout kernel under a fixed response coupling.

## Operational projection versus strategic sufficiency

The transition table is state-by-state and can use the realized native
before/after pair to emit `defaulted` or stutter. That is enough for a forward
operational projection theorem. It says nothing about whether a logical policy
can choose the same distribution of future actions.

For honest continuations, the current compiler already supplies strong
irrelevance facts. `resolvingPolicy_submission` and
`resolvingPolicy_no_cleartext` in
`Vegas/Compile/SealedResolutionPolicy.lean` constrain generated traffic, while
`resolvingPolicy_no_timeout` shows that absolute clock and readiness timestamps
do not select a different source kernel before timeout. Owner recall is read
from the retained command history.

For an arbitrary focal policy, erased observations can affect actions.
`MessageInterface.PlayerPolicy` receives the complete prior views and commands,
and its current view contains exact sent/inbox/ledger messages and public
receipts plus `PublicState.clock` and `readyAt`. A fixed policy function may
legitimately return different actions on two such native histories. Therefore
the strategic proof must not postulate pointwise command equality after
projection.

A fixed-honest-opponent proof may instead couple or condition these different
responses. That requires showing that the predrawn response and retained
logical information preserve every correlation with graph state needed by the
outcome law. The present table neither proves nor disproves that property.
Filtering other-site traffic is especially significant because the fixed
honest opponents and environment may react to it even when this site's
semantic state is unchanged.

## Exact next proof

One proof is warranted before any strategic API work: a **single-site
stuttering operational projection** for reachable candidate executions.
Fix `c`, `r`, `p`, their rule shapes, and the existing candidate acceptance,
opening, settlement, and owner-memory invariants. Define the gated/recall
projection above and an effect-dependent event projection from each native
action and realized successor. Prove:

```text
projectState(next) =
  runCertified(projectState(before), projectEffects(before, action, next))
```

for private commands, submit, replay, delivery, inclusion, and clock steps.
The inclusion case must prove equality with the actual receipt boolean; the
clock case must distinguish commitment timeout, reveal timeout, and propagated
default without manufacturing an accepted handle.

If this theorem requires exact message identifiers or absolute clocks in
`projectState` merely to state final projected-state equality, the operational
boundary has failed its intended simplification. If it passes, it establishes
only the semantic factorization. Strategic sufficiency should remain with the
existing full-information stopped coupling until a separate conditional-law
theorem is proved.
