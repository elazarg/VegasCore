# Sequential-equilibrium preservation with asynchronous submissions

The target is a commit–reveal program implemented on an idealized blockchain
where players can send at any opportunity after prerequisites are public.
Sending opportunities, silence and pending reception are not public facts.
The ledger alone determines the public record. A contract may delay readiness,
define packet authorization and penalties, and escrow funds; it cannot impose
a public order of who has had a chance to send, observe an empty global mempool,
or force a block producer to empty that pool.

No end-to-end preservation theorem for this target is established here.
The [scheduled-service benchmark](se-publication-scheduled-benchmark.md) proves
a more restricted mathematical statement with a fixed public sender calendar.
Its no-padding and replay-history reconstruction arguments depend on that
calendar and cannot justify the asynchronous target.

The incompleteness is mathematical, not only unimplemented Lean assembly.
Even granting the stated publication and evidence-delivery bounds, there is
no constructed joint timing/recovery policy whose source comparisons hold
at every actual private information set for one specified asynchronous
service. The scalar timing result covers a narrower success/own-floor
process; foreign failure and rollback are not instances of that process
without further proof.

The generic finishing principles are available. One legal fully mixed family
with uniformly vanishing local gains and the selected initialized-law limit
would yield SE by the finite Bayesian limit argument. Separately finding an
optimal timing policy, a rational handler completion and a reporting
equilibrium does not show they form that same family. Controlled replay
effects and concrete evidence acquisition are additional runtime obligations,
not consequences of padding or a larger deposit.

## What the contract can control

The contract can record a public reveal-block closure time c, reject further
game execution for that block, and keep the next commitment block unavailable
until a declared publication delay has passed. It can still admit a valid
outer publication transaction carrying a rejected inner game call. It can
bind authorizations to actual physical attempts and accepted commitments,
and keep deposits locked until the specified evidence period ends.

These choices do not guarantee delivery. A timing proof must state exactly
which broadcasts have a bounded inclusion guarantee, from which point that
bound starts, and whether replacement, fee insufficiency, nonce conflicts or
expiry can remove the message from that guarantee. Mere private receipt by
one peer does not imply durable admission to such a service.

## What remains valid without public sender turns

The contract-delay calculation only needs a bound on recording the relevant
already-submitted openings. It does not need a public order of senders.
The current counted-reference proof can use a ledger archive at commitment
sites when this publication condition is derived.

The [native readback](se-publication-native-adapter.md) reconstructs the
current ordered pending list from the complete-observation reference player's
own successive observations, outputs and ledger. It does not reconstruct
other players' sending opportunities. That is enough for the current
stateless pending-reception API.

The distinction between current-phase actions and fresh historical messages
also remains useful. A discarded attempt cannot authorize a reveal phase
that never existed. An excluded owner's base utility remains fixed, so
nonnegative penalties can only lower it. The generic mixed enforcement
comparison can use that direct bound without making its private disclosure
common knowledge. These facts do not by themselves prove the complete
asynchronous compiler theorem.

## The information and audit obligations

Visible retransmissions can expose delivery opportunities or operational
history absent from the old reference information. A public-calendar replay
proof cannot be transplanted. Possible routes are to derive a suitable
causal observation model from the actual asynchronous transcript, or to
strengthen the internal reference game's past observations and prove its
local comparisons anew. Giving reference players more information does not
automatically preserve its sequential equilibrium.

Audit delivery is separate from publication of properly submitted transactions.
Signed evidence privately visible to a player may never reach the ledger.
A positive result must implement its evidence collection or retain a precise
conditional-coverage assumption. It must not infer complete collection from
the existence of an audit contract.

The open construction therefore has three distinct tasks: derive the contract
publication invariant from an explicit asynchronous inclusion contract; prove
the prescribed beliefs and every local deviation comparison under actual
private observations; and supply an authentic, funded audit with the coverage
used by the raw-action extension. Contract-controlled padding is available.
Public sender turns and automatic queue clearing are not supplied by padding.

## Publication from an individual transaction bound

The [publication derivation](se-asynchronous-publication-contract.md) uses a
precise and narrower hypothesis: a qualifying entry admitted at time a is
recorded by a+Delta, including when its inner call has expired. If a reveal
phase closes at public time c, every retained current-phase opening has a<=c.
A contract that enables the next commitment only after the recording watermark
c+Delta therefore has

    recordedAt(opening) <= a+Delta <= c+Delta.

No sender order or batch-clearing premise occurs in this proof. Players may
send arbitrarily near c. Such a message may miss its game deadline and cause
failure; the bound only says its contents are public before the next binding.
The next event's own deadline starts when that event becomes ready.

The distinction between admission and a player's attempted broadcast is
substantive. If replacing or cancelling the outer transaction removes the
publication guarantee, the theorem does not cover that original entry.
The compiler can make a stale inner action recordable, but must not silently
turn every private leak into an admitted transaction.

## What the probability proof can reuse

The [reference-information derivation](se-asynchronous-reference-information.md)
gives two finite arguments, using the existing proof's stronger intermediate
identities.

First, the source–mechanics factorization is pointwise in the mechanical
history and service seed. Filtering those indices by a past operational
signal preserves the source factor: in

    A(k,g,a) = c(k) d(g,a),

summing over the indices with a chosen signal changes only c. Second, the
bad-preparation history repair preserves the network, receipts and service
history. It can therefore bound bad preparation inside each refined
information set, rather than incorrectly importing a coarse conditional
bound. The corresponding waiting comparisons survive refinement when they
hold for every fixed service seed.

This is a proof-only refinement. The implementation strategy must ignore the
added signal at every perturbation index. An auxiliary observation process
then generates the player's actual private transcript. Hidden elapsed service
flags require joint histories with the latent seed; conditioning must update
that seed's posterior. Actual players receive neither the seed nor the foreign
callback history.

These arguments retain the service hypotheses of the fixed-seed comparisons.
They do not prove that every bounded-inclusion service satisfies them.

## Bounded inclusion leaves a timing question

Suppose inclusion before time 10 pays 1 and failure pays 0. A service may include
a first submission at time 8 at time 11, but a first submission at time 9
immediately. Both satisfy Delta=3. Waiting at time 8 is then better than sending.
This remains a possible off-path history even when the player could have sent
much earlier and guaranteed success.

Thus one cannot retain the old prompt-send policy merely because a new service
has a bounded delay. Revealing a hidden past service signal only in the proof
can also invalidate a copied policy's incentive bounds. The detailed note
gives an example where every policy ignoring that signal has positive regret
at some refined site.

Neither example refutes concurrent preservation. A different policy using
only the player's actual information may handle late opportunities correctly.
What remains is to derive its source-game comparison and its common
consistency sequence, including rollback and other players' failures.

There is a proved conditional alternative to prompt sending. The
[optimal-timing analysis](se-asynchronous-timing-policy.md) considers a
completion process whose success probability is independent of the semantic
action and hidden source payoff, whose successful continuation is the source
continuation, and whose failure gives the acting player its floor F. Then

    implemented value = F + successProbability * (source value - F).

An optimal timing policy using actual private observations maximizes success
probability. Because every source payoff is at least F, the same timing policy
works for every source-optimal action and preserves ties. The finite dynamic
proof supplies a common fully mixed consistency sequence and vanishing local
gain bounds. Exact initialized-law preservation additionally needs attainable
certain success at fresh stages.

The missing step is deriving those hypotheses for concurrent recovery:
foreign failures can change a survivor's continuation rather than give it F,
and delivery may select source states or affect other players' behavior.
The timing theorem addresses that explicit class, not every bounded service.

A correct opening also satisfies a weaker **success-or-exit** invariant:
after its reveal event completes, either its owner survived and the unique
accepted value is public, or the owner's base payoff is permanently fixed.
This does not require publication of every rejected or replaced transaction.
It is worth exploiting, but it does not settle the survivors' choices. Their
payoffs can still depend on a failed owner's privately leaked value. The
existing full-archive source construction may prescribe different actions
for those different private histories, so forgetting that archive requires
a new continuation argument.

The [first-quitter extension](se-quit-handler-preservation.md) suggests a
different proof organization: keep the intended game as the no-failure core
and complete post-exit play on the survivors' actual private information.
Its source-level theorem allows arbitrary bounded survivor continuations
when the first exiter's utility stays capped and a public marker separates
the continuation region. It does not require a common archive of failed
openings. The native bridge still has to handle disclosures and timing choices
before that public exit, including submissions that may succeed. Moving those
observations into a handler by definition would skip precisely that obligation.

## Evidence can travel separately from the original transaction

The [post-exit collateral analysis](se-post-exit-deterrence.md) shows that a
failed player can keep a refundable communication bond, separate from the
failure forfeiture. New provable misconduct can then incur an incremental
loss. If total continuation utility is already fixed, silence can instead be
selected as a weak best response; no assumption that failed players cannot
send is necessary. A reserve already certain to be lost supplies no further
strict deterrence. Qualifying messages sent before exit are handled by the
publication delay proved above: they are public before the next binding,
even if received after failure. The bond addresses additional misconduct;
consistent off-path beliefs and operational incentive comparisons remain
separate proof obligations.

The [audit analysis](se-asynchronous-audit-feasibility.md) distinguishes a
signed application message from the outer transaction carrying it. A recipient
can report the former using its own nonce and funding even if the sender
replaces the latter. This is compatible with asynchronous submissions.

Collection still needs someone to possess the relevant authenticated data
and a report-delivery guarantee. A private hint may reveal a value without
providing evidence attributable to its sender. A reward cannot reconstruct
missing signatures or force a privately informed builder to report.

One useful conditional deterrence lemma avoids requiring that every attempted
message be seen. Couple a deviation to a legal retained policy so their base
payoffs agree until an effective departure E. If its gain on E is at most G
and the expected audit charge is at least beta*Pr(E), then

    expected net gain <= (G - deposit*beta) Pr(E).

This includes rare disclosure events without a lower bound on their
probability. Its premise must cover every strategic effect: queue disruption,
builder reactions and unsigned hints cannot be omitted from E.

There is a genuine impossibility result for a broader communication model:
if a player can privately disclose a verifiable hidden value, profit from the
recipient's forced best response, and leave no distinguishable misconduct
evidence, a sound audit cannot preserve every source SE. The audit note gives
a two-player guessing game proving this. It is a boundary on unauditable
communication, not a counterexample to the current compiler or to concurrency
itself. An implementation must say which disclosures its observation and
authentication model includes.

## Scope of the remaining problem

| Obligation | What is established | What is still needed |
| --- | --- | --- |
| Publication before another semantic binding | Public cooldown plus an individual finalized-recording bound | A precise transaction class with that bound, or a proof requiring less publication |
| Private reception without public sender turns | Ordered own-recall reconstruction; finite filtering and conditional repair arguments | The actual backend's observation and service adapters |
| Visible retransmission | A causal simulation when erasure preserves service and payoffs | Control of propagation, capacity, fee and builder effects |
| Late timing choices | Optimal actual-information timing for a separable success/floor process; failure of unrestricted prompt-send dominance | Derive the comparison for foreign failures, rollback and actual service reactions |
| Raw deviations | Direct fixed-exit comparisons and conditional audit-deterrence lemmas | Authentic disclosure classification and implemented evidence collection |
| End-to-end SE and selected joint law | No capstone for the asynchronous target | One fixed finite implementation and one consistent sequence satisfying all the preceding obligations |

The intended concurrent implementation remains the target. The restricted
scheduled service is a benchmark for the mathematical components, not a
reason to change that target or an impossibility argument against it.
