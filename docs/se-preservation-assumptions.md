# Realistic assumptions for concurrent sequential-equilibrium preservation

Research status: delivery and failure-floor lemmas proved; conditional
one-block policy comparison reviewed; common consistent assessment and general
recovery composition open. No new Lean theorem, checklist closure, or runtime
change is claimed here.

The target is to implement each selected intended-game sequential equilibrium
with the same joint law of private inputs, public results, and net payoffs, and
without failures or charges on its paths. The
[reviewed timing obstruction](se-concurrent-timing-obstruction.md) rules out
doing this for every currently permitted callback service with any finite
penalties chosen before the service. It does not rule out all asynchronous
services, always-online networks, or additional service guarantees.

No weakest realistic assumption set has been established. Stronger privacy,
stronger delivery regularity, and restrictions on failure payoffs involve
different tradeoffs. The useful question is which concrete service can support
a complete preservation proof while retaining the intended game and
expel/restart settlement.

## What needs to be controlled

Waiting can change both what a player knows and what the other players do.
The relevant observations include arrivals, missing receipts, callback order,
readiness, and public failures, as well as pending-message contents. A guarantee
about pending-message visibility alone misses the receipt-timing signal used
by the obstruction.

For the present exact, finite-deadline target, a compliant response also needs
a guaranteed opportunity and admission. An ordinary unbounded-delay channel
gives honest submissions a positive chance of missing any finite deadline;
eventual delivery does not establish zero-failure implementation. Known bounds
and bounds that hold only after unknown stabilization are different service
assumptions. [Dwork, Lynch, and Stockmeyer](https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf)
make that timing distinction explicit.

Finally, all information comparisons must retain the original joint source
law. Private inputs cannot be drawn afresh at a retry. A retry can erase a
current binding without erasing its owner's memory or a signal another player
already received. Reveals must respect the intended game's information order.

## Candidate services

| Service guarantee | What it buys | Status and cost |
| --- | --- | --- |
| Fresh stationary delays, independent of the entire pre-send observation history; exogenous activations; protected prompt submissions | A fixed packet cannot arrive later merely because it was sent earlier | Delivery lemma proved; whole-game preservation open. Correlated congestion, previews of the unread delay, or builder choices outside this kernel violate the assumption. |
| Private collection until all current choices are irrevocably closed, including protection of timing and participation metadata | Removes the opportunity to learn from another player's submission before choosing one's own value | A credible architectural route; requires confidential intake, availability, and source-appropriate release. The complete compiler adapter remains open. |
| A uniform conditional bound relating useful delay benefits to irreversible loss | Allows a finite penalty chosen before the service to deter informative delay | A proof criterion until derived from a concrete service. A lower marginal late-delivery probability does not establish it. |

### Regular delivery without a penalty for every wait

Suppose a sole packet has a fresh delay D, with the same bounded distribution
at every feasible send time, independent of types, payloads, other packets,
and everything observed before sending. Couple an earlier send at s and a
later adaptive send at t >= s using the same D. Then

    s + D <= t + D.

Thus arrival before a fixed cutoff after the later send implies arrival before
that cutoff after the earlier send. A positive failure risk for every short
wait is unnecessary for this conclusion. Per-sender FIFO is weaker: it orders
packets within one execution, rather than comparing the first send in two
different executions.

The strategic proof needs more. A player may choose a different value after
waiting; earlier traffic may change opponents' behavior; and recovery may
change which packets remain eligible. The proposed proof uses source-faithful
pooled timing, opaque commitment blocks, and independence of foreign binding
service from the focal player's timing. On a clean block close, a late value
choice must correspond to an allowed randomized source deviation. On a foreign
commitment failure, recovery must remove the current choice's strategic effect,
including effects through remembered signals and later service. These are
whole-policy obligations, not consequences of the displayed inequality.

The reviewed conditional block comparison makes those extra obligations
explicit. Fix a full information set I in a private commitment block followed
by mandatory truthful publication. Compare prompt usable play with any
adaptive usable timing/value policy. Assume one common experiment supplies
the SAME foreign commitment-miss set J under both policies; the complete
mechanical transcript and qualification are source-neutral conditional on I;
and every foreign full input is preserved until clean close or a separately
controlled departure.

If J is empty, qualified play reflects an admissible source deviation bounded
by the source equilibrium value V_I. Otherwise, successful qualification reaches the same
memory-safe restart value W_J, independent of canceled choices. Put
X_empty = V_I and X_J = W_J otherwise. Let a_I be the permanent own-failure
payoff, with X_J >= a_I. A whole-event coupling must additionally give
p'_J <= p_J for delayed versus earliest qualification. Then

    E[u_delay | I] <= sum_J P(J | I) [p'_J X_J + (1-p'_J) a_I]
                  <= sum_J P(J | I) [p_J X_J + (1-p_J) a_I].

The final expression is the prescribed prompt continuation's value. These are
joint continuation hypotheses, not consequences of iid latency alone. A
common consistent assessment and general phase composition remain open.

### Private collection with a variable schedule

This route does not require an exact activation calendar. Players may receive
opportunities and submit concurrently in a variable order. The service needs:

1. A real opportunity and enough reserved service for a prompt valid submission
   to qualify.
2. Confidential collection: no foreign participation, timing, queue, receipt,
   or absence signal before current choices are locked, beyond information
   already allowed by the source. Own acknowledgments and activation times
   must not leak foreign arrivals through a shared queue.
3. A final admission boundary. Information released after that boundary cannot
   be used to submit or replace a choice in the closed attempt. Aborted-attempt
   secrets must also remain protected before replacement choices on retry.
4. Immutable qualification and audit records, with collectible liabilities
   where required and fresh service for surviving retries. Binding values roll
   back exactly as specified by recovery; openings are released only when the
   source permits them.

The eventual release format must also respect source information. Publishing
an arbitrary player-chosen tag after one block closes can signal private
information before a later source decision. Delaying that tag alone does not
establish whole-program information fidelity.

A public receipt cutoff is enforceable by an intake service; it does not prove
when a packet was sent. The guarantee must not silently assume authenticated
local send times. A trusted intake endpoint is one concrete trust model.
Distributed or cryptographic implementations need their own availability,
confidentiality, and completion argument.

For a one-block proof, protected prompt actions can form the prescribed
strategy. Late submissions that happen to qualify remain uncharged deviations;
they must be compared by source reflection, rather than declared audit
violations. Before the admission boundary their value and qualification must
depend only on the owner's source information and source-neutral mechanical
noise. Compliant foreign submissions must qualify against arbitrary focal
traffic. These conditions support the local comparison; their common-belief
and whole-program composition argument is still required.

Encrypting the payload of a public pending transaction does not provide this
interface. For example, [Shutter's documented use cases](https://docs.shutter.network/docs/protocol/api/use_cases)
allow observers to see that a trade is pending while hiding its details.
Timing and participation confidentiality are separate requirements.

### The information/risk relationship

The useful form is conditional on the player's complete information and covers
an entire adaptive delaying policy. Suppose a source-matched comparison gives

    expected gross benefit <= R q,
    expected additional irreversible loss >= L p,
    q <= c p.

Then the net gain is at most (R c - L) p, so L > R c makes policies with p > 0
strictly worse, and those with p = q = 0 weakly worse. Here q must bound every
benefit created by delay, including information, opponents' responses, and
recovery selection. The constants must
be uniform over permitted services if the penalty is chosen before the builder.
This is sufficient algebra, not a network theorem.

In particular, p cannot mean rejection of an original packet if a foreign
failure can restart the phase and rescue its author. It must represent an
additional permanent loss under the policy's actual continuation. Nor can q
mean merely seeing a pending packet: an informative missing receipt can suffice.
Harmless waiting can have q = p = 0.

One concrete way to verify such a ratio is to inspect each physical transition
before either a first extra-information exposure or a first irreversible loss.
If its conditional exposure probability is at most c times its conditional
loss probability, with mutually exclusive first-event outcomes, summing over
visited transitions gives the corresponding
whole-policy race bound. This requires an exposure definition that includes
informative silence and receipt order, and a source correspondence proving
that no gain is available before exposure. A controlled intake service could
enforce that interface; an ordinary public network does not supply it merely
by having random delays.

A stronger local condition is a positive permanent-exclusion probability eta
after a first deferral. If surviving payoffs lie in [m,M], exclusion pays a < m,
and immediate compliance survives, then deferral is inferior when

    m - a > ((1 - eta) / eta) (M - m).

Indeed, waiting has value at most (1 - eta) M + eta a, whereas the protected
compliant continuation has value at least m. The displayed inequality makes
the former strictly smaller.

Ordinary always-open bounded-delay networks generally have safe short waits,
so they do not supply this condition. Restricting future callbacks can supply
it, at the cost of an additional interaction restriction. It still does not
construct a complete sequential-equilibrium assessment.

## What existing results establish

Asynchrony itself does not preclude sequential-equilibrium implementation.
[Geffner and Halpern](https://arxiv.org/html/2309.14618v2), Theorem 2, implement
mediator equilibria using asynchronous communication when n > 4k. Their setting
uses authenticated private communication, eventual scheduling and delivery,
and underlying Bayesian or normal-form games. Their participant bound belongs
to that distributed implementation theorem; it is not a requirement for a
trusted intake service. Their result does not establish our finite-deadline,
arbitrary-program, expel/restart theorem.

[Halpern, Pass, and Seeman](https://arxiv.org/html/1506.03030), Theorem 4.6,
give computational sequential-equilibrium preservation for suitable
representations of extensive-form games. The relevant requirements include
implementing source strategies, simulating unilateral deviations, and
consistent beliefs. Its computational guarantee is different from our exact
unrestricted target, and scheduling turns and retries need a new correspondence
argument.

Generic secure computation also does not settle the equilibrium question.
[Hubacek, Nielsen, and Rosen](https://eprint.iacr.org/2013/499) exhibit two-player
mediated outcomes that cryptographic cheap talk cannot implement with their
sequential-rationality requirement. This does not refute funded private intake;
it shows why abort behavior and credible continuation incentives need explicit
proof.

## Next mathematical obligation

The candidate that most directly retains visible traffic is the regular
independent-service route. Its remaining task is one common consistent
assessment, with whole-policy source reflection through commitment retries and
reveals. The more direct service-design alternative is private collection
through the final admission boundary. Neither is yet a proved minimal
assumption set or a complete concurrent preservation theorem.

For a shared EVM mempool and shared block capacity, independent per-packet
service is a benchmark to justify, rather than a default network assumption.
Private intake with reserved capacity offers a more controllable interface,
at the cost of an explicit confidentiality and availability trust model.
Removing explicit failure bonuses is not an alternative proof: expelling a
competitor can itself change continuation payoffs. A common low abort payoff
would change settlement and still would not prevent extra information on
zero-failure paths.

No semantics alternative in this note is adopted. The
[asynchronous checklist](se-async-checklist.md) remains unchanged; mathematical
research does not close its checked-theorem obligations.
