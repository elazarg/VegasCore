# Realistic assumptions for concurrent sequential-equilibrium preservation

Research status: general information/audit bounds and concurrent preservation
under the explicit reserved-service, complete-observation assumptions are
mathematically reviewed. Ordinary-chain sufficiency and a general always-online
impossibility remain open. No new Lean theorem, checklist closure, or runtime
change is claimed here.

The [network-assumption survey](se-network-assumptions.md) classifies common
literature models and gives a delivery comparison allowing correlated delays
and unknown network parameters. Actual packet-delay independence is sufficient
for one comparison below, but is not necessary.

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

## What a general impossibility must establish

A timing channel can exist without being used in a preserving equilibrium.
Players may rationally use the same timing across private types. Showing that
one proposed implementation strategy leaks information therefore does not
show that every possible preserving equilibrium fails.

There is, however, a model-independent cheap-information obstruction. Fix the
source in which a receiver guesses a fair hidden bit b before observing any
signal about it. Its payoff is 1 for a correct guess and 0 otherwise, so every
source strategy has expected payoff 1/2. Runtime own failure pays -C, C >= 0.

Against any candidate preserving runtime equilibrium, suppose the receiver
has a feasible whole-policy deviation obtaining a signal Y before locking its
guess. Let

    delta = TV(Law(Y | b=0), Law(Y | b=1)),
    p = P(own permanent failure under the composed decoding policy).

The policy must have no additional fees, realize the guessing payoff when it
survives, and include valid completion. Its signal law is the original joint
law, not a law conditioned on surviving. A missing-signal symbol can complete
the definition on failed runs. Optimal binary decoding has correctness
probability (1 + delta)/2, and the actual payoff is at least

    1{correct} - (C + 1) 1{failure}.

Therefore its expected payoff is at least

    (1 + delta)/2 - (C + 1) p.

If delta > 2(C + 1)p against every candidate preserving equilibrium, none can
preserve the source payoff. No independence between failure, signal, and
correctness is assumed. A service family with an unbounded information-to-loss
ratio defeats every finite prechosen loss whenever these whole-policy and
equilibrium-uniform availability conditions hold. This is a necessary barrier
for the guessing source, not a sufficient characterization of preservation.

The demanding part is obtaining that signal against every relevant equilibrium.
A passive leak can supply it independently of sender choices. An optional
timing channel need not: opponents might pool. The
[reviewed callback obstruction](se-concurrent-timing-obstruction.md) instead
forces different timing choices because the sender's private type reverses
its preference over the receiver's failure. Its strict timing comparison holds
against every credible receiver continuation, including after a zero-probability
delay. The receiver then learns at small expected loss.

The same finite-game argument applies to any implementation supplying that
strict failure contrast, timely distinguishability, and a complete bound on
all other actions. These are substantial causal and incentive conditions.
They have not been derived for general always-online blockchains. In
particular, additional early submissions, late hidden submissions, and
relaying can restore pooling or make the signal arrive too late to exploit.

## When a larger audit deposit cannot help

There is also a general evidence limitation, separate from the existence of
an informative timing deviation. Let E be the COMPLETE input to a fixed audit
mechanism, and let g(E) be its expected nonnegative charge, bounded by K.
Let mu be an honest calibration law on which the audit charges zero, and nu
the evidence law of the complete decoding deviation against the actual foreign
continuation. Both use the same charge mechanism.

Zero honest expected charge implies g = 0 almost surely under mu. Therefore,
if nu is absolutely continuous with respect to mu, its expected charge is also
zero. In a finite model this means every evidence record the deviation can
produce also has positive probability under the zero-charge honest law.
No increase in K changes that conclusion.

In the finite-record model, let q be the probability under nu of evidence
outside the honest support. Then

    E_nu[g(E)] <= K q.

With own-failure payoff -C before audit and all other expected costs, excluding
those already counted in C or g(E), at most k, the cheap-information deviation
above has payoff at least

    1/2 + delta/2 - (C + 1)p - K q - k.

If the last four terms give a positive advantage against every candidate
preserving equilibrium, preservation is impossible. This bounds even the
strongest nonnegative charge mechanism with that honest calibration and budget,
not just the current count audit. It permits arbitrary dependence between
information, failure, and evidence.

The honest and deviating laws must describe the entire record, including
logical outputs, authenticated metadata, foreign traffic, and every other audit
input. Matching receipt times alone is insufficient. A randomized audit is
covered by using its common conditional expected-charge kernel. If a calibration
law mixes honest legal source choices, the mechanism must be sound for all of
those choices; soundness cannot simply be assumed for new records.

This gives a precise limit on pricing intentional delay. If its full evidence
is compatible with honest network delay, an audit that charges honest play
nothing cannot distinguish the two. Actual default risk, additional fees, or
trusted evidence can still provide deterrence. We have not proved that a
profitable, evidence-compatible timing policy is uniformly available in a
general blockchain; that remains a physical and game-theoretic obligation.

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
| Under one shared network experiment, an earlier first submission retains every admission opportunity of a later submission | Fixed-packet qualification dominance despite correlated delays and learning about them | Delivery lemma proved; shared reserved-capacity processing opportunities give a concrete class. Full-game coupling and consistency remain open. |
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
the SAME foreign commitment-miss set J under both policies; J, the complete
mechanical transcript, and qualification are JOINTLY source-neutral given I;
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

## Why the checked positive results work

Asynchrony, concurrency, and observable timing are separate properties. There
are two relevant positive constructions in the repository.

The [calendar construction](../Vegas/Game/SourceServiceCompilation.lean) uses
an explicit serial plan for activation, inclusion, expiry, and moving to the
next event. Its [roster scheduler](../Vegas/Game/ServiceRoster.lean) never
consults the network-policy argument it receives. Its success is therefore
not a theorem about an arbitrary synchronous network or public mempool.

The later [recovery preservation theorem](../Vegas/Game/RecoverySequentialCompilation.lean)
allows an arbitrary fixed stochastic scheduler, including adaptation to public
traffic, subject to its service guarantees. It is asynchronous, but its
[graph](../Vegas/Game/RevealService.lean) is globally sequentialized: at most
one event is ready. While Alice's current choice is unresolved, Bob cannot
make a later still-changeable conformant source move and time it to influence
her current delivery. Nonconforming raw traffic remains possible and is
handled by the authentic count audit.

That structural restriction is substantial. The theorem also assumes:

* Guaranteed reaction opportunities, protected sole-packet receipts, completion
  within a finite horizon, and reaction plus inclusion bounds strictly inside
  each deadline. These hold against modeled raw behavior, not merely on honest
  paths. Protected receipt is converted to acceptance by separate validity
  and timing proofs.
* Finite source/native representations, enough preparation slots, well-formed
  source behavior, and independence of each owner's hidden initial cells from
  all other initial cells. Later posteriors need not remain independent.
* Bounded utilities, an exclusion payoff no greater than every intended
  terminal payoff, and authentic evidence with conditional collection coverage
  and a sufficiently funded count-audit deposit.

The large audit deposit prices forbidden traffic; it is not a charge for every
WAIT. The theorem's exclusion-payoff comparison is weak and applies to intended
terminal readouts, not every arbitrary raw terminal. Full-input repairs, belief
transport, and rational late/free continuations are proved in the serial
construction. They are not supplied as an assumption that observations add no
knowledge.

The initial-private-input independence premise does not explain away the
concurrent obstruction: its single-owner hidden bit satisfies it. The crucial
new interaction is overlapping unresolved choices. Synchronizing clocks alone
does not remove that interaction.

These are checked abstract-runtime results, not certified deployments on
Ethereum. Known all-raw admission bounds, bounded-horizon completion, exact
information hiding, audit availability, fees, and finality each need a backend
justification. In particular, constant gas fees can preserve best responses
while changing the exact net-payoff vector; prefunding alone does not bridge
the payoff-law claim.

## The protected-service theorem and its deployment boundary

The [reserved-service proof](se-reserved-service-preservation.md) preserves
each selected source sequential equilibrium under an explicit concurrent
service class. It permits visible traffic and arbitrarily correlated delivery
uncertainty. Its hypotheses include protected per-coordinate capacity,
source-independent service frozen through each complete commitment/publication
block, nested admission opportunities, complete pending observation, adequate
fresh slots and a global exclusion-payoff floor. Payoffs are the existing
state-based source utility, exclusion settlement and count audit; deployment
fees need a separate accounting argument. The result is reviewed mathematics,
not a checked Lean theorem or a minimal assumption set.

Failed openings require explicit treatment. A raw value can be exposed while
pending even when its guard or delivery later fails and the original source
observation records only failure. The proof retains every truthful proposal in
an enriched auxiliary recovery game without changing the intended game or
expel/restart rules. Publication incentives use a pointwise timing comparison;
later choices use the actual enriched information. One normalized auxiliary
witness and one native Bayes sequence supply consistency across retries.
Ambiguous unusable-preparation/withholding histories are handled by an explicit
perturbation hierarchy and a bounded approximation error, not a blanket exact
posterior identity. Query matching or a one-block delivery comparison alone
would not establish this result.

The theorem does not establish preservation for arbitrary partial pending
leaks, ordinary shared-capacity chains, or additional timing-dependent payment
rules. Private collection through the final admission boundary remains another
service-design alternative, without a complete general preservation proof here.

For a shared EVM mempool and shared block capacity, independent per-packet
service is a benchmark to justify, rather than a default network assumption.
Exogenous shared processing with reserved capacity is another idealized
interface to justify; it is not supplied merely by consensus liveness.
Its capacity reservation is doing real work. In an ordinary FIFO queue,
Bob's earlier job can delay Alice past her deadline while Bob remains safe;
Bob's later job can leave Alice safe. Each owner's own packet may still arrive
no later when sent earlier. Thus monotone own delivery does not establish the
required comparison of foreign outcomes. The protected shared-opportunity
interface is not an established ordinary-chain fact.

Admission-controlled reservation is an established engineering architecture:
[RFC 2212](https://www.rfc-editor.org/rfc/rfc2212) specifies bounded-delay
service for policed traffic with reservations along the path. Its permitted
spare-capacity sharing does not itself establish our stronger counterfactual
coupling. Likewise, Ethereum's
[draft inclusion-list proposal](https://eips.ethereum.org/EIPS/eip-7805#core-properties)
explicitly permits omission when a block is full; it is not per-game reserved
admission. An engineered ingress/ledger layer could enforce stricter isolation,
but an ordinary contract cannot infer that guarantee from consensus liveness.

Private intake with reserved capacity offers a more controllable interface,
at the cost of an explicit confidentiality and availability trust model.
Removing explicit failure bonuses is not an alternative proof: expelling a
competitor can itself change continuation payoffs. A common low abort payoff
would change settlement and still would not prevent extra information on
zero-failure paths.

No semantics alternative in this note is adopted. The
[asynchronous checklist](se-async-checklist.md) remains unchanged; mathematical
research does not close its checked-theorem obligations.
