# Audit feasibility with asynchronous private mempools

An asynchronous compiler can accept messages whenever their public prerequisites
hold. It need not allocate player turns or empty every pending queue between
decisions. The audit problem is then different from that of a registered
broadcast service: a privately received transaction may be replaced, dropped,
withheld or never become executable. A contract cannot infer its existence from
the eventual ledger.

The useful separation is between a signed **application message**, the outer
transaction carrying it, the recipients that retain a complete evidence witness,
and the later transaction that reports that witness. Reports can survive failure
of the original transaction. This supplies a practical audit route under explicit
observation and report-delivery conditions. It does not by itself prove that all
private disclosures meet those conditions.

The probability and incentive arguments below are hand derivations, not new
Lean results or a completed asynchronous SE capstone. There are no prescribed
sender turns, full-queue processing steps or invented block reservations in this
document.

## What ordinary transaction processing does and does not guarantee

Ethereum transactions carry a sender nonce and fee limits, and a proposer must
select a transaction for block inclusion. Submission is not inclusion.
[Ethereum's transaction documentation](https://ethereum.org/developers/docs/transactions)
describes these separate stages. Geth exposes configurable pool sizes, price
admission thresholds, replacement thresholds and queued-transaction lifetimes.
Those are local node policies, not a durable-publication service.
[Geth command-line options](https://geth.ethereum.org/docs/fundamentals/command-line-options)

There are three different notions of a duplicate:

| Object | Relevant identity | Consequence |
|---|---|---|
| Another reception of the same signed outer transaction | Transaction hash | A node already holding it need not allocate another pool entry. Its peer reception can still be observable. |
| A different outer transaction with the same sender/nonce | Different hash; competing nonce | It can replace the old transaction in a node's pool; both signed objects remain possible evidence. |
| A new transaction carrying an already known inner game message | New outer hash/nonce, same inner digest | It is another fee-paying transaction and can consume block capacity even if the contract treats the inner operation as idempotent. |

Geth's
[pinned transaction-admission implementation](https://github.com/ethereum/go-ethereum/blob/f8f9bc574459a1afefac7b63163739910ee0fe62/core/txpool/legacypool/legacypool.go#L659)
checks an existing hash and returns `ErrAlreadyKnown`;
its batch entry point filters known hashes before signature recovery and queue
promotion. Its replacement path separately tests the price bump and removes
the old hash.
This is a local, already-known-transaction fact. It does not suppress peer-level
receipts, prove zero network cost, forbid readmission after eviction, or make a
fresh outer wrapper consume no capacity. A second wrapper is attributable to its
actual signer; it is not automatically another signed instruction by the author
of the inner message.

Private delivery makes publication weaker, not stronger. Flashbots documents
private-transaction cancellation and a maximum inclusion block, and its example
explicitly allows a transaction to be dropped without inclusion.
[Private-transaction API](https://docs.flashbots.net/flashbots-protect/additional-documentation/eth-sendPrivateTransaction)
Protect also documents a policy of including only transactions whose execution
does not revert.
[Protect overview](https://docs.flashbots.net/flashbots-protect/overview)
Thus neither a valid signature nor a private relay acknowledgment proves that
the original bytes will eventually be public.

The implementation consequence is important: distinguish outer transaction
admission from inner game validation. A compiler can supply an inbox that records
a bounded signed inner message and returns successfully even when the game call
is stale or invalid. A failed low-level game call can be caught after recording.
This prevents *that contract's* rejection from deliberately discarding the
recorded message. It cannot make an underfunded, nonce-blocked, replaced or
censored outer transaction reach the contract.

### What fee funding buys

The fee market specifies a base fee, a priority fee and a maximum fee cap. The
base fee evolves from preceding block utilization. Funding a sufficient cap for
a finite window can remove fee-cap invalidity as a failure mode; it does not
force a proposer to include the transaction.
[EIP-1559](https://eips.ethereum.org/EIPS/eip-1559)

For a fixed finite K-block window, an implementation can compute a conservative
base-fee upper envelope from the protocol's exact integer recurrence and the
current public fee state. A simple bound from that recurrence is

    b_(t+1) <= (5/4)b_t+1,
    b_(t+K) <= (5/4)^K (b_t+4)-4.

Here the gas target is floor(gasLimit/2)>=1. Maximum utilization gives a
utilization excess at most target+1<=2*target, so the increment is at most b/4+1.
This deliberately loose bound accommodates integer rounding; it is not a claimed
typical fee-growth rate. Set the per-gas maximum fee to at least this base-fee
bound plus the chosen per-gas priority fee, and reserve the report's gas limit
times that maximum fee. This gives a finite *affordability* bound. It says nothing about nonce
availability, relay admission, builder selection or finality. A report liveness
assumption must address those separately.

## Make the signed message reportable independently of its transport

Use an application-level signature over a canonical, bounded structure:

    chain/domain, game/session, principal, physical attempt/event,
    kind, handle, typed payload, authorization/certificate references.

The domain includes the verifying contract and session. A message identifier
is its signed-content digest, independent of the outer transaction nonce and
fee fields. EIP-712 provides a standard typed encoding and domain separation,
but explicitly leaves replay protection to the application.
[EIP-712](https://eips.ethereum.org/EIPS/eip-712)

Expose a function such as `report(witness, beneficiary)` which verifies the
original application signatures and the objective violation. The reporter sends
this call using its own transaction nonce and fee funding. It need not execute
the original game action or consume the alleged offender's account nonce.
The authorization/relay separation is the same architectural distinction used
by meta-transactions, although an audit can verify the original signature
directly rather than trusting a forwarder.
[ERC-2771](https://eips.ethereum.org/EIPS/eip-2771)

Replacing or cancelling the offender's outer transaction then does not revoke a
copy of its signed application message already held by someone else. Changing
the current game phase also does not erase a signed conflicting pair. The
contract must retain the relevant public authorization records and must evaluate
misconduct against immutable message content, not against a mutable permission
which the offender can later repair.

Useful finite witnesses include:

* one properly attributable signed message with an intrinsic authorization,
  ownership, type or certificate defect;
* two distinct authenticated messages for the same prohibited event allowance;
* two authenticated bindings reusing a forbidden handle.

A non-inclusion claim, a claim about when somebody first heard a packet, or the
absence of another private message is not such a positive witness. A packet's
ordinary signature does not attest its sending time. Initial commitment
certification also does not substitute for a later reveal-phase authorization.

Application expiry must not erase evidence admissibility. It can prevent a late
game action while `report` continues to accept its authentic violation witness
until the audit deadline. Otherwise the offender could wait out the verifier.

## Complete evidence is different from an informative observation

For each allegation against player i, define a witness W as the complete bounded
data accepted by the deterministic verifier. A holder of only one member of a
conflicting pair does not yet hold W. Neither does a recipient of an informative
payload if the requisite sender authentication was removed.

This distinction occurs in real relay interfaces. Flashbots describes selectively
shared calldata and other hints; its `full` hint omits the transaction signature.
[Private-transaction privacy fields](https://docs.flashbots.net/flashbots-protect/additional-documentation/eth-sendPrivateTransaction#privacy-options)
If the calldata itself contains a complete inner application signature, that
particular problem disappears. The compiler must check the actual serialized
observation, not infer completeness from the word "full".

A leaked preimage can be highly informative without being a sound accusation
against a particular sender. Whether it alone proves misconduct depends on
exclusive-knowledge, authorization and public-timing facts. Correlated initial
information, legitimate earlier disclosure and forwarding can defeat an argument
that simply attributes any known preimage to its nominal owner. Conversely, a
specific cryptographic model may justify such attribution; it needs its own
proof rather than a general assertion that every informative hint is evidence.

### A precise honest-subset condition

Let H be a specified set of monitors who preserve received authentic data and
share witness fragments with one another. They need not receive everything.
For a first candidate violation at hidden history h and action a, let E_W be
the event that some monitor obtains a complete witness in time to report.
Require a conditional bound

    Pr(E_W | h,a, allowed continuation) >= alpha_i(h,a).

The deadline must include fragment propagation, verification, reporting,
inclusion and the required finality. "An honest node exists somewhere" gives no
positive alpha when the sender can deliver exclusively to a private corrupt
relay or an unmonitored recipient.

An example producer is random gossip sampling. Suppose a particular signed
message is sent to k uniformly sampled distinct peers from a fixed population
of N containing h honest monitors, with this conditional sampling law unaffected
by the source's private values or the sender's policy. Its probability of reaching
at least one monitor is

    q = 1 - choose(N-h,k)/choose(N,k).

This is an implication of that specified gossip experiment, not a property of
arbitrary private RPC submission. If a witness needs two messages and their
sampling experiments are independent conditional on the relevant history, both
reach the honest sharing set with probability q^2. Marginal bounds q alone give
only max(0,2q-1) by a union bound. They can give zero joint coverage when q<=1/2.
For example, Nature can reveal exactly one of the two messages to H and never
both. A reporting bounty cannot create the missing second message.

### The current coverage interface still needs a concrete witness adapter

The existing `Vegas.EventGraphRuntime.PhaseCount.Evidence` in
[PhaseCountMenu](../Vegas/Pending/PhaseCountMenu.lean) pairs the full signed
traffic list with an accused envelope. Its corresponding
`Vegas.EventGraphRuntime.PhaseCount.EvidenceCoverage` in
[PhaseCountCollection](../Vegas/Pending/PhaseCountCollection.lean) assumes
conditional observation and delivery of that evidence object. A recipient of
one leaked packet does not automatically possess it.

Portable signatures and report-all do not by themselves instantiate this
interface. The proposed positive singleton/pair/phase-certificate verifier
needs its own soundness proof and a first-departure argument showing that
the actual ledger and recipients collectively hold the needed witness.
Alternatively, a payoff comparison must show that the uncollected departure
cannot improve the deviator's payoff. This is a mathematical producer
obligation, not merely a different serialization of the existing evidence.

Even receiving complete envelopes is not sufficient without a restriction
on how reception is selected. The current
`Interaction.MessageNetwork.ObservationRule` in
[MessageNetwork](../Interaction/MessageNetwork.lean) selects identifiers as a
function of the entire pending list. For example, suppose innocent marker
packets x and y are both pending. A rule can reveal x when a hidden offending
packet contains bit zero and y when it contains bit one, while never
revealing the offending packet. The recipient learns the bit and possesses
only an innocent envelope. Report-all then supplies no evidence against the
hidden sender merely from that information gain.

This refutes an inference from arbitrary private reception to evidence
coverage, not SE preservation itself. A backend can restrict the observation
model and prove the appropriate evidence/effect relation, or supply
independent authenticated monitoring with its own justified coverage.
Neither the communication bond nor the publication lemma manufactures that
relation. The lemma still publishes all qualifying retained pre-closure
openings before the next binding, as already proved.

## A reporting-incentive theorem with explicit hypotheses

Freeze the base game outcome before the reporting stage. Messages remain
sendable at arbitrary opportunities allowed by the network; there are no
predetermined player turns. Fix a finite set J of eligible reporter identities.
An identity is not allowed to earn a reward for reporting itself. For every
offender i and reporter j in J with j!=i, reserve a separate entitlement B_ij.

The contract pays B_ij once for any valid witness against i submitted for j,
even if somebody else already reported i. Other reporters cannot exhaust this
entitlement. Copying j's signed claim preserves j as beneficiary; alternatively,
other registered reporters can claim their own separately reserved entitlements.
This avoids both a first-reporter race and theft of j's promised reward.
It uses a bounded registry: an unlimited fresh-identity reward would have an
unbounded funding requirement.

Suppose reporter j holds a complete verified witness and has not received its
entitlement. Assume:

1. It has a reporting policy with conditional success probability at least
   beta_ij>0 before the audit deadline, even given its entire information and
   the allowed behavior of other parties.
2. The total monetary cost on a successful report is at most c_ij. Unsuccessful
   attempts have no unreimbursed on-chain cost; any separate unavoidable
   broadcast/verification cost is at most c0_ij.
3. Reporting does not otherwise alter j's utility: the base outcome is frozen,
   its own audit liability and other entitlements are unaffected, and the
   reward is collectible from locked funding.
4. B_ij>=c_ij. All reporting costs are nonnegative.

Then the reporting policy has gain over never reporting at least

    beta_ij * (B_ij-c_ij) - c0_ij.

Proof: on successful collection its incremental net receipt is at least
B_ij-c_ij; on failure the assumed additional loss is at most c0_ij in total.
Average using the conditional success bound. In particular, with no upfront
cost, B_ij>c_ij and beta_ij>0 make nonreporting strictly inferior. The guarantee
is conditional on j's actual information, so it remains valid at a rare
off-path information set.

This proves existence of a profitable reporting policy, not that every later
time is as good as immediate reporting. A concrete client needs a policy that
meets the stated deadline and fee bound. No equilibrium can prescribe *never*
reporting at that information set when the strict inequality holds and the
comparison assumptions apply.

There is a useful quantitative strengthening. Put

    v_ij = beta_ij (B_ij-c_ij)-c0_ij > 0.

Any optimal reporting continuation must have conditional probability of
collecting this entitlement at least v_ij/B_ij. Its payoff gain is at most
B_ij times its collection probability, because costs are nonnegative; the
available policy gives gain at least v_ij. Thus even if an optimal reporter
chooses a different timing or fee policy, its collection probability cannot
drop below

    beta_ij (1-c_ij/B_ij)-c0_ij/B_ij.

This bound, rather than the candidate policy's beta_ij alone, is justified
for every optimal reporting continuation. With zero reporting costs it reduces
to beta_ij. For several interacting entitlements the payoff comparison must
isolate this claim, or bound the reporter's total changed rewards and costs;
the one-claim inequality cannot be applied independently without that fact.

The third assumption is essential. Freezing the base game does not automatically
make every player's remaining utility independent of its reporting decisions:
publishing evidence may expose its own violation, affect other claims, or enable
additional side payments. For an external monitor whose utility is only its
reserved reward minus costs, this condition has a direct implementation. For a
game participant it must be proved from the actual audit interface.

The offender alone is not a useful reporter. If its charge is D_i and its
self-report reward were B<D_i, self-reporting has net loss D_i-B. Excluding
self-rewards avoids a farming incentive, but it does not create a nonculprit
witness holder. The observation condition must require one.

### From witness acquisition to collection

Suppose E_W ensures some eligible nonculprit holder meeting the strict-reporting
hypotheses, and let b_i>0 be a uniform lower bound on its actual collection
probability, conditional on its information when the evidence becomes complete.
For an optimal reporter the preceding v_ij/B_ij estimate can supply b_i; for a
monitor with a guaranteed reporting policy its service bound can supply it.
Then

    Pr(charge_i=1 | h,a) >= b_i Pr(E_W | h,a).

For this conclusion the selection of a holder must respect the conditioning of
the bound. One sufficient producer designates a reporter from the public protocol
or the acquisition event and proves its bound conditional on that event and its
information. Another proves the collection bound at every complete underlying
evidence history, uniformly over the chosen holder. A lower bound conditioned
only on each holder's private information does not automatically survive a
hidden-state-dependent selection of the holder. Under either sufficient
condition, conditional expectation gives the displayed inequality; independence
among reporters is unnecessary. If Pr(E_W|h,a)>=alpha_i uniformly, the usual
alpha_i b_i bound follows.

This derives the observation/reporting split once the holder and network facts
are supplied. It does not infer an observation rate from a bounty. Nor does it
identify equilibrium reporting with an unconditional exogenous audit kernel
against arbitrary reporter policies: the reporting game must first be solved
or its eligible monitors modeled with their guaranteed policy.

## Inclusion assumptions for reports can be much narrower

The network need not include every attempted game message. It is enough for the
reporting proof that properly funded reports with complete witnesses have the
specified conditional delivery probability. A report uses an independent nonce
and cannot be cancelled by replacing the offender's transaction. Its verifier
must continue accepting a valid proof after another reporter has charged the
offender, so competition does not turn j's otherwise valid claim into a revert.

One possible finite liveness producer is the following explicit network model.
After a report has reached the relevant proposers and while it remains pending,
each successive block has conditional probability at least p>0 of including and
finalizing it by the agreed audit horizon. The bound holds conditional on every
previous failure and on the reporter's information. Then failure in K such
opportunities has probability at most (1-p)^K, by multiplying conditional failure
bounds, and

    beta >= 1-(1-p)^K.

Independence is unnecessary. The p assumption includes actual gas competition,
propagation, validity, censorship and finality; proposer honesty by itself does
not imply it. Neither the Geth nor Flashbots documentation supplies such a
uniform lower bound. Historical average inclusion rates also do not prove it
after conditioning on a private information set or an adversarially chosen
message. This is a candidate liveness contract to establish for a backend, not
an extra compiler theorem obtained by choosing a large gas limit.

Alternatively, a proved deterministic report-inclusion/finality bound gives
beta=1. That is stronger than ordinary transaction validity. Escrows must remain
locked through witness acquisition and that full report horizon; an indefinite
"eventually included" claim cannot justify a finite withdrawal deadline.

## Deterrence paid only when a deviation becomes effective

A uniform lower bound on witness exposure can sometimes be avoided. The
appropriate lemma couples the gain to the same event that makes evidence
available.

Fix a retained information set, an arbitrary belief on its histories, and a
deviating continuation. Construct a legal retained comparator on the same
probability space. Let E be a stopping event marking the first externally
effective departure. Suppose:

* on E's complement the two realized base payoffs agree;
* on E the deviator's base-payoff gain is at most G_i;
* the retained comparator is audit clean;
* the actual charge C_i is nonnegative, and
  E[C_i] >= beta_i Pr(E).

For a nonnegative deposit D_i, linearity and pointwise bounds give

    E[u_i^deviation-D_i C_i-u_i^comparator]
      <= G_i Pr(E)-D_i E[C_i]
      <= (G_i-D_i beta_i) Pr(E).

Thus D_i beta_i>=G_i deters the deviation without a positive lower bound on
Pr(E). No independence between payoff, exposure and reporting is used.
The argument applies conditionally at each information set; the comparator must
be one legal policy based on that player's information, not a different policy
chosen separately for each hidden state. Private shadow-memory simulation can
produce such a comparator only when its causal observation equations are proved.

For an evidence-carrying disclosure, E can be the first reception by a nonculprit
complete-witness holder, if the reporting theorem supplies its beta_i guarantee.
This is narrower and potentially more realistic than demanding that every
attempted packet eventually appear on chain.

### Exact ways the coupling can fail

E must include every payoff-relevant effect, not just receipt of a complete
message by a game player. The following are genuine missing cases:

* A builder reads an unrevealed message and changes ordering, inclusion or
  censorship. Other players observe the changed timing, while no eligible
  reporter receives the message.
* A private hint reveals the strategically relevant value without the required
  authentication or the other member of a conflicting pair.
* Repeated peer traffic changes propagation or queue latency even though the
  identical transaction hash does not acquire another local pool slot.
* A new outer wrapper carrying an old inner entry consumes capacity or fees.
  Application-level idempotence does not erase that physical effect.

In these cases a putative event E defined only by complete-witness receipt can
have probability zero while the base payoff changes. The first inequality in
the displayed proof is then false. One must either include that effect in a
detectable E, prove a service/coupling invariant making it irrelevant, or retain
it as an unresolved deviation. Local txpool deduplication is not that invariant.

## Bounty funding changes the utility comparison

For collateral that remains after exclusion, see the
[post-exit deterrence analysis](se-post-exit-deterrence.md).
Its comparison uses additional expected loss relative to silence. Reusing an
already-inevitable binary slash does not create an additional incentive, even
if the corresponding money remains locked.

If the original game players can earn reporting rewards, their raw utility is
not just base utility minus their own audit penalty. Let R_i^max bound all
incoming bounties player i can earn. The crude active-deviation upper bound is
then U_i+R_i^max; a sufficient collateral condition using uniform collection q_i
is

    q_i D_i >= U_i-L_i+R_i^max.

Outgoing report costs only lower this upper bound, but they matter for reporter
incentives and clean-path matching. All entitlements need separate, collectible
funding; counting a speculative future slash as already available is invalid.

For an excluded player, the previous direct comparison F_i-D_i C_i<=F_i can
fail after adding positive incoming bounties. A late disclosure may induce
another player's offense and create a reward. One cannot reuse that fixed-floor
argument while omitting the new payment stream.

There are two clean directions, with distinct obligations:

1. Use external registered monitors whose utilities and reward accounts are
   separate from the game's players. This avoids altering F_i and the original
   source payoff vector, but complete evidence must actually reach those
   monitors. Their mere existence supplies no coverage.
2. Sponsor all verified reporting costs and give game players no positive net
   reporting reward. In a terminal interface where reporting has no other
   effect on their own utility, report-all can be selected in a consistent
   equilibrium completion. This avoids incoming bounty gains. The following
   finite construction states the additional interface conditions precisely.

Disabling bounties only for excluded players also removes their strict reporting
incentive. It is not a free combination of the two arguments. Coalition resistance,
side payments, Sybil ownership of monitor accounts and unbounded verification
costs require their own model; the finite unilateral-SE argument does not settle
them implicitly.

### Zero-cost reporting with separate evidence streams

The following is an equilibrium construction, not a claim that arbitrary
reporters reveal everything. Fix a finite game ending in a frozen base outcome.
Each canonical signed application entry has exactly one author. Let K_j be the
finite set of complete entries known to player j; partial unauthenticated hints
are not entries. The report interface permits j to forward any subset of its
known entries authored by players other than j. Reports cost the game players
zero and earn them no reward. A separately typed report envelope is not itself
an application entry that can create a game-audit violation.

The terminal penalty against i is

    D_i * Bad_i(P_i, E_i),

where P_i is the fixed public evidence from gameplay and E_i is the set of
reported i-authored entries. The Boolean verifier uses only those entries and
fixed public facts. There must be no nested authentication loophole: if an
entry contains another author's signed application entry, that inner entry is
extracted and classified separately. A player cannot forward its own entry
inside an allegedly foreign wrapper. The signed grammar and public verifier
must make this decomposition unambiguous.

Require the following **evidence-stream noninterference** property from every
reporting prefix. If i varies its reporting continuation, and all other players
use the prescribed per-author report policy, the law of E_i is unchanged. A
direct sufficient implementation is a frozen-knowledge bundle stage: each j
submits its chosen foreign entries; the delivery law for i-authored entries
depends only on those entries and their relevant network randomness, not on
other entries included in bundles. All network/report opportunities can be
asynchronous. The property is about their effect, not a prescribed turn order.
For adaptive multihop forwarding, the knowledge updates, forwarding decisions
and delivery kernels must satisfy the same projection property for each author.

This property needs an actual producer. If adding another author's entries
enlarges a report's gas use, makes the whole bundle fail, changes other reports'
inclusion, or causes an observer to withhold already held i-authored evidence,
it can fail. Bounded input size makes the obligation finite; it does not prove
inclusion or eliminate competition. The simpler frozen-knowledge stage avoids
cross-author knowledge updates, but still needs the stated delivery condition.

**Reporting lemma.** Under this property, report-all is sequentially optimal
at every reporting information set, for every belief on that set. The base
outcome is frozen. Player i's reports contain no i-authored entries, and by
noninterference cannot change the law of the i-authored evidence delivered by
others. Its own penalty therefore has exactly the same conditional expectation
under every reporting continuation. No reward or cost remains. This proof is
pointwise in the underlying prefix before averaging, so it also covers reporting
histories that have zero probability in the proposed equilibrium.

A particularly transparent consistency sequence reports each available foreign
entry independently with probability 1-epsilon at each opportunity. Every
subset has positive probability for 0<epsilon<1. Use fresh coins separate for
each author, and require the per-author delivery and knowledge projections to
remain independent of other authors' report choices. Then the same
noninterference argument applies at each positive index. Copying a correlated
bundle policy that makes the treatment of one author depend on another author's
contents would not have this property.

Complete-witness acquisition at one reporter is unnecessary in this construction.
For a pair witness against i, one nonculprit may know its first signed entry and
another the second. Report-all allows the public verifier to combine them. The
relevant acquisition event is that

    P_i union union_(j != i) (K_j restricted to author i)

contains a valid witness, followed by delivery of the required entries. An
informative unsigned hint still does not contribute an authenticated entry.
For a finite witness requiring at most d fragments, a conditional failure bound
eta for each fragment gives delivery probability at least max(0,1-d*eta) by a
union bound. This requires each bound under the same relevant conditioning;
independence is not needed. If d=2 and delivery probabilities are merely
marginal beta, the guarantee is max(0,2*beta-1), not beta squared.

### Lifting an equilibrium through the reporting stage

Define the reduced pre-report game by replacing each terminal history with the
distribution of settlement produced by report-all and the specified reporting
network. This does not assume audit coverage against arbitrary withholding
profiles. Suppose this finite perfect-recall reduced game has an SE and a
fully mixed consistency sequence. Append the reporting stage to that same game;
copy the pre-report sequence and use the positive report-subset perturbations
above. The resulting sequence is fully mixed in one fixed finite extensive game.

There is a uniform error bound even if only the unperturbed report-all policy
has the required noninterference. Let K bound the total number of available
entry/report-opportunity pairs in any remaining reporting continuation,
including the current mixed subset choice when it is part of the comparison, and
let M bound absolute terminal utility, including deposits. Couple perturbed and
unperturbed reports with the same network randomness. Unless an inclusion coin
fails, both continuations agree. Fresh future coins fail with conditional
probability at most K*epsilon, from every history and under every belief.
Therefore either continuation value changes by at most 2*M*K*epsilon, and a
comparison of two actions changes by at most 4*M*K*epsilon. Earlier reporting
trembles cause no rare-event division: noninterference and the same bound are
required from the actual reached prefix, not only from a clean reporting start.

At pre-report information sets, future reports cannot change reach beliefs.
Their local gain inequalities converge to those of the reduced game. At report
information sets, report-all has zero gain from a unilateral change under the
unperturbed continuation, for every belief; the uniform error vanishes. Take a
subsequence of the finite Bayesian assessment space. The limit is a consistent,
sequentially rational assessment of the full game. Its joint base-outcome and
net-settlement law equals that of the reduced game, because its reporting policy
is exactly report-all.

This provides the common equilibrium completion needed for zero-cost reporting.
It does not prove that the reduced game's source-preserving SE exists. To obtain
that SE, derive collection or the exposure-weighted payoff comparison in the
reduced reporting kernel and apply an appropriate preservation argument there.
An existing theorem requiring collection against **all** raw future profiles
cannot be invoked directly on the full strategic-reporting game: withholding is
still a legal profile even though the constructed equilibrium does not use it.

## A sharp impossibility boundary

Suppose a private disclosure reaches no complete-witness holder who will report,
and the eventual auditor sees no information distinguishing it from a legal
retained execution. No sound audit can selectively penalize that disclosure.
Increasing the deposit does not change this indistinguishability.

There can also be no preserving SE. Nature chooses theta=0 with probability 2/3
and theta=1 with probability 1/3. A knows theta and holds a transferable,
unforgeable proof of its value; B does not. B chooses a guess and receives one
for correctness. A receives one if theta=1 and B guesses 1, and zero otherwise.
In the source A has no earlier message move; B uniquely guesses 0.

Add a private send of that proof before B's choice. Assume the proof can be
received without producing a collectable misconduct witness, and every resulting
public audit record also occurs in a source-legal execution with the same theta
and B's same action. Soundness on all retained legal histories forces zero charge
in those indistinguishable records. One concrete way to obtain that boundary is
for Nature to publish the same value proof after B's irrevocable choice, while
the auditor receives only terminal reports and no authenticated receipt time.
Holding the proof at reporting time then does not show that B held it earlier.
After receiving proof of theta=1, B's
consistent posterior is exactly one, so sequential rationality forces guess 1.
Any target SE preserving the source law would give A zero at theta=1, but sending
the proof yields one. Contradiction.

This refutes preservation for that larger private-communication model. It does
not establish a counterexample to the existing compiled runtime, and it does not
apply when receipt itself supplies a complete, attributable witness with an
incentivized and live reporting path. Those are precisely the facts a realistic
asynchronous audit theorem must establish.

## Bibliography keys

The corresponding entries are in `overleaf/vegas-paper.bib`.

| Source | Key |
| --- | --- |
| Typed application signatures and domain separation | `BloemenLogvinovEvans2017EIP712` |
| Base-fee recurrence and transaction fee fields | `ButerinEtAl2019EIP1559` |
| Separation of signer, relayer and recipient | `SandfordEtAl2020ERC2771` |
| Local pool admission and replacement options | `GethCommandLineOptions` |
| Pinned duplicate and replacement implementation | `GethLegacyPoolSource` |
| Private transaction expiry, cancellation and hints | `FlashbotsPrivateTransactionAPI` |
| Transaction submission and inclusion stages | `EthereumTransactionDocumentation` |
| Protect's execution policy | `FlashbotsProtectDocumentation` |

## The resulting division of responsibilities

| Compiler/contract can specify | Network or additional game model must establish |
|---|---|
| Domain-separated signed application messages and objective one/two-message witnesses | Who actually receives the complete signed evidence, possibly privately |
| Reports independent of offender nonce/replacement and mutable game-action expiry | Conditional delivery/finality for the reporter's funded transaction |
| Idempotent inner application, canonical entry identity and authenticated wrapper accountability | Effects of duplicate propagation and new wrappers on other transactions |
| Segregated escrow, bounded per-identity reward entitlements and exact payout accounting | Reporter incentives including all remaining utility effects and account ownership |
| A public audit/withdrawal deadline with verifier validity through that deadline | A sufficient witness-acquisition and report-delivery horizon |

The strongest conclusion supported here is a conditional asynchronous audit
construction and an exposure-weighted deterrence lemma. Neither universal
pre-receipt registration nor complete mempool observation is needed for those
lemmas. Full SE preservation remains contingent on the actual information and
service couplings, complete-witness acquisition, reporting incentives and the
network's report liveness; these cannot be inferred from a client transaction
pool or from collateral size alone.
