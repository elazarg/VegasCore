# Inclusion rules and continuation preservation

## Result and scope

Competing pending commitments do not, by themselves, prevent preservation of
optimal choices. There is a checked positive result for a useful class of
inclusion rules, and a checked SPE transfer theorem that permits lotteries
over source continuations. Neither yet establishes SPE preservation for the
complete reactive compiler.

The [reactive inclusion counterexample](reactive-inclusion-obstruction.md)
proves that unrestricted public scheduling prevents a uniform SPE theorem:
two public utilities share a source SPE but have no common target SPE for
one permitted scheduler. Its commitments are binding, responses are atomic,
and there are no leaks. The positive investigation therefore needs a stronger
service contract; the counterexample does not rule out such a contract.

The active runtime retains partial passive eavesdropping and the scheduler's
public-history memory. The selectors below are additional components
for investigating a preservation contract; the reserved service does not use
them automatically.

The [research note on inclusion assumptions](inclusion-assumptions.md) treats
neutral selection as an explicit hypothesis about service behavior, motivated
by miner incentives. It connects the mixture law to Luce's choice axiom,
explains fee-sensitive rules, and states the weaker local contract of
regularity. The local theorem, its converse, weighted selection, and finite
mixtures of stable priorities are checked. Their composition through the
reactive service remains open.

## The useful condition concerns choices, not memory

Fix a continuation with some already binding candidates. Write `nu` for the
law obtained by selecting among them. Suppose a fresh proposal `a` gives:

```text
include(a) = p * point(a) + (1 - p) * nu
```

Both `p` and `nu` must be the same for every fresh proposal being compared.
Silence leaves `nu` unchanged. Replay must either have the effect of one of
these proposals or leave `nu` unchanged. Forgetting past scheduler commands
does not imply this equation.

Let `V(a)` be expected utility from continuing after `a` is selected. If a
source policy `sigma` is optimal for this continuation, then:

```text
E[V(include(sigma))] - E[V(include(a))]
  = p * (E[V(sigma)] - V(a)) >= 0.
```

Silence is also no better: every retained candidate is a legal source action,
so `E[V(nu)] <= E[V(sigma)]`. Taking mixtures covers arbitrary randomized
responses, including when `p` is zero or one. No ranking of old candidates
needs to be extracted from the source strategy.

[`PendingChoice.optimal_response`](../GameTheoryExtensions/Core/PendingChoice.lean)
proves this for arbitrary action and outcome types, retained and prescribed
finite distributions, and a stochastic continuation kernel.
[`PendingChoice.nash_preserved`](../GameTheoryExtensions/Core/PendingChoice.lean)
uses the canonical Nash predicate for the one-player response game. The
continuation kernel is fixed across the compared proposals. Matching that
kernel to actual later play is a separate obligation.

## The more general local contract

Preserving relative odds is sufficient but stronger than needed locally.
`RegularSelection` permits any selection law in which insertion weakly
decreases each retained action's probability. The selection law is fixed
across the fresh source values compared. Under the same fixed-continuation
premise, [`RegularSelection.optimal_response`](../GameTheoryExtensions/Core/RegularChoice.lean)
proves that submitting an optimal source lottery dominates silence and every
randomized optional proposal. Supported recovery choices satisfy the same
inequality. The compiler instantiation is
[`reactiveRecoveryLaw_regular_optimal`](../Vegas/Pending/ReactiveRegularity.lean).

[`regularAt_iff_expect_le`](../GameTheoryExtensions/Math/Probability/Regularity.lean)
also proves the converse: regularity is exactly what improves every utility
maximized at the fresh outcome. This is a characterization of the local
comparison, not of full SPE preservation. All three statements concern finite
distributions and fix the downstream continuation.

### An exact law, not only an incentive inequality

Regularity also supplies an exact simulation with fixed branch weights.
Write `q(a)` for the old selection probability, `r(a)` for its probability
after insertion, and `p` for the fresh candidate's probability. There is a
lottery `d` over old actions such that:

```text
q = sum_a r(a) * point(a) + p * d.
```

When `p > 0`, `d(a) = (q(a) - r(a)) / p`: it is the distribution of the
displaced probability mass. When `p = 0`, its choice is immaterial.
[`regular_option_restore`](../GameTheoryExtensions/Math/Probability/RegularCoupling.lean)
proves existence, including this degenerate case.

Use the post-insertion selection lottery as the common branching law. At an
old branch, continue with that old action. At the fresh branch, submitting
`a` translates to `point(a)` and silence translates to `d`. The branch law
is unchanged by the response. This gives equality of action distributions
for every randomized optional response, and equality after any common
continuation kernel:
[`RegularSelection.responseLaw_factor` and `RegularSelection.continuationLaw_factor`](../GameTheoryExtensions/Core/RegularChoiceSimulation.lean).
The translation does not use utilities or inspect future chance.

This resolves the local law needed for a source-root mixture even when
regularity changes relative old odds. It does not identify those branches
with proper source roots or establish the common downstream kernel.

## Concrete selectors over the existing message network

[`Interaction/PendingSelection.lean`](../Interaction/PendingSelection.lean)
filters pending packets by an eligibility predicate, forms the finite set of
their identifiers, and samples uniformly from that set. It returns no
identifier if the set is empty. Eligibility can identify one owner and event.

For `n > 0` retained distinct eligible identifiers, appending one fresh
eligible identifier gives exactly:

```text
new selection = 1/(n+1) * point(fresh) + n/(n+1) * old selection.
```

[`uniformPending_append_fresh`](../Interaction/PendingSelection.lean) proves
equality of distributions before decoding commitment meanings. The runtime's
binding invariant is needed to justify retaining the same decoding of old
identifiers across later operations.

[`uniformPending_replay`](../Interaction/PendingSelection.lean) proves that
the actual `MessageNetwork.replay` operation leaves this selector's law
unchanged when the replayed envelope is already pending. Packets remain
available for observation and rebroadcast; transport multiplicity does not
give them more inclusion weight. Reintroducing an absent envelope is a
different case. Passive learning also leaves the selector's law unchanged.

[`PendingWeighted.lean`](../Interaction/PendingWeighted.lean) implements
weighted selection satisfying the same equation: retain each old candidate's
weight and give the fresh identifier a weight independent of its proposed
action. Its weight divided by total weight is `p`.
`weightedPending_append_fresh` proves the exact equation, and
`weightedPending_one` proves equality with the uniform selector.

[`PendingPriority.lean`](../Interaction/PendingPriority.lean) implements
selection using a finite distribution over stable total priority orders.
Insertion either preserves a ranking's previous winner or selects the new
candidate; `priorityPending_append_regular` proves regularity of the resulting
law. The distribution over rankings is held fixed across compared responses.
Already pending replay and passive learning leave the selector law unchanged.

Randomized stable priorities need not preserve relative old odds. The two
rankings A/C/B and C/B/A, equally likely, select A/B before inserting C and
A/C afterward. The exact laws, regularity, and impossibility of expressing
this as a fixed mixture with the old law are proved in
[`RegularChoice.lean`](../GameTheoryExtensionsTests/RegularChoice.lean).
Eligibility, priorities, weights, and continuation behavior remain explicit
premises across the compared responses.

### Covering every replay requires candidate retention

[`MessageNetwork.RetainsEligible`](../Interaction/PendingSelection.lean)
states that every eligible envelope any player knows how to rebroadcast
already has a pending candidate identifier. Its `replay_ids` theorem proves
that **every** raw replay preserves the eligible menu, including unknown
identifiers and ineligible envelopes. The `*_replay_of_retained` theorems in
the three selector modules then prove equality of selection laws.

This is an explicit service obligation. The primitive network does not
guarantee it: included envelopes are removed from pending but remain known.
[`PendingPriority.lean`](../InteractionTests/PendingPriority.lean) checks the
following sequence with fixed priorities ordered by increasing identifier:

1. Submit envelope 0 and include it, removing it from pending.
2. Submit envelope 1; it is now the only pending candidate and wins selection.
3. A fresh envelope 2 still loses to envelope 1, whatever its payload.
4. Replaying envelope 0 restores its priority and changes the winner to 0.

`not_retained`, `old_selection`, `fresh_selection`, and `replay_selection`
prove these facts using actual network operations. The priority rule satisfies
regularity throughout; the replay has transport attributes unavailable to the
fresh submission. This is a network selection example, not an application
execution or native SPE counterexample.

The active reactive service uses **at-most-once inclusion**, including for
rejected application calls. A second request to include a published identifier
becomes a wait; reserved selection skips such identifiers. Rebroadcasting
remains legal, and a retry may submit the same payload in a fresh envelope.

[`interaction_history_publishedOnce`](../Vegas/Pending/ReactiveServicePublication.lean)
proves that published identifiers are distinct at every legal initialized
service history. It covers arbitrary player responses and network policies,
including histories outside prescribed play. No acceptance test is needed
before consuming an identifier; premature calls can be rejected immediately.

The general carrier separately preserves the fact that every known envelope
is pending or published.
[`replay_unpublished_history`](../Interaction/ReactivePublication.lean)
therefore proves that every raw replay leaves the eligible menu unchanged
when eligibility excludes published identifiers. The removed-envelope
regression above uses an eligibility predicate that does not exclude them.
Equality of menus does not make the broadcast unobservable or settle the
effect of later responses. The active service's latest-pending selection and
arbitrary intervening network policy still need stronger selection premises
for the regularity argument.

## Why a memoryless scheduler is not enough

Consider old identifiers binding values `1` and `2`, with weight five each.
The next fresh identifier has weight one, independently of its value. For
utilities `(3,2,1)` and `(3,1,2)` on `(0,1,2)`, zero is optimal for both.

| Rule | Submit zero: both utilities | Replay preferred old identifier | Common optimal response |
|---|---:|---:|---|
| Uniform over distinct identifiers | 2 | 3/2 | Submit zero |
| Fixed weights over distinct identifiers | 18/11 | 3/2 | Submit zero |
| Fixed weights over transport copies | 18/11 | 5/3 | None |

In the last row, replay adds a copy of weight five, giving the preferred old
value probability `2/3`. The selector reads only the current pool, without
scheduler history or private observation records.

[`no_common_weighted_replay_response`](../GameTheoryExtensionsTests/PendingChoice.lean)
also excludes a common randomized optimum: each utility can attain `5/3`,
but their sum is at most `36/11` for every response law, less than `10/3`.
This is a local continuation-game obstruction, **not** a proper-root witness
or a native SPE impossibility theorem.

Run `python scripts/experiments/pending_selection.py` for exact comparisons of
six selectors, nine retained-value pairs, and 216 utility vectors per pair.
First identifier, latest identifier, uniform identifiers, uniform copies,
and fixed weighted identifiers preserve a source-optimal submission in all
these cases. Weighted copies fail in 996 of 1944 cases. The sweep does not
prove a general theorem; the Lean result supplies the positive statement
under its explicit mixture hypothesis.

## How this can feed an SPE proof

An unresolved lottery may correspond to an old commitment having taken effect
in some branches and a fresh source decision in another. Requiring a single
matching source history would unnecessarily exclude such a correspondence.

[`isBehavioralSubgamePerfect_of_root_mixture_laws`](../GameTheoryExtensions/Protocol/BehavioralContinuation.lean)
proves preservation using a finite law over **proper source roots**. At every
proper target root `k`, the certificate fixes `mu` before choosing a deviator:

```text
honestTarget(k) = sum_h mu(h) * honestSource(h)
deviatedTarget(k, i, tau)
  = sum_h mu(h) * sum_rho Q(h, i, tau)(rho) * source(h, sigma[i := rho]).
```

Both laws use the same root weights and unchanged source opponents. Each
replacement is a whole information-local policy; it cannot inspect future
chance. Averaging source SPE inequalities proves the target inequalities.
The compiler is one global playerwise function, independent of utilities.

The inclusion equation is only an ingredient in this certificate. The
remaining native obligations are:

1. **Recovery.** The [recovery compiler](reactive-recovery.md) submits again
   after unsupported earlier responses, reuses supported remembered choices,
   and reconstructs intentions from actual completions and accepted packets.
   Its initialized state law and one-packet guarantee agree with prescribed
   play. Its recovery lottery satisfies the local optimal-response theorem.
   Full source-observation correspondence and recovery optimality throughout
   the remaining reactive interaction are still open.
2. **Intervening responses.** The equation must cover the remaining interaction
   relevant to the abstract decision. A final uniform draw does not constrain
   earlier adaptive inclusion or new foreign transmissions. Passive leaks and
   reactions must be retained and simulated.
3. **Roots and information.** Each branch must match a proper source root,
   not just a compatible store. Hidden values, early disclosures, barriers,
   and arbitrary prior deviations matter. Do not obtain preservation by
   inserting irrelevant private tags that eliminate subgames.
4. **Failure and deadlines.** An unopenable binding is not a valid binding
   followed by an irrevocably fixed withholding decision. Explicit forfeiture
   admission, or a proved failure-elision criterion, is still needed. Recovery
   cannot reset deadlines.
5. **Initial correctness.** The compiler also needs its initialized
   public-outcome and deviation laws. The continuation certificate alone does
   not establish those laws.

Multiple candidates and uncertain inclusion are therefore insufficient reasons
to abandon preservation. Preservation through a constrained service remains
open; unrestricted public scheduling has the checked counterexample above.

## Relation to a blockchain runtime

Counting one candidate per distinct signed transaction is a plausible
abstraction: the Ethereum execution API recognizes already-known transactions.
This supports distinguishing duplicate broadcasts from distinct submissions.
[Ethereum transaction submission API](https://ethereum.github.io/execution-apis/api/methods/eth_sendRawTransaction/).

Ethereum's transaction nonce motivates consuming a published identifier once;
the same sender and nonce cannot be included twice.
[ERC-4337 nonce discussion](https://eips.ethereum.org/EIPS/eip-4337#semi-abstracted-nonce-support).
Our service abstracts this as a spent-identifier test. It does not model nonce
ordering, transaction replacement, fees, or chain reorganizations, and this
motivation is not a proof of an Ethereum implementation.

Uniform inclusion, stable priorities, or fixed action-independent weights remain explicit service
assumptions. They are not established by that interface. Geth documents
competing transactions for the same account and nonce, including different
gas allowances or transaction contents. Those replacement choices need their
own model and preservation argument.
[Geth transaction pool](https://geth.ethereum.org/docs/interacting-with-geth/rpc/ns-txpool).

The architectural boundary is a proved service/translation contract with
replay, eligibility, and continuation behavior specified. No source-language
flag named after scheduler memory is needed.
