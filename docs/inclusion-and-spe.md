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
public-history memory. The uniform selector below is an additional component
for investigating a preservation contract; the reserved service does not use
it automatically.

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

## A concrete selector over the existing message network

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

Weighted selection can satisfy the same equation: retain each old candidate's
weight and give the fresh identifier a weight independent of its proposed
action. Its weight divided by total weight is `p`. This algebra is covered by
the general mixture theorem; the concrete selector implemented here is
uniform. Eligibility, weights, and later scheduling must respect the same
condition across the compared responses.

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

Uniform inclusion or fixed action-independent weights remain explicit service
assumptions. They are not established by that interface. Geth documents
competing transactions for the same account and nonce, including different
gas allowances or transaction contents. Those replacement choices need their
own model and preservation argument.
[Geth transaction pool](https://geth.ethereum.org/docs/interacting-with-geth/rpc/ns-txpool).

The architectural boundary is a proved service/translation contract with
replay, eligibility, and continuation behavior specified. No source-language
flag named after scheduler memory is needed.
