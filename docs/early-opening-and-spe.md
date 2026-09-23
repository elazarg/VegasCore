# Early openings and honest SPE

## Checked result

**The current recovery compiler does not preserve SPE under uniform inclusion
and at-most-once publication alone.** A source policy that honestly binds zero
and opens is SPE. Its compiled graph policy has a strictly profitable native
deviation, at a proper subgame root, under the fixed schedule below.

The witnessing commitment is valid and binding from submission. The example
uses one player, no leaks, and no private preparation steps or computation
costs. It applies with either source commitment interface; admitting commitment
forfeiture does not remove this witness.

The principal theorem is
[`honest_source_spe_native_failure`](../VegasTests/ReactiveEarlyOpeningSPE.lean).
It pairs the source honesty and SPE proofs with failure of the actual
`compileReactivePolicy` on the corresponding bind-and-open graph policy.
[`source_graph_publication`](../VegasTests/PendingMenusSource.lean) identifies
the source and graph publication kernels for every binding and disclosure
choice. This is a graph-policy compiler counterexample, not an evaluation of
the entire `Setup.compileReactiveStrategy` pipeline.

## The source game

Alice binds an integer and then decides whether to disclose it. Her public
utility is:

| Published result | Utility |
|---|---:|
| `0` | 3 |
| `1` | 2 |
| `2` | 1 |
| Any other integer or failure | 0 |

The policy **bind `0`; always open** is honest and SPE. At the first decision,
zero earns the maximum possible utility. At every later source continuation,
opening weakly dominates withholding. This includes continuations following
other initial bindings. Both claims are proved, rather than assumed:
`source_honest` and `PendingMenus.source_spe`.

## The native prefix and service

Two earlier legal responses have left these envelopes pending:

| Identifier | Packet | Meaning |
|---|---|---|
| 0 | Commit `1` using handle A | A's immutable meaning is already `1` |
| 1 | Withhold at the disclosure event | If accepted, publish failure |

Neither envelope has been included. Withholding here is an explicit
application call that resolves the event as failure, as in the current
runtime. The example relies on that packet remaining available for inclusion.

The remaining service schedule is fixed:

1. Activate Alice once. She may submit or replay one envelope, or remain silent.
2. Uniformly select a distinct, unpublished envelope addressed to the binding event.
3. Grant the disclosure event.
4. Activate Alice once more.
5. Uniformly select a distinct, unpublished envelope addressed to the disclosure event.

The selection rule reads event addresses and the ledger. It does not inspect
hidden values, rank identifiers, remember private reads, or change activation
times in response to traffic. Publishing an identifier consumes its inclusion
opportunity even if the application rejects the call. Rebroadcast and fresh
submission are separate operations; fresh envelopes with equal payloads have
distinct identifiers.

This is the concrete bounded scheduler in
[`ReactiveEarlyOpening.lean`](../VegasTests/ReactiveEarlyOpening.lean).
`scheduler_atMostOnce` proves the contract for all its histories and views.
It is a particular reactive service instance, not the reserved-epoch service
and not a verified blockchain implementation. The schedule has no general
completion certificate against every policy. Both continuations used below
do publish a result on every branch, proved by
`compared_continuations_publish`; unfinished runs play no role in the payoff gap.

## What the compiler does

Alice's recall is inconsistent with the prescribed source policy, so the
compiler enters recovery. It uses the first remaining activation to submit a
fresh commitment to `0`, with handle B and envelope identifier 2.

At binding inclusion, envelopes 0 and 2 each have probability one half. The
compiler observes which binding actually took effect and, at the disclosure
activation, submits its correct opening as envelope 3.

At disclosure inclusion, the old withholding envelope 1 and the new opening
envelope 3 each have probability one half. Therefore:

| Public outcome | Probability | Contribution to expected utility |
|---|---:|---:|
| `0` | 1/4 | 3/4 |
| `1` | 1/4 | 2/4 |
| Failure | 1/2 | 0 |

The compiler's expected utility is **5/4**. These are executions of the
actual recovery compiler: `compiled_first`, `compiled_later`,
`compiled_publication`, and `compiled_value` prove the actions and laws.

## A better native continuation

At the first remaining activation, Alice instead submits an **early opening
of handle A**, as envelope 2. She already knows its value, `1`; nothing needs
to be guessed or assigned later. The packet waits until the disclosure event.

Only the original binding envelope addresses the binding event, so `1` takes
effect. At the later disclosure activation Alice follows the compiler again
and submits another correct opening in a fresh envelope, identifier 3.

Disclosure selection now has three distinct candidates:

| Identifier | Packet | Probability | Result |
|---|---|---:|---|
| 1 | Earlier withholding | 1/3 | Failure |
| 2 | Early opening of A | 1/3 | `1` |
| 3 | Later opening of A | 1/3 | `1` |

The expected utility is **4/3**, strictly greater than **5/4**.
`early_publication` and `early_value` prove the distribution and expectation.
The improvement uses a fresh submission, so deduplicating rebroadcasts or
enforcing at-most-once inclusion does not remove it.

## Why this is an SPE counterexample

The prefix is a legal history of the actual canonical reactive protocol.
[contested_isSubgameRoot](../VegasTests/ReactiveEarlyOpening.lean) proves
information-set closure. Alice remembers both
earlier actions; that recall identifies the deterministic prefix in every
future decision information set. The reusable argument is in
[`Interaction/ReactiveSubgamePrefix.lean`](../Interaction/ReactiveSubgamePrefix.lean).

`compiled_not_spe` applies the canonical behavioral SPE definition at this
root and uses the whole, information-local policy `earlyPolicy` as a unilateral
replacement. This root follows earlier deviations. SPE still requires
optimality there, even when the prescribed policy never reaches it.

The improvement compares public transmissions competing for later inclusion.
There is no cut inside a private computation or an atomic submission.

## What the local selection theorem leaves open

The [regular-selection theorem](inclusion-and-spe.md) holds the downstream
continuation kernel fixed. In this example, spending the first transmission
on an early opening changes the candidates available at the **later** event.
That continuation premise therefore needs an additional argument; regularity
within each individual event does not supply it.

The compiler faces a tradeoff between improving the binding's value and
improving the probability of successfully disclosing the existing value.
The checked witness establishes that its event-by-event recovery rule can
choose incorrectly. No claim about miner incentives is needed for this
calculation: the specified scheduler already selects uniformly.

## Design consequences and remaining questions

This refutes a preservation theorem for **this compiler under the stated
service assumptions**. It does not prove that every utility-independent
compiler fails for this uniform service, or that honest SPE is impossible
under every realistic service contract. The stronger impossibility for an
[unrestricted public scheduler](reactive-inclusion-obstruction.md) has a
different witness and must not be transferred to this case without a proof.

The next design investigation needs to address the tradeoff directly:

- **Transmission opportunities.** A service that permits useful submissions
  for several events before inclusion might avoid this particular competition.
  A finite batch or extra activations require a capacity argument at arbitrary
  legal roots; simply adding one more activation is not a proved solution.
- **Application treatment of failure and duplicates.** The witness uses an
  explicit, pending withholding call and two fresh opening envelopes. Changing
  either behavior changes the application/service contract and needs its own
  justification and proof. It is not implied by transaction replay protection.
- **Authorization after dependencies complete.** Requiring every executable
  packet to authenticate evidence unavailable before its predecessors complete
  would exclude the early packets in this witness. The
  [dependency-authorization note](dependency-authorized-submission.md) separates
  this proposed contract from ordinary timing checks and records possible
  blockchain mechanisms. It is not an implemented SPE result.
- **Recovery policy.** A different recovery rule could choose the early
  opening here. General utility-independent preservation would still need a
  proof across source games and utilities. This example does not prove such a
  rule exists or that it cannot exist.

Early submission and message observation remain legal. Removing capabilities
from native deviations solely to obtain a theorem would require a separate
modeling decision. There is no new source flag or restriction on raw responses
in this result.

## The witness with dependency-authorized inclusion

[ReactiveDependencyService.lean](../VegasTests/ReactiveDependencyService.lean)
uses the same activation times and raw response interface with a different
inclusion service. A public-history audit checks dependencies at each envelope's
original submission. Both premature disclosure packets remain pending but are
ineligible for the later draw; a fresh opening after binding is eligible.

The checked full-continuation comparison at the proper contested root is:

| Continuation | Uniform inclusion without authorization | Authorized uniform inclusion |
|---|---:|---:|
| Actual compiler recovery | 5/4 | 5/2 |
| Exhibited early-opening deviation | 4/3 | 2 |

Under authorization, the compiler publishes 0 or 1 with equal probability;
the deviation publishes 1. Both finish. This removes the exhibited profitable
deviation, without proving SPE against every replacement or at every root.
The [combined service design](reactive-spe-service.md) records the remaining
completion, information, recovery, and continuation obligations, and separates
the ideal public-history monitor from a concrete ledger certificate backend.
