# Why the reactive service cannot preserve every source SPE

## Checked result

For the source game below and one legal instance of the reactive reserved
service, **no utility-independent translation of complete strategy profiles
preserves behavioral subgame perfection for all public-result utilities**.
The theorem allows arbitrary whole-profile translations, hence includes every
playerwise compiler. It covers both value-only and failure-admitting source
commitments.

This is a theorem about a particular game and service. It rules out a uniform
guarantee for the service class containing this instance. Other service
restrictions, utility-aware synthesis, and preservation of equilibrium outcome
sets have different proof obligations.

The example relies on observing delivery of an already-known packet and on
inclusion reacting to traffic using that delivery as a signal. It establishes
an obstruction for this permissive scheduler class. Applicability to a network
whose observations reveal only newly learned messages is a separate question.

The source program is an actual typed `SourceProgram`. Its two-event graph is
an explicit realization with a checked equality of publication kernels for
every binding and disclosure. The result does not identify that graph with
the compiler's unsimplified output.

## Source game and utilities

One player binds an integer and then chooses whether to disclose it. A
successful disclosure publishes the binding; withholding publishes failure.

| Public result | Utility `u` | Utility `v` |
|---|---:|---:|
| 0 | 3 | 3 |
| 1 | 2 | 1 |
| 2 | 1 | 2 |
| Any other result, failure, or no result | 0 | 0 |

The complete source strategy **bind 0; always disclose** is an SPE for both
utilities. Initially, 0 is best. After any binding, disclosure is at least as
good as withholding. This includes source histories off the strategy's path.

## A legal network continuation

Each activation permits one optional transmission. Submitting a commitment
fixes its meaning immediately. There is no separate preparation decision.
The reserved service gives each strategic event one owner activation and four
network opportunities before reserved inclusion. In this instance the network
uses those opportunities as follows:

| Step | Who acts | Effect |
|---|---|---|
| Reserved activation | Player | Submit envelope `m1`, binding 1 |
| First network opportunity | Network, then player | Activate the player; submit `m2`, binding 2 |
| **Subgame root** | | Both fixed commitments are pending |
| Second network opportunity | Network | Randomly deliver `m1` or `m2` to the player |
| Third network opportunity | Network, then player | Activate the player; optionally submit another packet |
| Fourth network opportunity | Network | Include `m1` or `m2` by the public rule below |
| Reserved inclusion | Service | Attempt the remaining matching commitment; it is too late |
| Disclosure visit | Service and player | Allow disclosure of the accepted commitment |

Let `b` say whether the delivered envelope was `m1`, and let `c` say whether the
third response submitted a fresh packet. The network includes `m1` when
`c = b`, and `m2` otherwise. This is a fixed rule about delivery and packet
traffic. It never reads private opening material or the utility function.

### What the delivery communicates

Alice already knows both envelopes, because she submitted them. Delivery
reveals no new message content. The current player view records the inbox
separately from own-action recall, so the identity of the returned envelope
reveals a scheduler choice. Its strategic significance comes from the
inclusion rule depending on the same choice. The construction thereby provides
a signaling channel between the scheduler and Alice.

The scheduler is a fixed randomized mechanism in this theorem. It has no
utility, strategic coordinate, or equilibrium condition. A miner modeled as a
player would require a different game and a fresh proper-subgame analysis.
Nevertheless, the fixed mechanism supplies coordination through observable
delivery and responsive inclusion. That capability requires justification for
the intended network abstraction.

If observations represent only which envelopes a player knows, receiving one's
own known envelope again should leave that observation unchanged. The recovery
strategies proved here distinguish precisely those deliveries, so the proof
does not apply to that observation model. Establishing an obstruction using
new information from another participant and a justified inclusion policy is
a separate obligation.

The root is reachable by legal actions from initialization. It is a **proper
subgame root** under the canonical information model: no future decision
information set crosses it. The proof considers every legal history and all
future decisions. The player remembers both initial submissions, distinguishing
this continuation from histories with different initial responses.

The root precedes an external random delivery. To choose the winning binding,
the next response uses the actually received envelope. The player has no
access to the scheduler's private state or pending pool. A response chosen
before delivery lacks this signal. Treating an entire contingent policy across
delivery as one action would change the equilibrium interface; it is not the
coalescing of uninterrupted private computation.
This distinction is conditional on the delivery event being a meaningful
observation of the intended runtime. The theorem does not justify exposing
that event merely because the execution model can record it.

## The contradiction

After the root, the network always accepts one of the two old commitments
before any further choice. A new commitment to 0 cannot win this inclusion.
All later traffic can produce only publication of 1, publication of 2, or
failure. Therefore every native policy, including every randomized policy,
satisfies

```text
expected u + expected v ≤ 3.
```

An information-local deviation can nevertheless obtain utility 2 under either
utility function:

- For `u`, submit a packet exactly when `b` is true, then open `m1`.
- For `v`, submit a packet exactly when `b` is false, then open `m2`.

The extra packet can itself be the eventual opening. It need not be a new
commitment or malformed value. The later disclosure visit supplies another
opening if needed. The proof follows the complete reserved service, including
expiry, and proves that a successful publication persists.

An SPE for both utilities would have to attain at least 2 under each, requiring
their sum to be at least 4. No native policy can do this. Yet the same complete
source policy is an SPE for both. A translation that receives that policy and
the game, but not the utility, must return the same native profile for both
tests. Hence it must fail one test.

## What causes the failure

The target admits a continuation with a restricted choice between two
previously submitted values. The source has a fresh binding choice, where 0
remains available, or a fixed binding awaiting disclosure. It has no matching
choice between 1 and 2. The source strategy consequently carries no answer to
which of those two values the player prefers.

Both initial commitments are valid and permanently binding. Allowing
intentional commitment failure in the source does not repair this example.
Likewise, free private computation and atomic submission are already present.
An SPE compiler needs a continuation contract that rules out such residual
menus, represents them in the source game, or obtains the additional utility
information needed to complete the target policy. None follows from the
initial public-outcome law alone.

## Proof map

| Obligation | Checked artifact |
|---|---|
| Initialized root and full information-set closure | [`root_isSubgameRoot`](../VegasTests/ReactiveMenus.lean) |
| Arbitrary future policies cannot exceed the sum bound | [`rounds_value_sum_le`](../VegasTests/ReactiveMenusLaw.lean) |
| Adaptive, information-local deviations attain 2 | [`recovery_rounds_value`](../VegasTests/ReactiveMenusStrategies.lean) |
| Canonical behavioral SPE contradiction | [`no_common_reactive_spe`](../VegasTests/ReactiveMenusSPE.lean) |
| Common source SPE and publication kernel equality | [`source_spe` and `source_graph_publication`](../VegasTests/PendingMenusSource.lean) |
| Impossibility for all utility-independent profile translations | [`VegasTests.ReactiveMenus.no_utility_independent_spe_compiler`](../VegasTests/ReactiveMenusSource.lean) |

The final theorem has a guarded axiom audit in [`Paper.lean`](../Paper.lean):
only `propext`, `Classical.choice`, and `Quot.sound` occur. No missing simulation
or equilibrium claim is assumed.
