# Deriving abstraction requirements from restricted runtimes

## Method

Start from the current bounded native protocol. Disable one capability or
strengthen one operational restriction, then compare that restricted runtime
with the original runtime when the restriction is lifted. These comparisons
are candidates for adjacent abstraction steps. They are not additional
production semantics or a proposal to expose network operations in the source.

Each comparison fixes the game application, declared payoff, retained outcome,
and all runtime parameters except the named change. Any unavoidable induced
change must be stated: learning an envelope can also make forwarding or replay
possible, for example. An observation change cannot silently be advertised as
changing only beliefs while keeping all effective action capabilities fixed.

For each edge, seek:

1. An operational correspondence identifying exactly what the restriction
   removes and what restoring the feature adds.
2. A positive preservation theorem for a stated class of games, or a complete
   counterexample with an actual equilibrium in the restricted runtime.
3. A small causal or information condition explaining that result.
4. A requirement on any further abstraction retaining the same decisions,
   payoff and relevant behavior. An abstraction can instead exclude the
   witnessing games; that exclusion is part of the language boundary.

The terminal classifications and generic continuation theorems in
[the abstraction analysis](runtime-abstraction-classification.md) are proof
tools for these comparisons. Enumerating arbitrary quotients is a separate
question and is not the acceptance test for this investigation.

The [literature note](runtime-feature-literature.md) distinguishes established
results on optional disclosure and information expansions from the native
adapters still needed here. In particular, disclosure can be strategically
harmless even when its information would change another player's best response:
the sender's incentives to disclose also matter.

## First comparison: restore passive observation of pending packets

Use the existing selective-association native fixture. Both sides have:

- the same six-event compiled graph and initial state;
- the same signed integer payoff expressions;
- the same bounded raw submission and candidate alphabet;
- the same activation calendar, inclusion rule, deadlines and expiry actions;
- the same scheduler access to public traffic and its own command history.

Only the existing pending-observation parameter differs:

| Restricted runtime | Runtime with the feature restored |
| --- | --- |
| The observation rule always returns the empty set. | The existing rule lets Bob observe Alice's first pending envelope. |

The parameter is supplied directly to
[`EventGraphRuntime.reactiveApplication`](../Vegas/Pending/ReactiveRuntime.lean)
and its finite response adapter. The fixture is
[`SelectiveAssociationNative.lean`](../VegasTests/SelectiveAssociationNative.lean).
There is no need for a new application language or runtime state structure.

Passive observation is invisible to the scheduler at that activation, as proved
in [`ReactiveObservation.lean`](../Interaction/ReactiveObservation.lean).
Subsequent responses may differ and may then affect public state. Learning
also affects which known envelopes can be replayed and which evidence can be
forwarded. Those are consequences of restoring the capability, not additional
independently changed service rules.

### Checked operational comparison

[`SelectiveAssociationRestricted.lean`](../VegasTests/SelectiveAssociationRestricted.lean)
instantiates the empty observation rule on that same native fixture. It proves:

| Result | Scope |
| --- | --- |
| `two_rounds` and `bob_response_same` | Alice's certified pending packet gives Bob identical complete inputs for either bit. His arbitrary raw response therefore has a bit-independent law. |
| `first_response_guess_bound` | Any guess decoded from that response predicts Alice's fair bit with probability at most one half, including failure-valued reports. |
| `five_rounds` and `prefixPlayers_available` | The unchanged first five service instructions reach an accepted association using responses admitted by the full raw menu. |
| `association_input_hidden` | At those paired accepted-association prefixes, every non-Alice player's complete input, including recall, is identical across the two bit values. |
| `observation_feature_contrast` | Restoring the original observation rule supplies Bob with the certificate while it is still absent from the ledger. |

These are reachable prefix and response-law results. They do not prescribe or
justify equilibrium behavior in the remaining game. In particular, the
post-association equality is for the specified paired prefixes, not an
assertion that every full-runtime strategy keeps the bit secret.

### Exact equilibrium target and status

The candidate separating game is the existing declared-payoff game. The
restricted-runtime witness must give Alice expected payout zero.
**Existence of such an equilibrium in the native runtime
with the empty observation rule is open.** The current source equilibrium
proof uses a different communication interface and cannot fill this obligation.

For the runtime with passive observation enabled, the checked
[payout separation](../VegasTests/SelectiveAssociationPayoffSeparation.lean)
already proves that every sequentially rational assessment gives Alice
expected payout at least one half. Thus the missing restricted-runtime SE
would complete a comparison isolating one native parameter. Until it is proved,
the existing source/native theorem is not an isolated passive-observation result.

The restricted equilibrium needs consistent beliefs and rationality at every
legal information site, including deviations involving raw certificates,
replays, wrong addresses and failed openings. Matching the prescribed initial
outcome alone is insufficient.

The [candidate profile](../VegasTests/SelectiveAssociationRestrictedPolicy.lean)
uses silent preludes, a deterministic false binding for Alice, public-evidence
guesses, and ordinary openings. Every response is admitted by the unchanged
full raw menu, and the profile has some consistent belief completion. Neither
fact establishes optimality. The checked
[binding repair](../VegasTests/SelectiveAssociationRestrictedRealization.lean)
can realize either bit at every legal unfinished binding decision, including
after arbitrary prelude submissions, using the declared two candidate handles.
The [binding continuation theorem](../VegasTests/SelectiveAssociationRestrictedBinding.lean)
retains that chosen value throughout every subsequent raw-policy continuation.
The [opening optimality theorem](../VegasTests/SelectiveAssociationRestrictedOpeningOptimality.lean)
checks every legal opening information site against every complete behavioral
policy deviation, for any belief system. Other players' public results remain
fixed; the owner can publish its frozen successful value or incur failure.
Failed bindings are also covered. The
[initialized payoff law](../VegasTests/SelectiveAssociationRestrictedPrescribedOutcome.lean)
is a point mass at zero for Alice and one for each guesser. This is an execution
result for the candidate profile, not yet an equilibrium claim.

The [guessing incentive proof](../VegasTests/SelectiveAssociationRestrictedGuessOptimality.lean)
reduces whole-policy optimality to one precise posterior condition. When the
public view has no certificate for a successful true binding, its belief must
assign at least as much mass to Alice's successful false binding as to her
successful true binding. Alice's failed bindings contribute zero to both guesses.
A public true certificate instead determines the binding throughout the
information set. The proof permits arbitrary future policies and every raw
current response: reserved inclusion and timeout determine one binding result
throughout the information set, and later actions cannot replace it.

The probability calculation uses the actual native prefix law. The
[response factorization](../VegasTests/SelectiveAssociationRestrictedPrefix.lean)
and [history projection](../VegasTests/SelectiveAssociationRestrictedPrefixExecution.lean)
identify the original protocol's distributions before Carol's and Bob's guesses
with distributions over the three or four preceding responses. This avoids
requiring a bijection of full trace representations. A successful comparison
must still preserve the complete observed input, including the player's own
prior actions, and compare the exact probabilities of the response tuples.

The [candidate transformation](../VegasTests/SelectiveAssociationRestrictedSymmetry.lean)
flips a selected candidate's Boolean meaning while preserving the success or
failure of certificate requests. It permutes the raw menu, with equal uniform
weights whenever paired inputs have the same known message identifiers. The
[store transformation](../VegasTests/SelectiveAssociationRestrictedStoreSymmetry.lean)
handles accepted and rejected binding calls and binding expiry. The missing
concrete probability step is an injection from uncertified true-binding tuples
into false-binding tuples with the same guesser input and at least as much mass.
The fixed-depth Bayes formula and
[finite limit comparison](../GameTheoryExtensions/Math/Probability/ConditionalComparison.lean)
then transport that inequality to one common consistent assessment. An arbitrary
consistent completion of the profile does not establish the needed posterior
condition.

| Site | Proof status for the proposed profile |
| --- | --- |
| Alice's prelude and binding | Checked whole-policy optimality for arbitrary beliefs: both prescribed guesses stay equal under every complete Alice deviation, so her payout is at most zero; the prescribed continuation gives zero. |
| Bob's prelude | Checked whole-policy optimality for arbitrary beliefs: later correction and opening give the maximum payoff of one despite arbitrary earlier submissions. |
| Carol's and Bob's bindings | Checked whole-policy optimality conditional only on the stated posterior inequality. Its derivation from the common perturbation sequence remains open. |
| All three openings | Checked whole-policy optimality for arbitrary beliefs, including failed bindings. |

The [prelude proof](../VegasTests/SelectiveAssociationRestrictedPrelude.lean)
and the guessing and opening proofs use the same protocol and profile.
The [Alice proof](../VegasTests/SelectiveAssociationRestrictedAliceOptimality.lean)
checks the actual seven-step continuation between the guesses; Carol’s
prescribed commitment adds no certificate and cannot change Alice’s accepted
association. The sole substantive remaining obligation is the concrete prefix
probability comparison. The
[Bayes and common-limit adapter](../VegasTests/SelectiveAssociationRestrictedBeliefs.lean)
constructs one consistent assessment once that comparison is supplied. Thus the
restricted-native SE and isolated observation separation are still open.

An operational positive control is already checked: private observation cannot
change the scheduler's observation or its next choice after a silent response.
This isolates the additional information from direct scheduler coordination.
It is not an SE-preservation result for subsequent play. A separate candidate
positive edge would restore observations only after every action affecting the
retained payoff is irrevocable; its full continuation theorem is open.

## What a small pattern must retain

### A checked acquisition constraint

The existing packet-evidence interface admits an owner-or-copy condition:
a player can issue a certificate for its own fact, or copy a certificate from a
packet it already possesses. The actual native certificate issuer satisfies
that condition. The checked
[`foreign_known_observed`](../Interaction/ReactiveEvidenceOrigin.lean) theorem
says that a foreign certificate in any player's known packets must also occur
among that player's leaked packets or the ledger, at every initialized history.
Private output recall, arbitrarily long forwarding chains and replay cannot
create another acquisition channel.

Disabling passive observation removes the first alternative. Consequently,
[`foreign_certificate_published`](../Vegas/Pending/ReactiveEvidenceOrigin.lean)
proves that any possessed foreign native certificate must already occur in the
ledger. This is an ordering constraint on every legal prefix, independent of
strategies and of application acceptance. A rejected included call can still
publish its certificate.

The constraint concerns **carried certificates**, not all knowledge of their
values. An adaptive scheduler could encode pending contents through timing or
inclusion choices without delivering a certificate. The generic theorem allows
that; the fixed calendar and paired-input proofs above rule out that route for
the particular checked prefixes. Any stronger secrecy or causal-path theorem
must account for clocks, public responses and inference from silence.

### From acquisition to incentives

An event sequence can express temporal order, but the strategic obligation
also compares histories and available continuations. For candidate evidence,
the useful pattern has this causal shape:

```text
certify candidate h with value v -----> Bob possesses the certificate
             |                                     |
             v                                     |
publicly associate game binding with h -------------+
                                                   v
                                     Bob can determine the game value
                                                   |
                                                   v
                                     Bob takes a consequential action
```

The same public association can leave Carol unable to distinguish two values.
That claim needs equality of her observations or the relevant conditional
laws across executions. Absence of a direct message edge alone does not prove
it: timing and other players' responses may carry information.

Represent a first pattern with predicates on existing histories and information
sites, not a new trace grammar. The proof obligations are:

- actual reachability and the order in which events can occur;
- evidence validity throughout each receiver information set;
- indistinguishability or conditional-law bounds for other players;
- remaining legal responses and their outcome laws;
- the probabilities needed for an expected-payoff comparison.

This allows a partial pattern to ignore irrelevant interleaving while retaining
the facts that make it strategically significant. A positive-probability path
alone does not prove an initialized equilibrium obstruction; players' ability
to induce the relevant continuation must also be established.

## Requirements on arbitrary further abstractions

There are two different conclusions. The local response requirement is checked;
the initialized equilibrium comparison above is not yet proved.

### Local conditional behavior

Take two actual decision sites for one player, with the same fixed payoff and
retained action interface. Suppose their posterior decision problems have no
common maximizing action. An abstract observation that merges the
sites cannot support a rational implementation whose retained response law
depends only on that abstract observation.

[`ObservationRequirement.lean`](../GameTheoryExtensions/Analysis/Protocol/ObservationRequirement.lean)
proves this directly for families of actual continuation decisions. Under
sequential rationality, every nonempty abstract-observation fiber has a common
posterior-maximizing action. The result uses the game's fixed utility and its
actual beliefs; randomized responses cannot evade the requirement.
`expectedReward_of_known` makes that posterior reward independent of beliefs
when evidence fixes the payoff-relevant state throughout the information set.

The [protocol test](../GameTheoryExtensionsTests/ObservationRequirement.lean)
has two supported decision sites, one fixed correct-report payoff and an actual
standard SE. It checks the coarsening obstruction for arbitrary assessments,
and separately checks the escape through a state-aware macro action. A native
instantiation still needs its actual continuation decisions and retained-response
factorization; these are substantive premises, not consequences of hiding a
field in syntax.

`not_rational_of_coarsening_collision` propagates the local obstruction to
arbitrary further compositions of observation maps when
the retained-response requirement is maintained. It does not constrain an
implementation allowed to use the forgotten distinction inside a native
macro action. Such an abstraction may represent the conditional capability
through action semantics instead of exposing separate information states.

### Initialized equilibrium outcomes

To exclude arbitrary strategy translation, including payoff-dependent repair,
prove that every rational full-runtime assessment has a payout above a
restricted-runtime equilibrium's payout. The
[`induced-information theorem`](../GameTheoryExtensions/Analysis/Protocol/InducedInformation.lean)
already supplies this implication from operational information, feasible
deviation and continuation premises.

Any further abstract model which still represents that restricted game and
preserves that particular equilibrium outcome inherits the obstruction to
implementation in the full runtime. This conclusion allows arbitrary target
strategies and beliefs. It does not assume that a further abstraction preserves
the witness equilibrium automatically: excluding the game or changing its
information guarantees is a possible language restriction to identify.

The local requirement alone cannot replace the full initialized separation:
an implementation may use different native histories or a state-aware macro,
and a local information difference need not change any equilibrium outcome.
The universal native payoff bound is what rules out all those alternative
target assessments once the restricted equilibrium has been established.

The resulting requirement is to represent the consequential conditional
capability, or to restrict the admitted games until it is harmless. It is not
a requirement to retain particular packet identities or an explicit network
statement in the source language.

## Model restrictions and zero-probability play

An SE may assign an available action probability zero. Full support is required
of the approximating profiles used to justify beliefs, not of the equilibrium
profile itself. Our actual `IsSequentialEquilibriumFor` definition combines
sequential rationality with a common limit of fully mixed Bayes assessments.

The relevant distinctions are:

| Operation | What changes |
| --- | --- |
| Prescribe an available action with probability zero | One candidate strategy changes. The action remains a deviation; histories following it and rationality at their information sets remain part of the game. |
| Remove an action from a response menu | Feasible deviations, legal histories, information fibers and the space of consistency approximants change. An equilibrium of the smaller game need not extend. |
| Set a chance outcome's probability to zero in the runtime | The transition kernel changes. Our legal traces use its support. Player trembles keep that kernel fixed and cannot restore the removed chance outcome. |
| Hide an operation through an abstraction | The concrete capability remains. A preservation proof must represent its consequences, show it redundant for the claimed property, or restrict the admitted games. |

This is a change in the domains of the rationality and consistency conditions,
not a permutation of their quantifiers. At a fixed information site, rationality
compares the prescribed continuation with every feasible deviation, including
one assigned probability zero. Removing that deviation removes an inequality.
Removing histories also changes which conditional beliefs must be justified.
The [primary consistency reference](runtime-feature-literature.md#strategy-zeros-and-restrictions-on-the-game)
explains the fixed role of Nature's probabilities.

### Checked example and local omission certificate

[`ActionRestriction.lean`](../GameTheoryExtensionsTests/ActionRestriction.lean)
uses the existing terminal decision protocol, one state and one fixed payoff:
`false` pays zero and `true` pays one. Either singleton action restriction has a
standard SE. Restoring both actions makes the restricted `false` outcome
impossible at every SE, with arbitrary target strategies and beliefs. The
proposed always-false full-game assessment is nevertheless sequentially
consistent: it fails rationality. Conversely, the optimal always-true assessment
is an SE with the legal action `false` assigned probability zero. Thus the
distinction already occurs in a decision with no off-path information problem.

The generic
[`rationalAt_iff_omitted_not_profitable`](../GameTheoryExtensions/Analysis/Protocol/ContinuationDecision.lean)
states the additional local obligation exactly: once retained alternatives
have been checked, every omitted alternative must offer no higher continuation
value. `rationalAt_of_omitted_dominated` gives a sufficient certificate valid for
every belief at the site: each omitted action has a retained replacement whose
reward is at least as high at every compatible history. The replacement must
be the same throughout that information set; choosing it using the hidden
history would silently supply additional information.

These results address local incentives. A full game extension still needs
rational continuations at any added information sites and one consistent belief
system across the entire game. A local dominance check alone is not an SE
preservation theorem.

### What justifies a runtime restriction

The empty-observation experiment is a restriction on an external chance rule.
It is a valid mathematical comparison because the rule is fixed independently
of player strategies. Whether it describes the intended deployment is a
separate assumption. Likewise, excluding premature transmissions from every
legal menu needs either enforcement, an explicit behavioral restriction on the
players under study, or a proof that restoring them preserves the claimed
strategic content. Declaring that the compiler never emits them addresses only
prescribed play.

If the network is instead modeled as a strategic player, fixing its behavior
would require its own incentive argument. A claim about miner incentives is
not established by an SE theorem for a game whose network is an external law.

The investigation uses such restrictions to locate the needed proof premises.
Their mathematical usefulness does not establish their physical enforcement
or their suitability as assumptions about a blockchain.

## Readiness restrictions

The [readiness experiment](../VegasTests/ReactiveReadinessRestrictions.lean)
uses the same selective-association runtime. Its distinction is between
**when a call can execute** and **when the evidence attached to that call can
be read**. No additional production semantics is introduced.

### Different meanings of ready

| Restriction | What it excludes or requires | Checked scope |
| --- | --- | --- |
| No premature opening calls | Opening packet bodies before the opening event's dependencies complete | The selective-association prefix uses only commitment bodies, so this restriction leaves its information channel. |
| Dependencies complete at submission | Event predecessors have completed in the original submission view | The original certified commitment satisfies the existing authorization condition. All three initial binding events are dependency-ready. |
| Every submitted call is immediately accepted by the handler | Readiness plus the applicable deadline and call-specific admission checks | The first certified commitment and both competing association envelopes pass the actual handler before selection. |
| Every pending call remains ready at every state | A persistent condition on the entire pool | The existing pool does not satisfy this: selecting one winner leaves a stale competitor. A clock step can also invalidate an otherwise ready call. |
| Drop stale packets after state changes | Additional pool maintenance | Replacing the pool preserves current player inputs. Clearing it after association retains Bob's certified evidence and Carol's indistinguishability. This is a state calculation, not a checked new service. |

The service grant records the service's current event; the application handler does
not use it as authorization. Thus Alice's first certificate-bearing commitment
already succeeds while its grant is `none`. Confusing the grant with a call's
precondition would incorrectly classify this disclosure as premature.

Here “premature opening” means an opening **call** whose dependencies are not
yet complete. If the intended restriction instead excludes every certificate
of a still-hidden value, including evidence attached to an executable commitment
call, it directly removes the disclosure capability used by this witness.
That is a different restriction to investigate: handler readiness alone does
not enforce it. Also, handler acceptance is distinct from a successful game
publication; the native semantics can accept a commitment whose binding result
is failure. The witness above uses valid Boolean bindings throughout.

The experiment checks the actual first five service rounds with Bob silent.
Alice submits a certified candidate, Bob passively observes it, and Alice then
submits a certificate-free commitment to the same candidate. Both envelopes
could execute at that point. The scheduler includes the certificate-free one;
Bob combines his earlier certificate with the public association, while Carol
sees the same public data in both value worlds.

**Consequence:** banning premature opening bodies or requiring immediate
acceptability at submission does not eliminate this operational information
pattern. This does not yet prove SE failure for the corresponding restricted
games. Removing responses changes their rationality conditions, so the existing
full-menu payoff bound cannot simply be applied to their assessments.

### Where readiness does help

The earlier [opening-race example](early-opening-and-spe.md) uses a fresh
opening before its dependency has completed to improve a later selection
probability. The checked
[`ReactiveDependencyService`](../VegasTests/ReactiveDependencyService.lean)
denies authorization to that envelope and to the earlier premature withholding
call, and recalculates both compared continuations. This removes that particular
profitable comparison. It supplies no general SE theorem and does not remove
evidence attached to currently executable commitment calls.

### Deployment interpretation

Geth distinguishes executable pending transactions from queued transactions
with nonce gaps, and exposes both through its transaction-pool API.
[Geth's pool description](https://geth.ethereum.org/docs/monitoring/understanding-dashboards#transaction-pool),
[pool API](https://geth.ethereum.org/docs/interacting-with-geth/rpc/ns-txpool).
This network/client distinction must not be identified with a Vegas event's
application preconditions. Ethereum receipts explicitly represent failed
execution of included transactions.
[EIP-658](https://eips.ethereum.org/EIPS/eip-658).

It follows that requiring every modeled message to be an immediately successful
game call is an extra abstraction or service premise, rather than a consequence
of ordinary transaction validity. The evidence-bearing, immediately acceptable
commitment above shows why that premise alone still leaves selective disclosure
to analyze. A runtime-general result should state separately which traffic is
observable, which calls are admissible, and what happens to stale competitors.

## Other controlled comparisons

| Restriction to lift | Candidate property to preserve or explain | Current evidence |
| --- | --- | --- |
| Evidence becomes usable only after a public game association | Whether evidence about a candidate can be privately established first and linked later | Full source/native separation; an isolated same-runtime evidence restriction still needs a precise operational definition. |
| Payload authorization requires dependencies at submission, versus readiness checked only at execution | Which earlier transmissions can contribute to a later event | Checked service invariants and a repaired concrete SPE comparison; no general SE theorem. |
| Included identifiers are excluded from future selection, versus replay restoring eligibility | Whether a player can change selection power without a fresh candidate | Checked network selection and local incentive witnesses; no general SE separation. |
| A fixed completion opportunity is guaranteed, versus competing uses of that opportunity | Which continuations remain feasible before expiry | Checked compiler-specific SPE failure; no universal deadline abstraction impossibility. |

Each edge must be investigated separately. A failure for one scheduler is not
a failure for every restoration of the feature. A successful operational
simulation is not by itself a sequential-equilibrium preservation theorem.
