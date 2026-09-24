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

### Exact proof target and status

The candidate separating game is the existing declared-payoff game. The
proposed restricted-runtime witness has Alice choose a fair bit and gives her
expected payout zero. **Existence of that equilibrium in the native runtime
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

A candidate prescription uses silent preludes, a fresh fair binding for Alice,
public-evidence guesses, and ordinary openings. Off-path binding repair must
choose a fresh candidate after an arbitrary prelude. The finite-menu consistency
machinery and native service facts are reusable; the named-source posterior
symmetry proof is only a template. The main new obligation is a native symmetry
argument covering the full raw menu, followed by one common perturbation limit
and whole-policy rationality at every site.

An operational positive control is already checked: private observation cannot
change the scheduler's observation or its next choice after a silent response.
This isolates the additional information from direct scheduler coordination.
It is not an SE-preservation result for subsequent play. A separate candidate
positive edge would restore observations only after every action affecting the
retained payoff is irrevocable; its full continuation theorem is open.

## What a small pattern must retain

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

There are two different intended conclusions. These are theorem templates;
the complete feature comparison above is not yet proved.

### Local conditional behavior

Take two actual decision sites for one player, with the same fixed payoff and
retained action interface. Suppose their posterior decision problems have no
common maximizing action. An abstract observation that merges the
sites cannot support a rational implementation whose retained response law
depends only on that abstract observation.

The existing
[`ContinuationDecision`](../GameTheoryExtensions/Analysis/Protocol/ContinuationDecision.lean)
support and common-maximizer theorems supply the local incentive argument.
[`Knowledge.lean`](../GameTheoryExtensions/Protocol/Knowledge.lean) turns
authenticated knowledge into a constraint on every information-set belief.
An observation map and an action-respecting implementation still need to be
specified for an abstraction instance.

Further composition of observation maps cannot recover a distinction already
merged. This propagates the local obstruction to coarser observations when
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

The resulting requirement is to represent the consequential conditional
capability, or to restrict the admitted games until it is harmless. It is not
a requirement to retain particular packet identities or an explicit network
statement in the source language.

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
