# Recovery without extra player actions

An initialized-play compiler can leave its behavior after earlier deviations
unspecified. SPE cannot: it tests continuations at proper subgames even when
the prescribed profile would never reach them. In particular, an earlier bad
submission must not make the compiled player permanently wait while a useful
submission remains available.

Recovery must also respect randomness. Sampling a behavioral policy on every
activation can reveal repeated samples to other players or the scheduler.
The compiler therefore separates prescribed play from recovery using facts
already in the player's own recall.

## The policy definition

The compiler has three components in
[ReactivePolicy.lean](../Vegas/Pending/ReactivePolicy.lean):

1. **Prescribed play.** At a ready owned grant, sample the source decision,
   remember its intention, and submit one packet. Wait on later activations
   for that event.
2. **Consistency of own recall.** Check each recorded response against the
   support of the prescribed policy at its original local view and recall
   prefix. A possible random choice is consistent; it need not equal a new
   independent draw.
3. **Recovery.** After any unsupported earlier response, a ready owned grant
   permits another submission. Reuse the most recently remembered choice for
   that event which is supported by the current source decision law. If none
   exists, sample that law. Retain the choice in private implementation state
   and submit in the same response.

This is one total, playerwise policy. The consistency check is private
computation over existing recall. It introduces no source flag, runtime state
field, preparation step, activation, or observation. An unsupported earlier
response remains in recall; adding later responses does not erase it.

Prescribed and recovery implementations keep source intentions internally.
Their behavioral policies use the posterior over this state given actual own
observations and semantic responses. No intention tag appears in game actions.
The [implementation adapter](../Interaction/ReactiveImplementation.lean) proves
whole-execution realization against arbitrary opponents and scheduling; it does
not assert rationality of off-path recovery or consistency of equilibrium beliefs.

A recovery submission uses a fresh commitment handle when binding. Earlier
packets remain pending with their immutable meanings, and deadlines remain
unchanged. Resubmission does not promise successful inclusion. If another
activation occurs while the recovered choice is still supported, the compiler
reuses that choice. Recovery never requires utility values or a ranking of
the retained candidates.

## Which intention is remembered after inclusion?

A binding completion supplies the value that actually took effect. A different
candidate's earlier intention must not replace it in subsequent observations.

A failed disclosure needs an additional distinction: intending to disclose
can produce the same withholding packet as intending to withhold. The compiler
restores that private intention only from a response whose emitted packet has
an accepting receipt. It also checks that the remembered intention generates
the recorded response at its recorded view. A mismatched internal intention is
not such a witness. If no matching response exists, reconstruction uses the actual
graph completion.

Receipt matching uses message identifiers, so competing submissions do not
cause the first remembered intention to overwrite the selected one. General
source-observation correspondence still requires the application and provenance
invariants; these reconstruction rules alone are not that theorem.

## Checked guarantees

| Claim | Artifact |
|---|---|
| Following the completed policy preserves consistency of own recall, with arbitrary opponents and scheduling | [`Policy.recover_invariant`](../Interaction/ReactiveRecovery.lean) |
| Completing a policy preserves round execution laws from consistent recall | [`Policy.recover_runRounds`](../Interaction/ReactiveRecovery.lean) |
| It preserves initialized canonical state laws at every fuel bound, including intermediate player states | [`Policy.recover_canonical_run`](../Interaction/ReactiveRecovery.lean) |
| The graph compiler satisfies that equality playerwise | [`compileReactivePolicy_canonical_run`](../Vegas/Pending/ReactivePolicyFacts.lean) |
| The actual compiler realizes its prescribed private implementation against arbitrary opponents and scheduling | [`compileReactivePolicy_realizes`](../Vegas/Pending/ReactivePolicyFacts.lean) |
| Its initialized one-packet guarantee still holds against arbitrary opponents | [`canonical_reactivePacketIntegrity`](../Vegas/Pending/ReactivePacketIntegrity.lean) |
| Recovery chooses only from the current source law's support and retains a still-supported recent choice | [`reactiveRecoveryLaw_support` and `reactiveRecoveryLaw_remembered`](../Vegas/Pending/ReactivePolicyFacts.lean) |
| Recovery is locally optimal under the fixed inclusion-mixture and downstream-law premises | [`reactiveRecoveryLaw_optimal_response`](../Vegas/Pending/ReactivePolicyFacts.lean) |
| Recovery is locally optimal under the weaker regularity and fixed downstream-law premises | [`reactiveRecoveryLaw_regular_optimal`](../Vegas/Pending/ReactiveRegularity.lean) |
| The actual service never includes an identifier twice, including after rejection | [`interaction_history_publishedOnce`](../Vegas/Pending/ReactiveServicePublication.lean) |
| Every rebroadcast preserves the unpublished eligible menu at every legal initialized history | [`replay_unpublished_history`](../Interaction/ReactivePublication.lean) |

The state-law equality includes application state, network contents, private
recall, receipts, and scheduler recall. It is not merely a public marginal.
The theorem compares completed and prescribed policies from initialization;
it does not equate their behavior at arbitrary inconsistent prefixes.

The local incentive result uses a simple fact: every supported action of an
optimal finite lottery has the same optimal expected value. Any lottery
supported there is therefore optimal too. Combining this fact with the
[pending-selection contract](inclusion-and-spe.md) proves that the recovery
lottery is optimal against arbitrary randomized optional submissions, for a
fixed downstream kernel. This includes both reuse and fresh sampling.

Regularity also gives an exact response-law factorization with common branch
weights, including silence. This is proved in
[RegularChoiceSimulation.lean](../GameTheoryExtensions/Core/RegularChoiceSimulation.lean).
Supported recovery may reuse a choice instead of the original source lottery;
equal optimal utility does not imply equal action laws. A whole-service
correspondence must account for this distinction explicitly.

[ReactiveRuntime.lean](../VegasTests/ReactiveRuntime.lean) checks an actual
wrong binding response followed by the compiler's recovery choice, and checks
that ordinary supported choices are not resampled.
[ReactiveRecovery.lean](../VegasTests/ReactiveRecovery.lean) checks accepted,
rejected, competing, and mismatched internal disclosure intentions, and proves
that the two failed-disclosure intentions give the same semantic action. These are operational
and reconstruction tests; they do not certify proper native subgame roots.

## Remaining SPE obligations

This construction supplies a recovery policy and its initialized compatibility
proof. The [early-opening counterexample](early-opening-and-spe.md) proves that
recovery is not optimal under uniform inclusion and at-most-once publication
alone. Spending a transmission on a later opening can outperform the compiler's
attempt to repair the current binding. The schedule is fixed, and the source
policy is honest and SPE. A positive result requires a service or translation
contract addressing this competition between events, as well as intervening
reactions, deadlines, and information sets.

In particular, the local theorem fixes the selection law and downstream
kernel across fresh source values. The regularity version permits changed
relative odds among old candidates after submission, provided none gains
absolute probability. A scheduler can react to new
public transmissions, so a final uniform selection step alone does not establish
those premises. The same source-root mixture must also work for every unilateral
deviator at a native root. Irreversible forfeiture still requires the chosen
source admission interface or a proved elision condition.

The [reactive inclusion counterexample](reactive-inclusion-obstruction.md)
shows that no utility-independent completion works for every scheduler
permitted by the reactive interface. Public traffic can change which retained
candidate wins, without giving the new source-optimal candidate any chance.
This obstruction holds even when source forfeiture is admitted.

Passive partial leaks, foreign-message reactions, and scheduler memory of
public traffic remain available. Native SPE preservation under a constrained
service remains open.
