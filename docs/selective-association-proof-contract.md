# Selective association: proof contract

This compares **accepted named-binding evidence** and **candidate evidence later
associated with a binding**. No sequential-equilibrium impossibility for the
full named-evidence source service has been proved yet.

## Source evidence capability

Use the full existing `Vegas.Source.CommitmentEvidence` interface. A fact is
true only when its source name already occurs in the current context with the
stated successful binding. The owner may transmit any such fact; recipients
may forward facts they possess. False claims remain freely available.

The initial setup has no commitment bindings. Thus no certificate naming the
first future binding can be issued initially. Certifying an unaccepted proposal
would be a further evidence capability: the current `Holds` predicate does not
assert facts about proposals or future source names.

## Matching service timeline

The witness uses the actual compilation of the six-statement source program in
[`SelectiveAssociationGame.lean`](../VegasTests/SelectiveAssociationGame.lean):
Alice binds a Boolean, Carol binds a guess, Bob binds a guess, then each opens
in that order. There are no initial bindings or private inputs; all guards
accept. The schedule is defined in
[`SelectiveAssociationNative.lean`](../VegasTests/SelectiveAssociationNative.lean).

1. Alice has an ambient response. Its envelope remains pending.
2. Bob activates, with a passive leak rule selecting only Alice's first envelope.
   Bob then has an arbitrary response. It is neither recorded nor leaked to
   Alice or Carol before their next decisions.
3. Alice has another response for her binding event. The reserved selector
   includes her latest envelope addressed to that event.
4. Carol chooses her hidden guess and its binding is included.
5. Bob has his final guess response and reserved inclusion.
6. Ordinary opening events occur. There is no automatic opening primitive.

The compiler's barrier order leaves all three binding events initially ready.
The fixed service visits Alice, Carol, then Bob; source statement order and
native service order therefore agree without adding graph dependencies. The
candidate leak rule is stateless: it selects Alice's first envelope only for
Bob, and selects no envelopes for Alice or Carol. It inspects no private
delivery history. A second Bob activation may revisit the old envelope;
[`MessageNetwork.learn`](../Interaction/MessageNetwork.lean) excludes each
identifier for which `network.known who` already contains a message.

Every source response retains all possessed named certificates, arbitrary
claims, and forwarding. Envelopes are immutable. Any new named certificate
emitted after association has a new envelope identity and is not privately
delivered before the guesses under this rule. Recording it makes it public;
public disclosure remains available and must be covered by the source
equilibrium proof. An already pending certificate is not silently excluded:
the argument must show that no certificate of this previously absent binding
could have been valid when the earlier envelope was emitted.

## Actual native capability and admission risk

Alice's first native envelope can register a candidate `h` with value `x` and
carry its opening certificate. Her later envelope can bind that same `h`
without carrying a certificate. The checked association theorem states that
Bob's earlier candidate certificate and the public accepted association imply
the named binding at every compatible native history.

Candidate registration currently requires a commitment call. It is not a
standalone seal operation. The first packet may itself bind the game event if
included. The witness must therefore prove that the stated schedule leaves it
pending and selects Alice's later envelope, including after arbitrary replay
and competing traffic from Bob. This coupling may not be erased in the source
service contract.

The native prefix is checked in
[`ReactiveAssociationEvidence.lean`](../VegasTests/ReactiveAssociationEvidence.lean).
`later_envelope_selected` proves the latest-envelope selection for every Bob
response, including replay. `association_after_arbitrary_response` proves
Bob retains the earlier certificate and recognizes the accepted binding.
`carol_input_after_arbitrary_responses` proves equality of Carol's full recall
and current view even with different Bob responses in the two worlds;
`carol_activation_after_arbitrary_responses` extends it through the actual
passive-observation activation. It uses the shared compiled six-event graph.
The complete native deviation bound remains unproved.

## Checked schedule and payoff facts

[`SelectiveAssociationSchedule.lean`](../VegasTests/SelectiveAssociationSchedule.lean)
proves timeliness at every visit and terminal completion for arbitrary native
policies. Visit `e` has deadline `2^e`; the preceding visits use `2^e - 1`
clock ticks. Each visit provides one response and reserved inclusion, then
enough ticks and expiry to settle omissions. The evaluator agrees exactly with
the native scheduler. These are service guarantees, not prescribed openings.

[`ReactiveRoundReachability.lean`](../Interaction/ReactiveRoundReachability.lean)
connects every legal finite-menu history to round evaluation under a profile
that supports all responses.
[`SelectiveAssociationHistory.lean`](../VegasTests/SelectiveAssociationHistory.lean)
and [`SelectiveAssociationCursor.lean`](../VegasTests/SelectiveAssociationCursor.lean)
therefore give ready-or-completed status, timeliness, and remaining horizon at
every decision information fiber identified by its public service grant.

[`SelectiveAssociationOpeningService.lean`](../VegasTests/SelectiveAssociationOpeningService.lean)
constructs a legal opening response from the owner's observation. For a
successful binding at a ready, timely visit, reserved inclusion publishes the
value despite arbitrary earlier traffic. This establishes the feasible
alternative.

[`SelectiveAssociationOpeningEquilibrium.lean`](../VegasTests/SelectiveAssociationOpeningEquilibrium.lean)
proves that sequential rationality forces publication of exactly the bound value
at every usable opening information set with a successful owned binding. It covers all three
players, the complete bounded raw response menu, every compatible legal history,
and arbitrary earlier deviations. Successful disclosure is a consequence of
incentives under the actual service, rather than an imposed action.

The argument needs more than optimality in expectation. A compatible history
can have posterior probability zero. For each fixed raw response,
[`SelectiveAssociationOpeningSelection.lean`](../VegasTests/SelectiveAssociationOpeningSelection.lean)
proves that own recall and observation determine its reserved-inclusion effect.
[`SelectiveAssociationOpeningSettlement.lean`](../VegasTests/SelectiveAssociationOpeningSettlement.lean)
then accounts for the actual clock ticks and expiry. Thus a response that fails
at one compatible history fails throughout that information set. Its payoff is
minus four everywhere, while an available ordinary opening gives at least minus
one everywhere. Sequential rationality excludes the failing response from the
strategy's support. No positive-posterior premise for individual histories is
used.

[`SelectiveAssociationCorrection.lean`](../VegasTests/SelectiveAssociationCorrection.lean)
proves Bob's corrective binding is available at every legal binding decision:
he has only one earlier response, so two candidates leave a fresh one. Its new
packet replaces an older pending guess under the actual reserved selector.
[`SelectiveAssociationGuessEquilibrium.lean`](../VegasTests/SelectiveAssociationGuessEquilibrium.lean)
proves Bob's incentive: when his observation certifies Alice's accepted bit,
sequential rationality forces a matching successful guess and publication.
The statement covers the complete mixed strategy and every compatible history.
[`SelectiveAssociationSupportedResponses.lean`](../VegasTests/SelectiveAssociationSupportedResponses.lean)
also proves guarantees for each supported raw response. These apply during
Alice's deviating continuation, whose later actions need not follow the
assessment strategy.

Utilities depend only on the original three publication results. Alice receives
Bob's correctness minus Carol's correctness; each guesser receives its own
correctness. Each player loses four units if its own publication fails.
[`SelectiveAssociationPayoffs.lean`](../VegasTests/SelectiveAssociationPayoffs.lean)
proves that a feasible successful opening is preferable even allowing different
other-player results in the compared continuations.
[`SelectiveAssociationProbability.lean`](../VegasTests/SelectiveAssociationProbability.lean)
proves the intended half-unit deviation bound **conditional on** successful
Alice/Bob publication and Carol's independent-guess bound. Those hypotheses
still require the native information-set and incentive proofs.

[`SelectiveAssociationGuessContinuation.lean`](../VegasTests/SelectiveAssociationGuessContinuation.lean)
proves that later communication and publication decisions cannot improve the
correctness of Carol's already settled guess. Successful publication must equal
the stored binding; withholding can only remove a correct guess. [`SelectiveAssociationCarol.lean`](../VegasTests/SelectiveAssociationCarol.lean)
proves that the settled guess law is independent of Alice's bit, even with
arbitrary, different earlier Bob responses. It includes the actual reserved
inclusion, ticks, and timeout settlement.

## Source interface and equilibrium obligation

[`SelectiveAssociationSourceCore.lean`](../VegasTests/SelectiveAssociationSourceCore.lean)
uses the original source protocol transitions.
[`SelectiveAssociationSourceService.lean`](../VegasTests/SelectiveAssociationSourceService.lean)
adds pending messages with any finite nonempty claim alphabet, all requested
named evidence, silence, and every known replay. Source game actions remain
stage-local. Early request-shaped traffic is expressible as a claim; it creates
no private registry of immutable pending source proposals. The separation being
investigated concerns this **whole source interface**, not every possible
language with pending requests.

The protected response executes its source step immediately before reserved
recording, with no intervening observer. A newly accepted named binding may
already be certified in that response's packet; the source equilibrium must
handle this public disclosure. Ordinary source opening supplies genuine owned
evidence. Other claims remain available.

[`SelectiveAssociationSourceCalendar.lean`](../VegasTests/SelectiveAssociationSourceCalendar.lean)
defines the matching calendar, candidate strategy, and a common perturbation
with positive mass on every menu response. Full mixing and Bayes consistency
of each positive perturbation are checked.
[`SelectiveAssociationSourceGuessSymmetry.lean`](../VegasTests/SelectiveAssociationSourceGuessSymmetry.lean)
proves equal conditional probabilities for the two successful Alice values in
the actual response-prefix laws at guessing inputs with no public Alice certificate. Arbitrary prior
responses, claims, and Carol's response are retained. Every certificate requested at the binding response is proved to become public
before both guesses; the no-certificate premise is an observed fact. The result
uses the same common perturbation on the complete menu; failure probability need not vanish.
[`SelectiveAssociationSourceBeliefs.lean`](../VegasTests/SelectiveAssociationSourceBeliefs.lean)
connects these laws to the canonical Bayes beliefs at every guessing information
set, including off-path sites. The proof establishes the exact history depth
of each information fiber rather than assuming it.
[`SelectiveAssociationSourceConsistency.lean`](../VegasTests/SelectiveAssociationSourceConsistency.lean)
constructs a consistent assessment with the prescribed strategy and these fair
beliefs, using one common subsequence of the fully mixed assessments.

[`SelectiveAssociationSourceGuessEquilibrium.lean`](../VegasTests/SelectiveAssociationSourceGuessEquilibrium.lean)
and
[`SelectiveAssociationSourceOpeningEquilibrium.lean`](../VegasTests/SelectiveAssociationSourceOpeningEquilibrium.lean)
prove sequential rationality at the guessing and opening information sets
against arbitrary whole behavioral continuation policies. Public certificates
direct both prescribed guesses; without a public certificate, the consistent
belief assigns equal mass to the two successful values. Failed bindings and
optional failed openings remain in the game.

[`SelectiveAssociationSourceAliceValues.lean`](../VegasTests/SelectiveAssociationSourceAliceValues.lean)
proves the actual continuation payoff bounds for Alice's ambient and binding
responses: arbitrary Alice policies yield at most zero against the prescribed
guessers, while her prescribed policy yields zero. The key source fact is that
both guessers select the same public guess; recording Carol's ordinary binding
adds no new certificate. Integration of the remaining ambient and binding
incentives into a full source SE is still required.

[`SelectiveAssociationNamedEvidence.lean`](../VegasTests/SelectiveAssociationNamedEvidence.lean)
proves that its six named facts cover every genuine commitment fact of this
source program, none is available initially, and observed certificates hold
throughout the recipient's information fiber. It also proves exactly which
facts each player owns before the guesses. Thus the finite evidence alphabet
does not omit a source binding.

## Native deviation and remaining strategic obligations

[`SelectiveAssociationNativeDeviation.lean`](../VegasTests/SelectiveAssociationNativeDeviation.lean)
constructs Alice's legal strategy over the full response menu. Its prefix laws
execute the actual calendar and retain Bob's arbitrary prelude response.
[`SelectiveAssociationNativeDeviationPayoff.lean`](../VegasTests/SelectiveAssociationNativeDeviationPayoff.lean)
factors the complete outcome law through Alice's fair bit and bounds Carol's
correctness unconditionally in the opponents' policies. Its half-unit payoff
bound still assumes successful Alice and Bob publications in each supported
outcome; the remaining composition must discharge those assumptions.

The outstanding conclusions are:

- A full source sequential equilibrium and its initialized public outcome law,
  assembling the consistent beliefs and all decision-site incentives.
- Successful Alice and Bob publications throughout the actual deviating run,
  using the checked supported-response guarantees at its intermediate histories.
- A profitable whole-policy deviation at the native initial information set,
  contradicting preservation of the source equilibrium's public outcome law.

The operational association result alone does not rule out a one-way SE
compiler. A source service that already grants prospective evidence or a
matching retrospective disclosure rule needs a different analysis. No claim
that every implementation requires an ambient seal registry follows here.
