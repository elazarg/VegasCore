# Zero-sum compilation: the remaining runtime bridge

## Status and distinct conclusions

Two-player zero-sum utility gives a checked expected-value result for the
paper's pending-message service. Sequential-equilibrium implementation for the
finite reactive service remains open. The mathematical repair argument in
[zero-sum-sequential-repair.md](zero-sum-sequential-repair.md) is not yet a Lean
theorem.

Three conclusions must be distinguished:

| Conclusion | Meaning | Present status |
| --- | --- | --- |
| The compiled profile is sequentially rational | Its prescribed recovery is optimal at every legal information set, with one consistent belief system. | Not established generally; existing continuation counterexamples concern particular compilers and services. |
| Some native SE implements the source outcome | Native behavior may change off path, while the initialized decoded result law is preserved. | The proposed zero-sum repair theorem would supply this from Nash preservation into the same finite perfect-recall target. |
| Native equilibrium values equal the source value | Each player's expected utility agrees; the result and payout distributions may differ. | Checked for every coarse correlated equilibrium of the paper's pending-message policy game. |

Existence of a matching native SE is weaker than preservation by the fixed
playerwise compiler. Equality of expected utilities is weaker than either
claim and does not construct an equilibrium.

## Checked expected-value theorem

[GameTheoryExtensions/Core/ZeroSum.lean](../GameTheoryExtensions/Core/ZeroSum.lean)
works with arbitrary strategy carriers, including behavioral policies:

- `GameTheory.IsNash.zeroSum_security` turns a two-player zero-sum Nash profile
  into security guarantees against every opposing strategy.
- `GameTheory.IsCoarseCorrelatedEq.expectedUtility_eq_of_zeroSum` gives equality
  of expected utilities between any coarse correlated equilibrium and an
  existing Nash equilibrium of that same game.
- `GameTheory.IsNash.expectedUtility_eq_of_zeroSum` specializes the comparison
  to two Nash profiles without adding another mixed-strategy layer.

The actual compiler capstone is
`Vegas.SourceProgram.Setup.valueBindingParameterPendingGame_coarseCorrelated_value`
in [Vegas/Game/ZeroSum.lean](../Vegas/Game/ZeroSum.lean). Given a source Nash
profile, pointwise zero-sum utility, and the existing service-feasibility
certificate, every native coarse correlated equilibrium has its source expected
utility. Native policies need not lie in the compiler image. Utilities may
depend jointly on an initial parameter and the final public result; restricting
them to declared payouts is a specialization when the payout readout is used.

The proof uses the parameter-aware Nash and initialized-law certificates in
[ParameterOutcomes.lean](../Vegas/Game/ParameterOutcomes.lean). It concerns the
existing command-policy pending-message game. No claim about a different
reactive protocol, native SE existence, or equality of payout laws is implicit
in the statement.

### Checked ingredient for sequential repair

[ZeroSumRegularization.lean](../GameTheoryExtensions/Analysis/ZeroSumRegularization.lean)
now supplies `GameTheory.ZeroSumRegularization.exists_saddle`: finite nonempty
row and column plan carriers admit a mixed saddle for their expected base
payoff minus a nonnegative weight times the row feature distance, plus the
same weight times the column feature distance. Each distance is the L1 norm
of an expected feature vector minus its reference. The proof represents the
norms by finite sign choices and uses the existing finite minimax theorem;
the signs remain private proof machinery.

`GameTheory.ZeroSumRegularization.penalty_bound` combines two regularized
best-response comparisons with approximate security bounds at reference
candidates. It bounds the saddle's total weighted feature distance by the
two security errors and the candidates' weighted distances. Neither theorem
assumes a sequential equilibrium. Connecting finite plan features and trembles
to the protocol's own recall and continuation evaluation remains necessary.

## The existing interfaces do not yet compose

### Command-policy pending service

[EventMessageStrategic.lean](../Vegas/Game/EventMessageStrategic.lean) proves
`eventPendingGame_deviation_law`: against unchanged compiled opponents, every
native command-policy deviation has the source terminal-state law of a finite
mixture of source deviations. The same file's
`eventPendingGame_deviation_guarantee` transports lower bounds on any public
result test, even when the test is not the deviator's utility.

The underlying [EventService.lean](../Vegas/Pending/EventService.lean) schedules
three uninterrupted owner command calls before its reaction rounds and reserved
inclusion. Its player policy can issue private commands, submit, replay, or
wait. This is the service covered by the paper's strategic certificate.

### Atomic native protocol over that application

[NativeProtocol.lean](../Vegas/Pending/NativeProtocol.lean) exposes an actual
multiplayer protocol with one atomic action per player invocation.
`nativePolicyEquiv` in
[NativeProtocolPolicy.lean](../Vegas/Pending/NativeProtocolPolicy.lean) is an
exact playerwise correspondence between native policies and protocol behavioral
policies. `native_run_map_state` in
[NativeProtocolEvaluation.lean](../Vegas/Pending/NativeProtocolEvaluation.lean)
identifies their evaluation at every legal prefix.

Those are representation results for atomic policies. They do not identify
atomic policies with the command policies of the Nash theorem. In
[EventPlayerAction.lean](../Vegas/Pending/EventPlayerAction.lean),
`transmit_native` realizes one atomic transmission using zero, one, or two
low-level commands; `actionStep_native` supplies the corresponding support
fact. Neither theorem preserves a fixed service plan or its policy recall.
Similarly, `compileResponse_law` in
[NativeResponse.lean](../Vegas/Pending/NativeResponse.lean) coalesces consecutive
atomic invocations; it does not turn the command-policy Nash theorem into a
finite reactive theorem.

This atomic protocol still permits an arbitrary finite list of private memory
data in each action, as well as unbounded identifiers. Its unrestricted legal
menus are infinite. With the repository's finite-support distributions, an
infinite menu has no fully mixed law:
`BehavioralAssessment.not_isFullyMixed_of_infinite_choice` in
[Sequential.lean](../GameTheoryExtensions/Analysis/Protocol/Sequential.lean).
There is no checked finite-menu adapter for this atomic service that also
transports the paper's strategic certificate.

### Finite reactive protocol

[ReactiveFiniteResponses.lean](../Vegas/Pending/ReactiveFiniteResponses.lean)
defines explicit raw-value and candidate bounds. Its raw menu retains every
bounded packet constructor, malformed calls, certificate requests, known
forwarding references and replays, and silence. Its normalized menu removes
only operationally ineffective private distinctions. The bounds are assumptions
about the modeled backend, not an encoding theorem for arbitrary blockchain
interaction.

[ReactiveFiniteCompiler.lean](../Vegas/Pending/ReactiveFiniteCompiler.lean)
proves `compiled_response_available_history`: output-value coverage and enough
candidate capacity make every compiled response available at every legal
history. `compileFinitePolicy_run` gives exact continuation evaluation in the
normalized finite menu. These statements do not prove source correctness or
optimality.

`compileFinitePolicy_exists_consistent_assessment` in
[ReactiveFiniteConsistency.lean](../Vegas/Pending/ReactiveFiniteConsistency.lean)
constructs consistent beliefs for the finite compiled profile. It has no source
equilibrium premise and does not assert sequential rationality. The remaining
whole-service compiler obligation is stated explicitly in
[ReactivePolicy.lean](../Vegas/Pending/ReactivePolicy.lean).

The finite protocol already has useful ingredients for the repair route:
full-mixing and Bayes constructions in
[ReactiveFiniteAssessment.lean](../Interaction/ReactiveFiniteAssessment.lean),
actual own-action recall in
[ReactiveOwnPlay.lean](../Interaction/ReactiveOwnPlay.lean), and the checked
`exists_canonical_sequentialEquilibrium` theorem in
[ReactiveAliasEquilibrium.lean](../Interaction/ReactiveAliasEquilibrium.lean).
The last theorem lifts an SE from normalized responses to the full raw menu,
preserving the projected initialized state law and admitting whole-policy
deviations. Its hypotheses must be instantiated for the chosen finite bounds;
normalization is not permission to omit publicly distinguishable responses.

## Prescribed concealment and optional native disclosure

The ordinary source compiler must conceal a rejected candidate. Its source
observation contains publication failure, without the failed value. This is
separate from a deviating player's ability to publish authentic evidence.

`reactiveResolutionPacket` in
[ReactivePolicy.lean](../Vegas/Pending/ReactivePolicy.lean) computes
`EventCode.resolveOutput?` using the owner's local store. It emits an opening
only for a successful validated publication; withholding implements every
failed result. `EventCode.resolveOutput?_playerStore` in
[Validation.lean](../Vegas/EventGraph/Validation.lean) proves that this local
calculation equals the full-store calculation. All guard inputs are public,
and the owner can read its binding. No private input of another player is
required. This is the same packet-selection rule as `resolutionPayload` in
[EventPolicies.lean](../Vegas/Pending/EventPolicies.lean).

The checked local and service guarantees retain their full public-result scope:

- `reactiveDecision_disclosure_public_law` realizes either source disclosure
  choice and either guarded result, including failed bindings and rejected
  successful bindings. Withholding can alias different source choices, so its
  conclusion is equality of the store and public observation; the compiler's
  implementation retains its sampled intention privately.
- `reactiveDecision_rejected_action_irrel` proves that a rejected resolution
  emits the same response for both source disclosure choices.
- `reactiveResolutionPacket_eq_of_resolution` uses equality of the guarded
  result and accepted handle. The full read frame in
  [ReactiveDisclosureService.lean](../Vegas/Pending/ReactiveDisclosureService.lean)
  supplies both equalities throughout arbitrary wire reactions.
- `reactiveDecision_disclosure_service` realizes the sampled public result
  after those reactions and the reserved inclusion. Its existing readiness,
  deadline, integrity, and availability premises are unchanged.
- `compiled_packet` in
  [CommunicationNative.lean](../VegasTests/CommunicationNative.lean) withholds
  the actual guard-rejected secret in the existing fixture. The same file's
  explicit raw `submitted` and `included` executions still prove failure of
  publication together with public knowledge of the secret binding.

The ambient source experiment in
[Communication.lean](../Vegas/Source/Communication.lean) instead emits evidence
when its source disclosure choice is true, including a rejected publication.
That experiment has additional communication decisions and observations.
`Setup.compileReactiveStrategy` currently accepts an ordinary source policy;
it is not a compiler for those communication-extended policies. The runtime's
raw opening actions, certificate requests, handlers, and evidence decoding stay
available. There is no mode flag making the ordinary source compiler disclose
failed values. These statements concern the existing ideal commitment model;
they are not cryptographic implementation claims.

### Why even a zero-sum security proof needs concealment

The following is a written counterexample design, not a checked full game.
Alice privately binds a fair bit, then resolves it under an unsatisfiable guard.
Bob next binds his guess. Alice later binds the same bit again, using her own
source recall; their final publications permit comparison. Give Bob payoff
`+1` for a correct guess and `-1` for an incorrect guess, and Alice its negative.
Give a withholding or failed guessing action payoff `-1` for Bob; if his guess
succeeds and Alice's final publication fails, give Bob `+1`. The first failed
publication carries no payoff.

Against Alice's prescribed source strategy, Bob sees only failure before
fixing his guess: his expected payoff is at most zero. If Alice's compiler
were to emit that first rejected opening, its ledger inclusion would reveal
the reused bit before Bob chooses. Bob could then guess correctly. Passive
leaks and miner collusion are unnecessary for this candidate, since inclusion
itself is public. Completing a Lean counterexample would require the actual
source and native run laws and all response cases. The checked fixture above
establishes the relevant raw disclosure capability and the prescribed
concealment separately. This concerns security of a specified compiler
strategy; it does not exclude every native equilibrium implementing the same
source payout law.

## The existing recurring service is the positive candidate

Use `interactionScheduler` and `interactionHorizon` from
[ReactiveService.lean](../Vegas/Pending/ReactiveService.lean), with the finite
response bounds already defined for that runtime. Each epoch visits every
event: it grants the event, activates its owner when strategic, permits a fixed
finite number of arbitrary wire reactions, reserves inclusion of the latest
eligible owner packet for that event, and samples public chance when relevant.
The epoch then advances the clock and expires overdue events. Envelopes are
included at most once, even after application rejection. The network may react
to public transmissions; passive observations use the separate observation rule.

This is stronger service than eventual completion. The checked
`interactionEpoch_owner_opportunity` and
`interactionEpoch_new_activation_opportunity` provide ready, timely visits
under their stated age and deadline premises. `ServiceFeasible` requires every
deadline to be at least two epochs. Arbitrary bounded reactions occur between
the response and reserved inclusion without clock advancement.
`reactiveDecision_binding_service` and `reactiveDecision_disclosure_service`
already prove the corresponding result is realized across that entire block,
under the stated state, provenance, submission-audit and policy-integrity
invariants. The proofs permit arbitrary opposing policies and network reactions;
they do not require a scheduler oblivious to packet identity.

`canonical_interaction_service` identifies this explicit service evaluation
with the actual canonical behavioral run. `compileReactivePolicy_canonical_run`
also identifies recovery-completed and prescribed initialized behavior against
arbitrary opponents and schedulers. Neither theorem yet identifies those runs
with the source evaluator. The remaining substantive step is source observation
reconstruction and effective-action locality across the whole recurring service.
The command-service mixture theorem provides a proof template, not an adapter:
its service, private staging calls, and recall differ. Source public barriers,
owner-local validated packet selection, private intention reconstruction and
the actual opportunity lemmas must enter the new proof explicitly.

These are the assumptions of the existing positive candidate, not a proved
minimality characterization. Finite value alphabets, sufficient fresh-candidate
capacity and bounded interaction are additional hypotheses of its finite-menu
SE formulation. They do not follow merely from transaction replay protection.

## A concrete service obstruction that zero-sum does not remove

**The game-level payoff separation in this paragraph is a proposed proof,
not a checked theorem.** Its operational prefix is checked in the existing
two-player `SequentialValidation` runtime; no new scheduler is needed to state
it.

Alice has three early opportunities; Bob has one later opportunity. If Alice
remains silent, Bob is activated before his dependencies settle. The checked
`silent_bob_not_ready` and `legal_unusable_bob_response` declarations in
[CommunicationServiceOmission.lean](../VegasTests/CommunicationServiceOmission.lean)
exhibit this as an actual legal history. The service is dependency-authorized
and uses at-most-once inclusion, as proved by `native_service_authorized` and
`native_service_once` in
[SequentialValidationService.lean](../VegasTests/SequentialValidationService.lean).
That file also proves `VegasTests.SequentialValidation.native_unique_bob_activation`.

Consider changing the declared payoff to give Bob 1 exactly when his final
publication succeeds, and Alice its negative. Bob's initial commitment is a
successful commitment to `true`. In the source, his final disclosure action
can succeed after any preceding Alice choices; `VegasTests.SequentialValidation.guess_publication` in
[SequentialValidationSource.lean](../VegasTests/SequentialValidationSource.lean)
is the relevant checked calculation. The expected source value for Bob should
therefore be 1.

In the native silent prefix, Bob's sole response cannot yet resolve his event.
After the last selection, `native_calendar_tail` in
[SequentialValidationTail.lean](../VegasTests/SequentialValidationTail.lean)
permits only clock advancement and expiry. There is no later player activation
or inclusion. The proposed native bound is therefore 0 for Bob against silent
Alice. To turn this into a theorem requires the actual declared-payoff change,
a proof covering every legal Bob response at that prefix, the final failure
readout, and the source and native strategic bounds. The existing fixture uses
the normalized finite menu; a raw-menu statement also requires its adapter.

This candidate concerns loss of a usable response opportunity, not disclosure
preferences. Eventual completion by timeout does not provide the missing
choice. The recurring service has stronger checked opportunity guarantees:
`interactionEpoch_owner_opportunity` and
`interactionEpoch_new_activation_opportunity` in
[ReactiveServiceOpportunity.lean](../Vegas/Pending/ReactiveServiceOpportunity.lean)
provide timely visits under their explicit deadline and activation hypotheses.
Those lemmas are ingredients for a positive service theorem, not that theorem
itself.

## Minimal final proof plan

1. **Fix one finite reactive target and prove its initialized Nash edge.**
   State the existing runtime, observation rule, bounded response menu, service
   and deadline premises explicitly. Use the guard-aware prescribed emission
   above and prove whole-service source observation reconstruction. Then prove
   the compiled initialized decoded law and the two security bounds against every
   bounded native opposing
   policy. For fixed zero-sum utility, those bounds suffice to establish native
   Nash; a full mixture backtranslation would be a stronger optional result.
   Persistent private parameters must use the same joint readout on both sides.
2. **Formalize the general repair theorem in the extension library.**
   Derive finite perfect-recall realization plans from the actual protocol
   interface, prove the localized continuation identities, and construct the
   common behavior-and-Bayes limit in the
   [mathematical proof](zero-sum-sequential-repair.md). Consistency alone cannot
   replace the conditional optimality proof. The multiplayer extension requires
   the stated aggregate comparison condition; terminal utilities summing to
   zero are insufficient. Pairwise zero-sum decomposition must hold for the
   expected realization-plan payoffs to use the polymatrix sufficient case.
3. **Compose into an outcome implementation statement.**
   Apply repair to the native Nash profile of step 1, then use the decoded-law
   equality. Obtain some native SE with the source initialized public-result
   law, and consequently its payout law. If normalized responses were used,
   discharge the existing alias-lifting hypotheses and return the full raw-menu
   assessment. A source SE premise additionally needs its checked implication
   to Nash for the source evaluator used in step 1.

This route uses the existing source and reactive runtime. It adds neither a new
runtime layer nor another bespoke fixture. It permits utility-dependent
off-path repair and does not assert that the original compiler's recovery,
source beliefs, or every continuation law are preserved.

## Commitment capability boundary

The [ideal commitment capability audit](ideal-commitment-capabilities.md)
distinguishes capabilities attached to player identity from operations enabled
by possession of actual material. The ideal runtime forwards issued
certificates and recommits learned values, but does not represent arbitrary
use of a foreign opening witness or shared signing key, including initially
correlated possession. It also excludes some commitments to related unknown
values. Hiding, binding, authentication, and non-malleability alone do not
justify denying an operation to a player who possesses its valid witness or
key.

A concrete initialized Nash refinement might protect the fresh secrets of
prescribed compiled opponents. That does not establish sequential optimality
after arbitrary legal native sharing histories. Both the initialized secret
distribution and the operations available after sharing need explicit scope.
Generic zero-sum results remain valid for the supplied game; the runtime bridge
must establish that it supplies the required strategies and information.
