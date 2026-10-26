# Source phase correspondence and Nash transport

The source game is `Vegas.SourceProgram.Setup.sourcePhaseGame`: the existing
source exit/retry protocol, with declared integer cash and a separate history
valuation. The physical target uses `phaseApplication` with the same maximal
commitment blocks. Singleton sequential phases are a distinct partition; their
after-failure behavior cannot be identified with that source kernel.

The target Nash port must compile each player's policy independently, preserve
the initialized joint observation/cash law for every source profile, and cover
every native unilateral deviation against the compiled opponents. Reflection
must retain every source unilateral deviation. Neither a legal source endpoint
nor an intended-only equilibrium theorem supplies these policy-law obligations.

## Checked endpoint correspondence

[SourcePhaseOperational](../Vegas/Game/SourcePhaseOperational.lean) derives the
source counterpart from the actual initialized physical trace. For every
execution mode, maximal phase plan, scheduler and pending-observation rule, an
actual completed raw prefix yields a legal terminal source history with:

- the same actual excluded set;
- the same complete typed terminal readout;
- the same entire declared integer cash vector;
- retained source recall, public chronology and archived source origins.

The counted variant retains the full consumed proposal archive and uses the
physical completion contract to derive native completion at protocol-terminal
prefixes. The caller supplies no source history or simulation witness.
These are pointwise results; the extracted history is not asserted to follow
one source policy or to have the source evaluator's probability law.

## Source payoff recoding

[SourcePhaseObservation](../Vegas/Game/SourcePhaseObservation.lean) reads the
same `TerminalObservation` from the full source game. Its Nash equivalence
retains every source policy, every source unilateral deviation and the exact
same error. Valuation must factor through that observation on completed source
paths. No finite prior, finite menus or new integrability premise is needed;
the original expectation guards are retained. This is a source outcome
recoding, not the native strategy port.

The factorization is substantive.
[SourcePhaseValuation](../Vegas/Examples/SourcePhaseValuation.lean) constructs
two legal initialized terminal histories with an initially unusable binding.
Withholding and attempting its publication give identical terminal state,
exclusions and cash, but retain different original own actions. A valuation
of that action gives different utilities, so no reader of the common terminal
observation can represent every full-history valuation.

## Checked interface distinctions

[SourcePhasePartition](../Vegas/Examples/SourcePhasePartition.lean) uses a real
two-owner program and initialized source and physical traces. Source omission
inside its maximal block retains that block's checkpoint and later retries a
surviving owner, retaining its voided action. The singleton runtime advances
the failed slot without that retry. Phase addresses, retry generations and own
recall differ. Both displayed readouts are unfinished; the result does not
assert terminal-law or Nash impossibility.

[SourcePhaseInformation](../Vegas/Examples/SourcePhaseInformation.lean) checks
an immediate-callback decoder failure on the concurrent maximal graph. A later
source owner sees an earlier owner's omission, whereas a native scheduler can
activate that later owner before the earlier owner acts. The paired source
information values differ and the paired native callback inputs agree. No
decoder maps those particular families as proposed. The witness scheduler is
not claimed to satisfy a complete physical service contract, and the theorem
does not rule out clients that wait or a unilateral-deviation simulation.

## Checked surviving information and clients

[SourcePhaseCursor](../Vegas/Game/SourcePhaseCursor.lean) and
[SourcePhaseRevealCursor](../Vegas/Game/SourcePhaseRevealCursor.lean) derive a
genuine current source cursor at every actual raw sequential binding or
disclosure request. They retain current exclusions, including earlier omissions
in the same attempt, and the full surviving source view and public chronology.
No honesty, source counterpart or service premise is supplied. Disclosure
prefixes save the current rank after each source instruction; binding prefixes
retain the commitment-block entry rank.

[SourcePhaseClient](../Vegas/Game/SourcePhaseClient.lean) proves that a complete
surviving source view and its numeric public chronology determine the entire
original source information. Its representative decoder is justified by
constancy on every realized fiber. It reads the same full source information
from actual physical callbacks, for both bindings and disclosures.

The first-opportunity client queries the original source policy and uses the
existing guarded binding/opening encoders. It is legal in the actual one-packet
and raw menus at every input. Own recall records silence as well as packets, so
the same attempt/event is sampled once. Playerwise compilation preserves
unilateral profile updates. The checked response law binds the source choice
law to the guarded physical encoder; adequate wire coverage and persistent
candidate capacity are required for untruncated encoding. The checked
[binding encoders](../Vegas/Game/SourcePhaseClientBinding.lean) derive an
actual fresh serial below the physical horizon from every supported first
callback. Horizon at most candidate capacity and coverage of every typed value
then make the encoder exact, including omission and accepted failure. The
candidate reserve is persistent across retries; an event-count bound alone
does not establish this condition.
The decoder is a mathematical representative construction, not an executable
decoder implementation.

The [opening encoder](../Vegas/Game/SourcePhaseClientOpening.lean) validates
publication using the owner's actual masked store. An intention whose deferred
guard rejects the publication emits silence, even if its binding stores a
successful value. Otherwise sending that value would disclose information
that the source's failed publication keeps private. The checked local
validation agrees with source effective disclosure under the existing failure
extension and reference-agreement hypotheses. Suppressing an ineffective
opening preserves the typed successor, exclusions and every foreign player's
[entire source information](../Vegas/Game/SourcePhaseDisclosure.lean).
The exited owner's original intention remains in its source recall.

[Actual raw client play](../Vegas/Game/SourcePhaseClientLaw.lean) has the same
whole control law as its representation in the one-packet menu at every
prefix length. Each supported raw control therefore has a genuine counted
history, and its count-audit charge is zero for every player. These facts
include omissions and retries; they do not establish native/source law
equality or transport arbitrary native deviations.

The lower [phase traffic projection](../Vegas/Pending/PhaseTraffic.lean)
retains the complete network, environment recall, receipts, focal recall and
full focal application view, including handles and phase archives. It has exact
transport through arbitrary focal responses and passive activation. Arbitrary
foreign binding-result laws have the same
[focal traffic law](../Vegas/Pending/PhaseForeignTraffic.lean) at the same slot.
[Prepared-candidate provenance](../Vegas/Pending/PhaseCandidateInputs.lean)
derives canonical slot equality from the public input word on arbitrary raw
histories, including rollback. These are factual transport lemmas, not a
conditional-noise or deviation-realization theorem.

The [binding-delivery adapter](../Vegas/Pending/PhaseTrafficBinding.lean)
derives candidate meanings and handler compatibility from actual raw
histories. The [environment adapter](../Vegas/Pending/PhaseTrafficEnvironment.lean)
couples both actual environment kernels and retains a successor binding frame
on every support pair, as well as focal traffic equality. Its ownership and
completion guards remain explicit. In particular, this binding frame does
not cover arbitrary differences in initial inputs.

## Checked initialization and continuation kernels

[Initialization](../Vegas/Game/SourcePhaseInitialization.lean) couples the
actual first source and raw runtime steps under arbitrary profiles using the
original setup draw. It retains the genuine extended histories on both sides.
[Initial noise factorization](../Vegas/Game/SourcePhaseInitialNoise.lean)
shows that the complete initialized focal traffic depends only on that
player's source observation, allowing a correlated original prior. This is
an initial-step statement, not a future conditional-noise theorem.

[Automatic continuation](../Vegas/Game/SourcePhaseAutomatic.lean) and its
[stopping-window consumer](../Vegas/Game/SourcePhaseAutomaticWindow.lean)
give exact original source laws through excluded-owner instructions, for
arbitrary source policies. The stopping proof rules out an earlier frontier;
it is stronger than merely identifying a fixed-length endpoint.
[Fresh normalization](../Vegas/Game/SourcePhaseNormalization.lean) applies
these laws to an actual generated source path. Its endpoint is the saved
checkpoint; a current physical cursor can be farther ahead within an
excluded prefix.

[Sample-command couplings](../Vegas/Game/SourcePhaseStep.lean) retain the
original expression draw, actual physical normalization and environment
recall. The [raw stopped sample law](../Vegas/Game/SourcePhaseSampleWindow.lean)
derives that draw's marginal for every raw profile under physical completion,
without a reserved calendar or a finite Nature assumption.
[Binding receipt kernels](../Vegas/Game/SourcePhaseBindingStep.lean) retain
the exact original install-and-close step, including final-slot rollback and
retry. These local kernels do not yet supply a joint law at every macro
boundary with all surviving information preserved.

## Source continuations after ineffective openings

[Surviving continuation](../Vegas/Game/SourcePhaseSurvivingContinuation.lean)
compares two actual source histories whose saved and live semantic states
agree and whose surviving players have the same complete source information.
Under any original source policy profile, every continuation length has the
same law of the common typed readout and declared cash vector. Excluded players
have only the automatic silent choice; no policy is required to factor through
erased private memory. The comparison uses no prior-independence or finite
Nature assumption. Arbitrary history-dependent valuation still requires the
separate observation factorization stated above.

[Ineffective disclosure continuation](../Vegas/Game/SourcePhaseDisclosureContinuation.lean)
applies this result to actual legal source steps. Replacing an intention whose
publication fails by its effective silent choice preserves the saved and live
semantic states and excludes its actor. Every remaining player's full source
information agrees, so the complete subsequent readout and cash law agrees
under the original policies. This supplies the source continuation comparison
needed by the guarded opening encoder. Matching that source step to the full
physical delivery/expiry window remains an operational obligation.

## Ordinary private inputs and permitted observations

[Private-input execution transport](../Vegas/Pending/PhaseInitialInputObservation.lean)
changes ordinary private input fields while fixing initial commitments, program
outputs, and commitment candidates. Actual response, packet inclusion, and
environment-command kernels commute with that change, including rejected
packets and the supplied leakage rule. The resulting one-step couplings have
the exact execution marginals and preserve the focal player's full permitted
traffic when its visible initial fields agree. Recall agreement is derived
from actual initialized raw histories. The arbitrary focal policy consumer
uses that player's permitted inputs, without universal pending visibility or
prior independence.

This result does not transport initial commitment values or establish the
conditional traffic-noise factorization needed for arbitrary native deviations.
Those remain separate obligations of the initialized law comparison.

## Remaining strategy obligations

The first positive policy target uses the sequential graph with maximal phase
blocks: sequential readiness orders source decisions while maximal blocks keep
the same rollback and retry rule. The existing singleton SE theorems retain
their own partitions and statements.

After a player exits, future source instructions are automatic; erased
failed-disclosure intentions still require the explicit payoff factorization
above. It is applied to the pre-audit observation. Audit deductions then change
actual receipts separately; evaluating an arbitrary valuation on already charged
receipts would not justify the assertion that charges only reduce utility.

Initialized law transport and arbitrary native deviation simulation remain
unproved. Existing `GameForm.UtilitySimulation` and
`GameForm.isεNash_of_deviation_bounds` own the Nash algebra; introducing a
certificate that merely assumes these missing facts would not prove the port.
The retained plain-contract Nash results therefore remain available.
