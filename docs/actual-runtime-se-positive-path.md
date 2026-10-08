# A positive SE path through the actual Vegas runtime

Analysis by Codex. The useful positive direction is a faithful sequential
service with public traffic, followed by enforcement of departures from that
service. Pending packets need not be invisible. The unresolved part is proving
that the actual asynchronous service is faithful at information sets, including
unreached ones, rather than merely matching initialized terminal outcomes.

This analysis does not change the asynchronous target, checklist, or semantics.

## What already applies to the runtime

The checked theorem
`SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved` in
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean) starts
with an arbitrary SE of the original full source game. It concludes existence
of an SE of the bounded raw native runtime with the same joint terminal law of
the typed source outcome and realized payoff. It chooses the service, backend,
and deposits before the source equilibrium. Initialized target play collects
no deposit.

This is an actual runtime theorem, with a restrictive scheduler. Events run
sequentially, each has a fixed activation roster, and its phase ends with
inclusion of the owner's selected packet or execution of its chance event.
The remaining clock and expiry instructions finish that event before the next
phase. Arbitrary passive pending-message observations and public network
policies are admitted inside this service. The scheduler is allowed to see
public pending packets; the theorem does not hide their existence or payloads.
The phase-ending inclusion instruction is a guaranteed service operation, not
a probabilistic promise of eventual L1 inclusion.

The genuine extension beyond that service is also partly checked.
`AsyncServiceSpec.risk_sequentialEquilibrium_extends` in
[SourceServiceRiskExtension](../Vegas/Game/SourceServiceRiskExtension.lean)
extends an SE of the actual asynchronous risk menu into the effective raw
runtime. Its audit estimates use actual runtime evidence and the stipulated
delivery service. Its comparators can settle a fresh lawful call under the
actual asynchronous contract. However, its source equilibrium is an equilibrium
of the **risk menu**, not yet an arbitrary original-language equilibrium.

Consequently, composing that result with an assumed risk-menu consistency or
comparison certificate does not settle source preservation. The certificate
is exactly where the missing source-information proof can reside. The current
owning layers do not provide that proof for every `AsyncServiceSpec`.

## Why public pending reveals can be harmless

There are two different disclosure problems.

A canonical binding submission carries a commitment handle in the public
packet. Its private preparation contains the binding value. Changing that value
does not change the public packet or network. This is an ideal commitment
interface already present in Vegas, not a claim that an unencrypted value sent
over a real network becomes invisible. A concrete cryptographic realization
would need to justify that idealization at its own security level.

A canonical opening contains the raw value, and pending observers may read it
before inclusion. In sequential mode, the next source event cannot become
ready before the current event completes. During a protected reveal phase,
therefore, no later source choice intervenes between seeing the opening in the
mempool and its successful logical publication. Observers may be activated,
but a faithful retained interface gives them only transport or bookkeeping
responses during that interval. If the opening is guaranteed to settle in time,
its early visibility gives no extra information at the next meaningful source
decision: the source view there already contains that public revelation.

This argument requires both successful protected settlement and decision order.
If an opening can be dropped and the event can finish as a failed publication,
the observer has learned a value that the source failure branch does not reveal.
If another logical decision is permitted before settlement, the observer can
use the early value at that decision. Neither situation is repaired merely by
calling the reveal a non-message.

Thus sealed-until-ordered openings are one possible runtime facility. They are
not necessary for the sequential protected service. Its alternative is to
serialize meaningful choices and guarantee settlement of legitimate openings.
This does not require suppressing physically visible traffic.

## A close runtime model with stochastic scheduling

A useful next positive target is a **bounded public phase service**, implemented
using the existing reactive application rather than a different message model.
The following describes a concrete constructor to verify; it is not a theorem
about an arbitrary scheduler satisfying only `AsyncContract`.

1. Use the sequential event graph. A finite public controller maintains the
   current event and a finite remaining phase budget. Its state and random
   scheduling results are observable. It may insert bounded waits and vary
   inclusion timing. Every branch finishes the current phase before enabling
   the next event's meaningful decisions.
2. A phase has publicly specified finite activation opportunities. The retained
   client interface offers the same logical source choices as the existing
   source-service menu. It may retain its existing early submission or deferral
   choices, but does not add new message contents, public aliases, or a new
   admission lottery for legitimate source actions.
3. Every legitimate submission allowed by that menu is included while it is
   acceptable and before expiry. The controller's budgets and deadlines must
   make this true on every legal retained branch. Publication withholding is
   still the source choice, handled by the same logical failure transition;
   network loss of a legitimate publication is not a second failure mechanism.
4. Primitive controller kernels use public execution inputs only: the public
   source prefix, controller state, public packet envelopes, and prior public
   scheduling results. Canonical commitment handles are selected by the
   existing public slot convention. Private candidate meanings, private source
   cells, and private preparation fields are not controller inputs.
5. Primitive leak kernels use the actual pending packets. They may reveal the
   entire opening packet. Their sampling randomness has finite support and
   obeys the existing native observation rules. No pending-invisibility premise
   is added.
6. Terminal utility depends on the typed source outcome as in the present
   theorem. If fees or physical delay also affect utility, their effects must
   be incorporated in the source or proved compatible with the lifted choices.
   Random scheduling is not automatically payoff-neutral in such a model.

The clean service can have random, adaptive phase duration. A worst-case bound
and reserved inclusion capacity are service assumptions. Such assumptions
describe an ideal bounded-latency ledger or application sequencer. They are
stronger than saying an ordinary public-mempool transaction is usually included.
The distinction is necessary for an exact theorem.

**Candidate preservation statement.** For this constructor, every original
source SE should have an SE of the retained phase service preserving the typed
terminal law. Subject to sound actual evidence and a uniform positive collection
bound for excluded raw departures, a finite deposit vector fixed before the
source SE should extend that assessment to the raw native runtime and preserve
the joint outcome and realized-settlement law.

The second edge follows from the existing enforcement machinery once its
runtime adapters are supplied. The first edge remains a candidate for this
constructor. The general public-chance expansion has a
[paper proof](public-scheduling-se-preservation.md), but applying it here must
also handle the client timing choices already present in the service menu.
Those are player decisions, not scheduler chance moves. Their local comparisons
and their effect on source consistency sequences must be proved separately.

## The two substantive missing inductions

For source information set I, a native site generally contains extra traffic,
clock, and activation history. The existing theorem
`SourcePrefixCheckpoint.source_view_eq_of_observe_eq` in
[SourceServicePrefixInformation](../Vegas/Game/SourceServicePrefixInformation.lean)
proves that native information determines the source view. It does not prove
that the extra observation has the same likelihood across hidden histories in I.
That latter fact is needed for transporting off-path Bayes limits.

The first missing induction must start from the controller's primitive kernels
and the actual packet transformations. For a selected lift of fully mixed
source profiles, it should factor the native prefix law into the source prefix
law and an observation-local traffic kernel. Hidden commitment values must not
change the public scheduling likelihood. Earlier opening values may change it,
but only after they belong to the recoverable public source prefix of the next
meaningful decision. Client timing trembles must be chosen independently of
hidden source values, with sufficiently fast vanishing errors where required.

This is more than an initialized outcome coupling. It must cover every legal
native decision reached by the selected fully mixed sequence, including late
activation and initially unreached source sites. Conditioning on a rare site
can amplify small unconditional errors; convergence of initialized traces does
not by itself control that effect.

The second induction must compare every retained local action at those sites.
Choosing another logical source action must have its corresponding source
continuation law. Choosing another permitted timing must have the same law or
a vanishing local comparison error along the selected sequence. Otherwise a
player may exploit a timing signal or inclusion probability even when the
intended initialized profile ignores timing. Consistent completion must then
optimize the genuinely new raw sites. It cannot prescribe perpetual compliance
after an earlier violation makes a charge inevitable.

Several primitive pieces already exist and should be reused:

- [ReactiveBindingObservation](../Vegas/Pending/ReactiveBindingObservation.lean)
  proves equality of the pending networks and foreign observations for different
  privately prepared canonical binding values.
- [ReactiveBindingFrameRounds](../Vegas/Pending/ReactiveBindingFrameRounds.lean)
  gives public-scheduler round and multi-round coupling during transport
  windows. The scheduler sees the same actual public input in paired states.
  These are useful local noninterference facts, not yet a whole-game SE adapter.
- [SourceServicePrefixFactorization](../Vegas/Game/SourceServicePrefixFactorization.lean)
  supplies the multi-phase observation-local factorization for the checked
  calendar. It includes dynamic bindings, reveals, source sampling, and timing
  mixtures; a broader controller needs an extension of these phase inductions.
- [SourceServiceAsyncTimeliness](../Vegas/Game/SourceServiceAsyncTimeliness.lean)
  proves settlement of a fresh acceptable protected call under the actual
  asynchronous contract against arbitrary other responses.
- [SourceServiceRiskExtension](../Vegas/Game/SourceServiceRiskExtension.lean)
  already performs the risk-menu-to-raw equilibrium extension. Its evidence
  collection and completion should be instantiated, not replaced by an assumed
  equilibrium or by assumed posterior equality.

Adding a wrapper around any one of these results would not close the missing
source-to-service edge. The next checked result should be a phase-controller
prefix factorization or a source-to-risk-menu assessment construction under
explicit controller premises.

The concrete
[CommittedResolutionReadout](../Vegas/Examples/CommittedResolutionReadout.lean)
leaf supplies a further checked operational comparator ingredient. At every
legal RAW history, for any observation-local scheduler and horizon, Bob's
initialized binding retains its accepted handle and TRUE meaning. Every
successful Bob publication is therefore TRUE, and every accepted Bob opening
identifies that same handle and value. These statements apply to the
deterministic late-recovery controller as well as the original controller.
They permit arbitrary alias submissions and preparations; they do not assert
that publication succeeds or that an equilibrium preserves the source law.

The subsequent
[CommittedResolutionBobService](../Vegas/Examples/CommittedResolutionBobService.lean)
leaf checks a successful continuation comparator on the actual recovery
controller. After every legal RAW prefix at Bob's activation, his canonical
TRUE response is accepted by the actual next scheduler round with probability
one. It yields the TRUE publication, an accepting receipt, and a permitted
packet verdict. Earlier Alice choices are unrestricted. An accepted packet
remains permitted at every later settled record retaining that receipt.
The owning fixture's `bob_activation_phase` supplies the ready, timely phase
fact from its existing all-history scheduling proof. This is a concrete
ingredient for proving that every target SE selects Bob's successful logical
publication when his failure forfeit dominates the base payoff range. The
whole-continuation utility comparison and resulting SE outcome theorem still
need to be assembled; the operational comparator does not assert them.

## The exact-law boundary

Suppose a legitimate action has positive probability of an unrecovered runtime
failure before the fixed horizon. Take a source game with a unique desired
terminal typed outcome and no source chance failure. If that runtime failure
produces a different typed outcome, the target law cannot equal the source law.
Collecting a deposit changes payoffs, not the missing typed outcome. This is an
outcome-realization obstruction before sequential-equilibrium consistency is
even considered.

Accordingly, an exact arbitrary-source theorem needs guaranteed clean execution,
a recovery mechanism that really produces the same source outcome, or a source
semantics exposing the relevant runtime failure. For a finite-horizon ledger
with positive unrecovered legitimate-message loss, approximation is the natural
alternative. An outcome-distance estimate alone still does not establish an
approximate sequential-equilibrium theorem: conditional errors at rare
information sets need their own control.

The strongest positive claim justified for the actual implementation today is
the checked audited raw calendar theorem. The most direct realistic extension
is a bounded, public, sequential phase service with guaranteed legitimate
settlement and actual penalties for departures. Arbitrary `AsyncServiceSpec`
preservation remains open at its source-information adapter, even though its
risk-menu enforcement edge is already checked.

## A useful fully public one-phase calculation

For a fixed-value opening phase, full visibility can remove the selection
mechanism of the asymmetric late-opening counterexample. Here is the precise
calculation, rather than a general conclusion about every asynchronous game.
Assume base continuation payoffs lie in `[L,U]`, with width `B=U-L`, and
unsuccessful publication incurs one deterministic forfeit `D`. At a final late
opportunity, sending succeeds with probability `q`; if it fails, the recipient
sees the emitted opening. Never sending incurs the same forfeit. There are no
additional timing fees in this calculation.

If `q <= 1-B/D`, every send payoff is bounded by

```
U - (1-q)D <= L.
```

It therefore cannot improve on a protected continuation paying at least `L`,
regardless of the recipient's responses. Conversely, the difference between
sending and never sending is at least

```
[L-(1-q)D] - [U-D] = qD-B.
```

Thus, if `D>2B`, every potentially profitable late probability satisfies
`qD>B`, and every hidden type strictly sends at that final opportunity. This
supplies a common completion at the dangerous high-reliability end. It does
not say that every type sends at every low-probability opportunity.

If successful continuation payoffs `S_theta` and emitted-failure continuation
payoffs `F_theta` are the same across timing options, then

```
V_theta(j) = q_j S_theta + (1-q_j)(F_theta-D).
```

For $D>B$, every type ranks these options by $q_j$. One can select the most
reliable option independently of hidden preferences and avoid timing-induced
selection among those preferences. A choice may depend on the opened value
when that value is subsequently part of the successful source observation.

These bounds, the common-continuation strict ranking, and existence of a
uniform finite reliability-gap forfeit are checked in
[DisclosureReliability](../GameTheoryExtensions/Analysis/DisclosureReliability.lean).
They identify a promising route to a general proof, but their continuation
hypotheses are substantive. Several
attempts, recovery, and previously incurred forfeits can create different
continuation games after different failures. A finite list of primitive
reliability values has a positive minimum gap between distinct values, so
sufficiently large $D$ can overwhelm bounded payoff differences between them.
This does not give a uniform gap across arbitrary behavioral profiles:
opponents' mixed actions can induce continuously varying inclusion probabilities.
Equal-reliability
options do not have such a gap: their forfeit terms cancel. Also, at a late
binding decision, different private binding values may have identical success
probability. The forfeit then does not control their relative incentives.

A general source-to-service proof must handle those ties and private logical
choices using actual continuation and belief transport. Full pending visibility
and a large forfeit, taken alone, do not yet supply that argument. No actual
runtime counterexample to that proposed stronger combination is established
here either.

For the fixed immutable-value, single-phase game, the
[full-public disclosure analysis](full-public-disclosure-phase-preservation.md)
gives a stronger paper preservation theorem. It needs only $D>B$, arbitrary
receiver failure preferences, and any finite number of late opportunities
with type-independent inclusion probabilities, including zero and one. A finite
auxiliary game chooses a rational no-emission belief;
calibrated type-dependent root trembles preserve the original posterior at all
emitted sites, including types that never emit in the limiting continuation.
The `D>2B` calculation above is a useful robust margin, not a necessary
condition for that theorem. Its assembly into the actual runtime remains open.

## Availability in the broader positive conjecture

The proposed source-to-service extension concerns the intended source model
with its existing well-formedness and guard-satisfiability hypotheses. It needs
lawful TRUE continuations that actually succeed at the relevant source sites.
The binding menus predicted by the guards and the `GuardsSatisfiableFrom`
assumptions are substantive parts of this premise. A forfeit larger than the
base payoff range cannot create an opening that the source rules make
unavailable. In particular, a guarded reveal can fail despite a truthful TRUE
choice, and an initially failed binding can be unopenable.

For that intended model, a possible construction is to preserve the initialized
source outcome while freely completing dirty runtime branches, rather than
requiring every source off-path belief and response to survive verbatim. Public
metadata that leaves the logical source choice unchanged may admit a pooling
completion. The finite disclosure-phase proof supplies evidence for this
construction, not a general theorem. Across several phases, the single
consistency sequence must respect the private information available to each
sender; it cannot calibrate root probabilities using hidden states that sender
does not observe. Public scheduling likelihoods must also admit transport
conditional on the legitimately revealed logical view.
