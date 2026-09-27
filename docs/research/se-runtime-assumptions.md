# Assumptions for sequential-equilibrium implementation

## Recommendation and claim boundary

The compiler goal keeps the ordinary source game unchanged and implements it
with an explicit inclusion, observation and settlement contract. The proof has
two strategic obligations: retained native responses implement source choices
and incentives; every raw deviation has a retained continuation with at least
as good an expected settlement. Some responses are repaired without accusation;
attributable departures supply audit evidence. The raw native game continues
to admit those additional responses. Source correspondence cannot be replaced
by a packet-shape checker.

The [roster compiler theorem](../../Vegas/Game/RevealServiceRosterCompilation.lean)
closes this route for finite reveal-only programs with initially openable
bindings. It permits repeated player visits, partial pending reads and pending
replays, with no dedicated strategic watcher. Each owner needs one visit per
event. Under protected final inclusion, authentic terminal sampling with a
positive conditional coverage bound, and collectible deposits, it preserves
standard SE and the joint typed-outcome/realized-settlement law. The retained
strategy compiler is fixed before choosing a source equilibrium; the full raw
game conclusion supplies an equilibrium extension. The finite roster remains
an explicit scheduling restriction. See the [proof and scope](se-ambient-rosters.md).

Full-source compilation additionally needs the evolving binding and guard
continuation proof and remains open. Its finite-message instance must cover
every admitted fresh commitment value. This is a genuine restriction for an
unbounded integer commitment; finite interaction alone does not imply it.
Publication types need not be finite: the checked
[candidate-value invariant](../../Vegas/Pending/ReactiveBoundedValues.lean)
covers all actual initial values and preserves the declared alphabet through
arbitrary bounded raw responses. The
[allocation theorem](../../Vegas/Pending/ReactiveBindingResources.lean)
derives a fresh unused handle at every legal active history from a capacity
at least as large as the interaction horizon.

These bounds describe the current compiler theorem. General PMF support in
upstream GameTheory removes the finite-support obstacle to countable response
menus, but does not itself remove the interaction horizon or the finite
equilibrium-completion argument. The [PMF assessment](se-pmf-interaction.md)
separates the available upstream results from those remaining proof obligations.

Interpreting source games with ambient communication remains an alternative
for environments whose extra channels cannot satisfy the audit contract.
This changes the game being preserved even when the source syntax stays the same;
it is not the claim of the ordinary-source monitored compiler.

The narrower [monitored guessing instance](se-native-pilot.md) does have a
checked native SE theorem, using the existing source syntax, full bounded raw
menus, one early communication opportunity, one partial monitoring opportunity,
and collectible receipt liability. Its costless strategic watcher supports a
reporting equilibrium by indifference. These assumptions establish forward
preservation for that game, not a general monitoring backend.

Distinguish a fixed playerwise compiler preserving every source SE from
`for every source SE, some target SE has the same initialized result law`.
A general off-path completion can depend on the opponents' source profile and
therefore establish only the second statement. Neither statement asserts that
all target equilibria reflect to source equilibria.

## What the proposed service can honestly assume

Labels: **ledger** = implementable application checks conditional on inclusion
and the chosen finality abstraction; **model** = explicit restriction of the
modeled environment; **incentive** = utility/belief hypothesis needing proof;
**setup** = additional communication or cryptographic service.

| Candidate assumption | Classification and exact limit |
| --- | --- |
| Bounded public packets and interaction count | **Model.** A finite alphabet, finite activation budget and bounded candidate supply make finite SE analysis possible. A game deadline or gas limit does not bound all pending packets or all communication before it. Enforcing admission counters bounds accepted game moves, not messages an opponent might read. |
| Binding when submitted | **Cryptographic/ideal premise.** A posted commitment must not acquire its meaning later. Binding does not imply that its author knows an opening, cannot share it, or retains exclusive signing-key control. The current ownership-based capabilities need a possession-based cryptographic refinement. |
| Partial pending observation plus public ledger | **Model with a realistic mechanism.** Ordinary nodes may see pending traffic; included transaction data is public. Using the same observation rule does not give a watchdog another player's sample. The rule, activation opportunities and correlation with later inclusion must be specified. |
| Positive probability of a timely report | **Setup/incentive.** Requires observation, retained evidence, reporting and timely inclusion, conditional on what the deviator knows. Public gossip supplies no universal quantitative lower bound. Private submission paths exist. |
| Inclusion oblivious to identity or new messages | **Service/incentive assumption.** Ethereum permits economically consequential inclusion, exclusion and ordering. Non-collusion alone does not imply a particular selection kernel. Prefer contract-checkable event authorization for ledger effects where that suffices; it does not suppress pending observations. |
| Canonical public encodings eliminate signaling | **Unproved unless concretely enforced.** Canonical parsing removes some aliases. Legal values, cryptographic coins, identifiers, timing, silence and correlations may still signal. A traffic normalizer acting before reception is a stronger **setup** than a watchdog fining afterward. |
| Signed evidence identifies the liable player | **Ledger plus liability policy.** A signature identifies an account under its key; shared keys separate account authorship from strategic control. An opening proves a candidate/value relation, not original transmission time or latest rebroadcaster. Define sending or custody liability explicitly. |
| Escrow guarantees a sanction | **Ledger**, after a valid report is included and adjudicated. The deposit must remain locked, correctly denominated in utility, and collectible at the relevant continuation. A prior forfeiture is sunk; future deterrence needs remaining collateral. |
| Interested players will enforce | **Incentive.** Compare reporting with concealment including fees, information advantages, retaliation, self-report rebates and side contracts. Being interested in winning does not automatically make reporting optimal. |

Ethereum's documentation gives signatures, nonces, arbitrary transaction data,
gas, pending pools and block inclusion; it does not certify the proposed
monitoring service. Its MEV documentation expressly discusses strategic
ordering and private submission. These are reasons to expose the assumptions,
not claims that a specific watchdog design is infeasible.
[Transactions](https://ethereum.org/developers/docs/transactions/),
[MEV](https://ethereum.org/developers/docs/mev/).
The cryptographic capability distinction is audited in
[ideal-commitment-capabilities.md](../ideal-commitment-capabilities.md).

## Minimal monitoring obligations

The following are proof obligations for a chosen backend, not an assertion
that all blockchains satisfy them:

1. **Sound admission:** every legal source deviation retains an unpenalized
   implementation. Enforce protocol conformance, not one selected strategy.
   If lawful observable support is `A`, a zero-false-positive monitor can
   detect only observations outside `A`. Changed probabilities within `A`
   remain a blind spot even when statistically distinguishable.
2. **Accountable profitable deviations:** identify a first extra behavior and
   a source-compatible replacement. Bound its conditional game-utility gain;
   establish why retained evidence proves a breach by the charged account.
   Do not replace this argument by assuming that every rejected call leaks.
3. **Conditional collection:** at each relevant information set `I`, for each
   deviation, prove a lower bound on its *additional future expected net
   charge*. A sufficient comparison is `gain(I,deviation) <= charge(I,deviation)`.
   Factoring charge as `p(I,deviation) * D(I)` requires an actual collection law.
   Positive ex ante sampling, or positivity separately for infinitely many
   deviations, does not provide a uniform finite deposit.
4. **Credible continuation:** receivers act optimally after learning evidence;
   reporters act optimally after observing violations. Use one common
   fully mixed approximation for all beliefs. Collection probabilities must
   be justified under those beliefs, including after unexpected prior acts.
5. **Observation accounting:** reports and fines can themselves reveal secrets
   or correlate later decisions. Replacing them by an expected utility charge
   requires a continuation-law argument. A charge parameter is not an
   implementation of the monitor that would collect it.

These obligations have checked pieces: observable-support deterrence,
fixed-snapshot sampling/report bounds, and SE extension for finite
sender/receiver decision games. The latter has one disclosure opportunity,
arbitrary payoffs, and explicitly completed receiver behavior; it does not
solve repeated off-path disclosure after collateral has already been lost.
See [ObservableEnforcement](../../GameTheoryExtensions/Analysis/ObservableEnforcement.lean),
[MessageMonitoringProbability](../../Interaction/MessageMonitoringProbability.lean),
and [DisclosureEnforcementEquilibrium](../../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean).

Certificate-shape checking permits ordinary matching opening certificates and
detects the checked selective-association packet. By itself it also permits
premature matching openings; the service conformance checker separately checks
the authorized phase. The shared-pad experiment shows why even
complete public packet observation need not expose signaling inside lawful
formats. These are concrete requirements for a complete protocol checker;
neither relies on an assumed external private channel.
[ReactiveConformance](../../Vegas/Pending/ReactiveConformance.lean),
[MonitoredSignaling](../../GameTheoryExtensionsTests/MonitoredSignaling.lean).

## Comparing routes

| Route | What it can buy | Main cost or limitation |
| --- | --- | --- |
| Same ambient communication in source and runtime | General strategic abstraction without promising secrecy that players can voluntarily defeat; language syntax can remain game-oriented. | Prove a concrete observation/action correspondence, including timing and evidence possession. A channel contract is still part of the semantics. |
| Watchdogs plus escrow | Ordinary-source SE extensions for games whose profitable extra behavior is detectably nonconforming and whose stakes are bounded. | Conditional reporting incentives and admission completeness; fines do not erase received information or necessarily eliminate additional equilibria. |
| Mediator, reverse firewall or threshold service | Prevent selected extra channels before observation; privately compute or release data according to a specified interface. | Stronger setup, availability and corruption assumptions. No generic blockchain implementation follows. |
| Two-player zero-sum restriction | Useful value results and a possible route from a preserved Nash law to some SE outcome implementation. | Expected value is weaker than outcome-law preservation; repair need not be a fixed playerwise compiler. Current general reactive SE bridge remains open. |

Timed or threshold recovery can remove an owner's later veto over opening;
it does not stop an owner who already knows transferable opening material
from sending it early. Boneh–Naor timed commitments expressly allow normal
opening and add forced opening under sequential-work assumptions. Keeping
the witness outside the owner changes the service and possibly the game.
[Timed Commitments, Section 2](https://www.iacr.org/archive/crypto2000/18800237/18800237.pdf),
[cryptographic future work](../cryptographic-runtime-future-work.md).

## Primary results that guide the boundary

- **Computational SE preservation:** Halpern, Pass and Seeman, Theorem 4.6
  in arXiv:1506.03030v1 (9 June 2015),
  derive computational SE from a perfect-recall source SE under their
  representation conditions. Those conditions relate histories, utilities,
  implemented strategies and feasible deviations. The conclusion uses
  computational indistinguishability and negligible approximation, not exact
  classical SE over every bit-string distinction. Their commitment example
  also shows why reverse equilibrium correspondence need not hold when players
  coordinate on revealing encodings. This is a direct future-crypto target.
  [Computational Extensive-Form Games, arXiv v1](https://arxiv.org/pdf/1506.03030v1).
  The same preservation statement is Theorem 4.5 in the
  [Cornell author PDF](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf).
- **Actual mediator elimination for SE:** Geffner–Halpern prove implementation
  of mediated `k`-resilient sequential outcomes with `n > 3k` synchronously and
  `n > 4k` asynchronously. Their authenticated communication model, secure
  computation and common consistent beliefs are substantive. The main results
  restrict outcome probabilities to rationals; asynchronous delivery is
  eventually guaranteed and need not satisfy a fixed deadline. Communication
  is present on both sides. This does not implement an arbitrary silent
  two-player source over our pending-message service.
  [Communication games, sequential equilibrium, and mediators, Sections 2–6](https://arxiv.org/html/2309.14618v3).
- **Preserve allowed communication, suppress implementation-added channels:**
  Alwen–Katz–Maurer–Zikas fix the same external resources in both worlds.
  Their collusion-preserving formulation is stronger than collusion-freeness;
  general constructions require resources providing isolation, independent
  randomness and programmability. The stated impossibilities concern their
  general functionality/resource setting, not every individual game.
  [Collusion-Preserving Computation, Sections 1–2](https://www.iacr.org/archive/crypto2012/74170124/74170124.pdf).
- **Normalization before reception:** Mironov–Stephens-Davidowitz construct
  protocol-specific reverse firewalls that modify traffic without reading
  the protected party's private state. Their security/exfiltration definitions
  show what a stronger normalizing service can promise. Mere canonical
  serialization or post hoc inspection is not such a construction; an SE
  implementation theorem remains a separate obligation.
  [Cryptographic Reverse Firewalls, Sections 1–2](https://www.iacr.org/archive/eurocrypt2015/90560152/90560152.pdf).
- **Interested enforcers require a coalition model:** Kelkar et al. study
  provable whistleblowing and colluders' enforceable retaliation contracts.
  Their impossibility and conditional positive results rule out treating a
  bounty as unconditional honesty. We have not instantiated their financial
  assumptions or proved reporter equilibrium here.
  [Breaking Omertà](https://eprint.iacr.org/2025/1582).

## Future work: reducing channel value

Batching, shuffling, fixed fees and canonical fields may reduce particular
signaling opportunities. Ledger batching does not erase earlier pending
observations; normalizing one field leaves other permitted choices, including
cryptographic randomness, unless normalization precedes reception. Noise need
not make channel capacity zero, as Shannon's noisy-channel analysis shows.
[A Mathematical Theory of Communication, Sections 12–13](https://people.math.harvard.edu/~ctm/home/text/others/shannon/entropy/entropy.pdf).
A cost-free increase from 50% to 55% correct guessing is still profitable for
a player rewarded for accuracy. A promising future route combines bounded
utility, communication/checking costs or strict incentive margins with
quantitative information bounds. Exact SE requires conditional incentive
bounds at every relevant information set, including rare ones; an average
noise or mutual-information bound alone supplies no such result. An
approximate-SE bridge from these bounds remains future work.

## Remaining end-to-end obligations

The target is the full existing source syntax with an explicit bounded service
and audit contract. The reveal-only capstone is a completed fragment of that
objective. The remaining proof obligations are:

1. **Binding opportunities.** Repeated owner activations before inclusion must
   allow waiting before the first binding and forbid a second fresh binding.
   A submission becomes required at the final owner opportunity. Early silence
   is not evidence of a missed deadline. The checked
   [required-choice timing laws](../../GameTheoryExtensions/Math/Probability/DeferredChoice.lean)
   assign positive waiting probability before the final slot, force submission
   there, and recover the exact chosen first-submission distribution. The
   [service menu](../../Vegas/Game/SourceServiceMenu.lean) selects the required
   binding set exactly at the last unsent owner opportunity. The actual
   compiler policy must still realize the timing laws throughout a full run.
2. **Full source execution.** Compose actual sample, binding and guarded
   disclosure phases across arbitrary finite reaction rosters. The
   [source checkpoint](../../Vegas/Game/SourceServiceCheckpoint.lean) and
   [prefix decoder](../../Vegas/Game/SourceServicePrefix.lean) retain the
   evolving accepted bindings, source configuration and deferred guard registry;
   their constructor proofs do not by themselves establish the complete run.
   [Delayed binding inclusion](../../Vegas/Pending/ReactiveBindingReplay.lean)
   permits arbitrary intervening retained responses after submission and proves
   the same application, ledger and receipt result as immediate inclusion.
   The [complete binding phase](../../Vegas/Game/SourceServiceBindingPhase.lean)
   now starts before the first roster visit: the actual limiting source policy
   waits, submits at its final owner opportunity, and preserves the original
   typed commitment law through the remaining roster and reserved inclusion.
   Its [supported endpoint theorem](../../Vegas/Game/SourceServiceBindingCheckpoint.lean)
   also carries the semantic source successor and the evolving candidate and
   accepted-handle catalogues through that entire phase. It preserves canonical
   allocation, restores the serial/ledger counts, and proves all pending and
   known copies published at the completed boundary. The
   [boundary invariant](../../Vegas/Game/SourceServiceBoundary.lean) combines
   those facts with actual response counts, future-event recall, source store
   agreement and deadline accounting. Initialization, grant, passive activation
   and general service invariant preservation are checked. The
   [retained binding support](../../Vegas/Game/SourceServiceBindingSupport.lean)
   theorem covers every legal retained policy, including early typed submissions:
   every supported completed roster has an actual first-binding witness and
   immediate-inclusion provenance. The required final menu rules out all-wait
   paths. The [complete binding boundary](../../Vegas/Game/SourceServiceBindingBoundary.lean)
   carries every such retained policy through grant, the whole roster,
   reserved inclusion and expiry to the next typed source successor. This
   includes the dynamic allocator, all copy locations, future-event recall,
   serial accounting and the next event's timing. The
   [guarded disclosure phase](../../Vegas/Game/SourceServiceDisclosurePhase.lean)
   proves the actual limiting source policy's complete roster law, including
   failed deferred guards, withholding and the replay choices used by its
   silent branch. The all-syntax fold and support theorem for every retained
   history still need composition across event constructors.
3. **Conditional incentives.** Derive the native information-fiber likelihood
   from those actual executions, including dynamic candidate catalogs and
   extra response recall. When failed disclosure and withholding both produce
   silence, use the
   [conditional private-history law](../../Vegas/Game/SourceServiceDisclosureMemory.lean)
   and a common mixture of original source assessment comparisons. Native
   observations determining a source view is weaker than posterior equality.
   [Candidate reconstruction](../../Vegas/Game/SourceServiceCandidateObservation.lean)
   removes an assumed private catalog correspondence, using the source view
   and the coupled public and own-response records instead. Deriving that
   joint coupling and its conditional likelihood remains necessary.
   The [binding-window likelihood](../../Vegas/Pending/ReactiveBindingLikelihood.lean)
   and [conditional law](../../Vegas/Pending/ReactiveBindingPosterior.lean)
   prove that an actual opaque submission, replay roster and reserved inclusion
   convey no further private-result information to a foreign player, conditional
   on the initial auxiliary readout. This includes the actual pending pool,
   passive samples and focal recall. The auxiliary projection excludes other
   players' private response parameters without removing them from the runtime.
   The full-source likelihood fold must still establish its relation to the
   source information sets and include the timing before first submission.
   [Scheduled binding](../../Vegas/Pending/ReactiveBindingSchedule.lean) extends
   the foreign-readout equality to the entire roster and protected inclusion,
   including an actual behavioral mixture over submission opportunities.
   Its timing distribution is shared across private values. Relating that law
   to the complete source assessment remains part of the full-source fold.
   The coupling covers the owner as well when the owner's source-visible
   binding result agrees; it does not claim that owners forget their choices.
   The [opening likelihood](../../Vegas/Pending/ReactiveOpeningLikelihood.lean)
   uses the same focal readout through actual opening windows, reserved inclusion
   and clock/expiry tails. It therefore permits foreign private binding responses
   to differ while retaining their true runtime recall. It requires the actual
   handler-result views to agree; composing these phase laws across the entire
   program remains necessary.
   The [source memory factorization](../../Vegas/Game/SourceServiceFactorization.lean)
   derives initialization and binding constructors from actual service laws,
   retains the original private-intention history through guarded disclosure,
   and discharges the successful opening handler-view comparison. These are
   constructor results; no complete-program posterior equality is assumed
   or yet concluded.
   The [public-sample constructor](../../Vegas/Game/SourceServiceSampleFactorization.lean)
   derives the actual sampling instruction's traffic law from the source
   distribution and preserves the joint effective/original source-memory
   factorization. Its [native likelihood law](../../Vegas/Pending/ReactiveSampleLikelihood.lean)
   couples the public draw while retaining actual scheduler observations and
   the focal player's recall.
4. **Raw deviations and settlement.** Finish the remaining-plan coupling to a
   legal retained continuation until the first attributable departure. Hidden
   unusability requires repair; it cannot be detected by a sound public audit.
   Publicly missing obligations require deadline evidence. Compose the stopped
   comparison with authentic partial terminal sampling and collectible deposits,
   preserving the joint initial-type/public-outcome/realized-settlement law.
   The [repair frame](../../Vegas/Pending/ReactiveBindingSubmissionFrame.lean)
   now holds at submission, before any inclusion. Its
   [parameter/public-outcome readout](../../Vegas/Game/BindingRepairReadout.lean)
   gives exact base-utility equality while the frame holds. The
   [serial evidence](../../Vegas/Pending/ReactiveSubmissionSerial.lean)
   connects first-event recall to the public next-envelope serial during a
   clean single-event phase, without requiring complete pending observation.
   Fresh submission followed by inclusion restores the baseline serial/ledger
   equality, including rejected application calls; arbitrary later replay
   affects neither counter. This accounting is checked in the same generic
   [serial module](../../Interaction/ReactiveSubmissionSerial.lean).
   The [public phase checker](../../Vegas/Pending/ReactiveServiceConformance.lean)
   admits the first canonical opaque binding, independently of hidden material,
   and the current certified opening whose public guards succeed. Its phase
   classification supplies the packet branches; the stopped whole-run proof
   must still derive its evidence and collection probability.
   [Local soundness](../../Vegas/Pending/ReactiveServiceSoundness.lean) proves
   that all ordinary retained binding, guarded-resolution and foreign-player
   choices pass this checker under their operational phase facts. The result
   covers arbitrary retained choices, not just the selected source profile.
   Published boundaries establish network conformance; passive observation and
   conforming responses preserve it, including known pending-envelope replays.
   [Disclosure-window conformance](../../Vegas/Pending/ReactiveResolutionWindowConformance.lean)
   preserves the serial test and the actual phase-stamped traffic records
   through every retained roster, including early opening and pending replay.
   [Disclosure-window support](../../Vegas/Pending/ReactiveResolutionWindowSupport.lean)
   proves that the reserved inclusion restores publication of every pending,
   known and remembered envelope, also when the player withholds throughout.
   Establishing and composing the full phase boundaries on every retained
   history remains part of the support induction.
   The [opening classifier](../../Vegas/Pending/ReactiveServiceOpening.lean)
   derives actual successful inclusion and the precise guard-aware response
   from public conformance and the runtime's evidence and binding invariants.
   A failed original binding cannot produce a conforming fresh opening.
   The [binding audit step](../../Vegas/Pending/ReactiveBindingAuditStep.lean)
   couples arbitrary effective binding responses and their actual passive
   activation to the retained implementation, preserving either the repair
   frame or an attributed rejected traffic record. The
   [guarded-resolution audit step](../../Vegas/Pending/ReactiveResolutionAuditStep.lean)
   proves the same actual mixed-response and passive-activation split for
   disclosures, using authentic evidence and arbitrary deferred guards. Once
   a first submission has already consumed the next public serial, the
   [repeat-submission step](../../Vegas/Pending/ReactiveRepeatedSubmissionStep.lean)
   gives the corresponding split without requiring a fresh candidate:
   transport preserves the repair frame; any fresh submission supplies an
   actual rejected record. The
   [required final response](../../Vegas/Pending/ReactiveBindingRequiredStep.lean)
   additionally covers silence or replay at the last binding opportunity:
   [actual omission](../../Vegas/Pending/ReactiveBindingFinalOmission.lean)
   is proved after the complete foreign tail, reserved inclusion and expiry.
   The [good binding block](../../Vegas/Pending/ReactiveBindingForeignInclusion.lean)
   carries the repair frame through that same complete suffix for usable,
   missing or mistyped private material. Foreign responses may be arbitrary;
   the proof uses authenticated authorship, not assumed opponent conformance.
   The [required final block](../../Vegas/Pending/ReactiveBindingFinalBlock.lean)
   combines the actual mixed final response with the entire foreign tail and
   settlement: its exact coupling yields either the repair frame, a persistent
   rejected record, or the actual missed-binding obligation. Whole-program
   stopped composition and legal repaired-history support remain
   open. The
   [physical continuation](../../Interaction/ReactiveTrafficContinuation.lean)
   and [service-plan persistence](../../Vegas/Pending/ReactiveServiceTraffic.lean)
   retain such records through arbitrary later responses and instructions.
   Sampling and collection remain separate service obligations; evidence
   persistence does not turn an unauthenticated or unseen record into a charge.
   Given uniform per-record sampling coverage, the physical service-plan
   theorem derives the conditional collection lower bound for every remaining
   plan and player policy, even when sampling depends on the final transcript.
   The [terminal comparison](../../GameTheoryExtensions/Analysis/Protocol/TerminalAuditCoupling.lean)
   turns a coupled execution law into an inequality between actual randomized
   settlements when the bounded departure gain is covered by incremental
   collection. It does not construct the coupling or the audit coverage.

The compiler must fix its service, alphabet, conformance rules and deposit
before selecting an equilibrium. No source-level flag for a backend mechanism
or assumed strategic correspondence discharges these obligations.

All current unilateral-SE conclusions remain distinct from CE or coalition
preservation. Shared recommendations, keys, witnesses, side payments and
jointly controlled reporters alter the deviation class. Zero-sum value
invariance or a unilateral fine calculation does not discharge those cases.
Miner/validator participation and Ethereum deployment feasibility are deferred
economic/engineering questions; this audit supplies no deployment guarantee.
