# SE compilation stack and implementation plan

## Objective and status

The [fixed proof checklist](se-proof-checklist.md) tracks theorem-level
completion. Supporting lemmas belong to its existing obligations; they do not
close an obligation until its full statement is proved.

Implement a source-to-native sequential-equilibrium theorem for a reusable
class of VegasCore programs, with all bounded raw responses available in the
final game. Fix the program, service, monitoring rule, utilities and deposits
before selecting an equilibrium. Preserve the joint initial-type, public-result
and actual net-payoff law of **every source SE**.

### Checked end-to-end scope

The [general-roster revelation theorem](../Vegas/Game/RevealServiceRosterCompilation.lean)
preserves every source SE for reveal-only programs with openable initial
bindings. Each actor has at least one visit at its event; arbitrary additional
finite roster visits, passive partial observations, replay and source
withholding remain available. Authentic signed phase evidence, positive
conditional monitoring coverage and collectible deposits are explicit service
assumptions. The conclusion is existence of a bounded raw-runtime SE with the
same joint typed source outcome and actual settlement law.

The full language has checked
[initialized execution laws](../Vegas/Game/SourceServiceLaw.lean) and
[settlement laws](../Vegas/Game/SourceServiceAudit.lean) for every admitted
compiled profile, including fresh bindings, chance, correlated private inputs
and guarded disclosure. Its
[source-to-permitted-runtime SE theorem](../Vegas/Game/SourceServiceEquilibrium.lean)
is checked. The permitted-to-full-runtime SE extension is checked, including actual
conditional incentives, off-path completion and raw response aliases. Their
[composition](../Vegas/Game/SourceServiceCompilation.lean) preserves every
source SE of the full language in the audited bounded raw runtime, for programs
whose commitment payload types are finite, with the joint law of the typed
terminal state and realized settlement and no charge on the equilibrium's
paths.

### Assumptions of the full-language theorem

`Vegas.Paper.source_audited_raw_sequential_equilibrium` has the following
hypotheses and modeling choices. The first column says what the theorem
requires, the second what it is used for in the proof, and the third why it is
reasonable and what it leaves outside the claim.

| Assumption | Mathematical role | Justification and impact |
| --- | --- | --- |
| Finite response interface (`SourceServiceSpec.values`, `SourceServiceSpec.initialValues`, `SourceServiceSpec.capacity`) | Every source binding value and supported initial binding table has a native message form and a candidate slot, so the native game is finite and implements every source choice. | Declared once for the service. Every commitment payload type must be finite, so a program committing integers is outside this theorem; the Nash-level theorems do not need this. |
| Bounded interaction (`SourceServiceSpec.rosters`, `SourceServiceSpec.opportunities`) | Finite activation rosters give a bounded native horizon; each actor has an activation at its own event. | Rosters may add arbitrary finite extra visits and passive observation. Unbounded interaction and PMF-valued traffic are separate refinements. |
| Protected service | The modeled runtime includes each submission at most once and completes events at their deadlines; public binding omissions are attributable. The delivery and ordering environment is not a player. | A property of the service being modeled, not a hypothesis of the theorem. No ledger provides it outright: a block producer paid to delay an opening past its deadline turns a prescribed action into a failure, and payoffs that reward an opponent's failure make such bribes worthwhile. Censorship and a strategic sequencer are outside the claim. |
| Authentic partial audit (`authentic`) | Sampled evidence is a subset of actual traffic, so the audit charges no permitted history. | Missing records are never evidence. Authenticating phase and prior-ledger context remains an oracle obligation beyond signatures. A record carries the phase at which a message was transmitted, including a third party's replay, and is attributed to its author, so a late replay of a pending envelope is charged to that author; the protected service keeps prescribed traffic clear of this. |
| Positive conditional coverage (`positive`, `coverage`) | Each forbidden record of a player is sampled with at least a fixed positive probability, so a fixed deposit deters every first departure. | The rate is a property of the audit backend; independent per-record sampling achieves it, and a complete audit gives rate one (`SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved`). It covers messages that are never included, which no mempool observer guarantees, and it presupposes closed communication: an opening handed to an opponent through an unaudited channel or an unregistered account is verifiable and invisible to the audit. |
| Collectible fixed deposits (`rosterAuditDeposit`) | Settlement subtracts a deposit fixed from the finite payoff range before an equilibrium is chosen. The range is taken over all native histories, where an unfinished history counts as zero. | Collectibility is an interpretation of the settlement utility: utilities are quasi-linear in money, forfeited deposits are burned, and one charge covers all of a player's violations. No escrow implementation is proved. The deposit scales as range/p. |
| Utility of initial parameters and public outcome | The source utility is the raw utility evaluated on the typed source readout, invariant under private response normalization. | Utilities that read repaired private future values are outside the claim. |
| Public chance | A sample draws exactly from its kernel, conditional on the preceding execution, and players cannot withhold or replace the draw. | A realization needs a randomness beacon that players cannot predict or bias, read after the draw's inputs are final; players' own commit–reveal and block hashes do not qualify. With bounded randomness only dyadic weights are exact. |
| Final inclusion | An included message stays included. | Reorganizations before finality are outside the model; a reorganized grant would make lawful messages look forbidden to the audit. |
| Complete play | Both sequential equilibria and both joint laws are of terminal play. The source instruction bound and the native fuel certify termination (`Vegas.SourceServiceSpec.sourceTerminates`, `Vegas.SourceServiceSpec.rawTerminates`). | Standard sequential equilibrium; no step count enters the statement. |

The theorem asserts no cryptographic or EVM refinement: commitments are ideal,
and signed evidence is attributed to accounts, not to physical senders.

### Source beliefs and sequential incentives

The actual compiler policy implements the full source program on the existing
runtime. [Timed policies](../Vegas/Game/SourceServiceTimedPolicy.lean) choose
an owner opportunity using a common timing law and select the source action
there; this introduces no represented private scratch state. The
[timed binding phase](../Vegas/Game/SourceServiceTimedBinding.lean) and
[guarded disclosure phase](../Vegas/Game/SourceServiceTimedDisclosure.lean), and
[public sampling phase](../Vegas/Game/SourceServiceTimedSample.lean) have
exact laws retaining the whole native execution. The
[whole-prefix factorization](../Vegas/Game/SourceServicePrefixFactorization.lean)
proves the joint decoded-state and native-traffic law at every event boundary
for the full language. The [actual owner posteriors](../Vegas/Game/SourceServiceBayes.lean)
and [original-assessment comparison](../Vegas/Game/SourceServiceAssessment.lean)
connect every owner visit to the original source assessment, including private
intentions erased by normalization. The
[local comparison interface](../Vegas/Game/SourceServiceLocalComparison.lean)
reduces every physical local comparison to the configuration law of the
current phase after each legal response. Public-sampling sites, foreign visits,
owner visits after a recorded binding or opening, and unsent owner bindings are
checked, as are unsent owner disclosures with and without an available
opening. The
[joint phase checkpoint laws](../Vegas/Game/SourceServiceTimedCheckpoint.lean)
retain each chosen source successor together with its actual native traffic;
equal terminal marginals do not establish that joint law.

[Source choice completion](../Vegas/Game/SourceChoiceCompletion.lean) extends
one original Bayes sequence at abstract views outside actual decision sites.
It preserves all actual continuation laws and the original assessment limit.
The required finite choices follow from existing binding-value coverage;
normalization then supports every effective source choice. This supplies a
source support fact. The
[actual decision support theorem](../Vegas/Game/SourceServiceLocalSupport.lean)
then proves that every permitted physical response is a replay alias or is
supported by the actual source policy. The
[native full-mixing theorem](../Vegas/Game/SourceServiceTimedMixing.lean) and
the [supported source sequence](../Vegas/Game/SourceServiceChoiceSupport.lean)
are checked for the full language. A consistent assessment need not be
rational, so belief correspondence and local incentives are separate proofs.
The [initialized timed law](../Vegas/Game/SourceServiceTimedLaw.lean) identifies
every actual native approximant's outcome law with its original finite source
strategy. The [timed continuation law](../Vegas/Game/SourceServiceTimedContinuation.lean)
derives the whole typed source continuation from any supported native phase
boundary. The local response comparisons connect those boundary laws to the
actual intermediate choices.

The active [binding law](../Vegas/Game/SourceServiceActiveBindingLaw.lean) and
[binding checkpoint](../Vegas/Game/SourceServiceActiveBindingCheckpoint.lean)
start after the current passive observation has occurred; binding excludes
passed opportunities when no binding was submitted. The
[available-opening laws](../Vegas/Game/SourceServiceAvailableOpening.lean)
retain disclosure timing opportunities that passed with a silent source
choice. The
[local source policy theorem](../Vegas/Game/SourceLocalPolicy.lean) realizes an
arbitrary one-site choice law as one admitted syntactic policy shared by all
hidden histories at that observation, followed by the baseline continuation.

The checked [conditional-regret bound](../GameTheoryExtensions/Math/Probability/DeferredChoice.lean)
divides original binary regret by a positive lower bound on remaining timing
mass. A fixed half-uniform, half-final timing law has remaining mass at least
one half at every owner opportunity, by
[rosterTiming_prefix_le](../Vegas/Game/RevealServiceRosterTiming.lean).
Thus a factor of two suffices for the binary comparison once its physical
continuation laws are established. This is a choice of implementing strategy;
the permitted response menus retain every timing choice.

Private-intention normalization has checked posterior and conditional
continuation comparisons. The
[assessment comparison](../Vegas/Game/DisclosureAssessment.lean) expresses
both prescribed and deviating normalized continuations using the same mixture
of original source information views. Actual owner observations are connected
to these comparisons by the checked source-prefix recovery and traffic
factorization. The local-incentive proofs identify the actual physical
continuation after each permitted response. No posterior correspondence is an
assumed premise of the compiler theorem.

At zero-mass effective views, normalizing erased intentions need not commute
with limits. Use the existing common-subsequence SE limit theorem for an
existential target assessment and prove its initialized outcome law. Do not
infer that the fixed terminal-law compiler is the pointwise SE strategy limit.
A fixed strategy translation would require a separate proof at those views.

### Raw deviations and actual settlement

The [binding stopped coupling](../Vegas/Game/SourceServiceStoppedBindingWindow.lean)
handles the whole remaining binding roster: optional waiting, a first opaque
submission, repeated owner and foreign visits, protected inclusion and expiry.
Its repaired marginal uses one fixed implementation and every repaired endpoint
has a permitted trace. Each original endpoint either contains attributed
forbidden traffic, certifies a missed binding, or preserves the required
observation relation. The
[off-turn roster coupling](../Vegas/Game/SourceServiceOffTurnWindow.lean)
retains known pending replays and classifies fresh focal transmissions while
another actor holds the roster turn. Complete stopped couplings also cover
[public sampling](../Vegas/Game/SourceServiceSampleRepair.lean),
[guarded disclosure](../Vegas/Game/SourceServiceResolutionBlock.lean), and
[foreign binding settlement](../Vegas/Game/SourceServiceForeignBindingRepair.lean).
Each includes its real inclusion or sample, clock padding and expiry.
The [remaining-event induction](../Vegas/Game/SourceServiceRemainingRepair.lean)
composes these blocks through any complete-event suffix, preserving both
actual marginal laws and one fixed repair implementation. The
[active-history coupling](../Vegas/Game/SourceServiceActiveRepair.lean) starts at
any intermediate decision. The [evaluator theorem](../Vegas/Game/SourceServiceEvaluatorRepair.lean)
identifies both marginals with the standard behavioral continuation evaluators,
using one repair policy across all hidden histories at the information site.

The [behavioral realization](../Vegas/Pending/ReactiveBindingRealization.lean)
identifies the seeded repair runner with one legal behavioral continuation
against the original target opponents. The seed depends only on starting own
recall, so it is shared by every hidden history in the information set. The
whole-program coupling supplies the matching original marginal against unchanged
opponents.

The [combined audit](../Vegas/Pending/ReactiveServiceAudit.lean) charges once
for sampled forbidden traffic or a public binding omission. Its source instance
charges no permitted history. Missing records in a partial sample are never
omission evidence. A public omission is attributable only under the explicit
protected timely-inclusion contract. Accepted unusable handles instead use the
checked owner-memory repair; no public test for privately unusable material is
assumed.

The [settlement comparison](../Vegas/Game/SourceServiceRepairSettlement.lean)
derives actual incremental collection from this coupling and the repaired
traces' zero charge. Its range corollary fixes the deposit from all effective
native-history payoff extrema, before any equilibrium is chosen. The
[conditional continuation comparison](../Vegas/Game/SourceServiceContinuationComparison.lean)
instantiates that bound for every actual whole deviation and every finite
belief. The [SE extension](../Vegas/Game/SourceServiceRestrictionExtension.lean)
therefore extends every permitted-runtime SE to the effective native menu,
including rational off-path play and the exact joint observation/realized-payoff
law. The [raw response-alias lift](../Vegas/Game/SourceServiceRawExtension.lean)
completes this edge to the full bounded raw runtime. Source readouts and their
initial-type/public-result projections satisfy its proved normalization
invariance condition. Utilities depend on initial types and public results;
repaired future private values are excluded.

One deposit can cover a first departure and every subsequent plan: the bound
uses the whole continuation's payoff range. After an unavoidable charge, the
proof permits rational off-path continuations rather than requiring further
compliance. No increasing sequence of fines is required. An already unavoidable
charge cannot be counted again when justifying a later comparison.

### Layering

These are proof relations, policy families and restrictions of the existing
runtime. They add no emitted language, interpreter, source operation or
player-memory representation. Generic equilibrium and probability arguments
belong in GameTheoryExtensions; generic reactive execution belongs in
Interaction; pending-message semantics belongs in Vegas/Pending; source
correspondence and compiler composition belong in Vegas/Game. The GameTheory
submodule is not an implementation workspace.

## Main theorem boundary: audit at settlement

The end-to-end target must retain bounded off-turn transmissions and pending
observations. The owner/watcher calendar below is a checked service instance,
not a restriction on the final preservation claim. The source language and its
legal opening/withholding choices remain unchanged.

The compiler theorem uses a terminal audit service with four explicit duties:

1. Report authentic signed envelopes with their public phase and prior ledger.
   The signed-audit checker permits public replay by every player and attributes
   forbidden fresh traffic to its signing account. Authenticating phase and
   prior-ledger evidence remains an oracle obligation beyond the signature.
2. Charge no permitted source behavior, including off-equilibrium choices.
   Missing audit records alone are not evidence of an omitted action.
3. At every retained opportunity for a first departure, provide a conditional
   collection probability sufficient for the fixed deposit and payoff bound,
   uniformly over subsequent play. Later deviations cannot erase recorded
   evidence, and an already unavoidable charge is not a fresh deterrent.
4. Supply audit information to settlement without adding unmodeled observations
   before the last strategic choice. Public intermediate reports require their
   own information-correspondence proof.

[TerminalAudit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
checks the generic SE extension and exact joint realized-payoff law from these
incentive assumptions and the structural action restriction. It permits
correlated partial audit verdicts and needs no strategic watcher. This is not
yet an instantiation for every VegasCore program or arbitrary service.

[ReactiveAuditEquilibrium](../Vegas/Pending/ReactiveAuditEquilibrium.lean)
composes that enforcement with the actual runtime's private-alias lift. It
accepts any retained response menu, initial law and service satisfying the
decision-clock and traffic certificates. This native edge has no revelation-only
or watcher premise. The source capstone separately supplies its revelation
calendar, source correspondence and concrete conformance checker. Broader
source classes need those operational proofs, not another enforcement tower.

[ReactiveTrafficAudit](../Interaction/ReactiveTrafficAudit.lean) reads traffic
from successive public service views of the existing runtime. It retains the
broadcaster, envelope, observation phase and preceding ledger, including for replays. Its
persistence and partial-observation soundness proofs allow arbitrary schedulers
and raw responses; no reserved reporting slot or one-message pending pool is
assumed. The complete readout is an ideal service specification, not a claim
that an ordinary passive client sees all traffic or authenticates every sender.
Coverage, accurate phase reports, attribution and collectible collateral are
implementation obligations. A client/oracle realization may provide a partial
record and a conditional collection bound instead of a complete log.
[ReactiveAuditCollection](../Interaction/ReactiveAuditCollection.lean) derives
that continuation bound from per-record sampling coverage and actual first-step
evidence, against arbitrary later strategies. It also proves zero charges for
conformant traffic under authentic partial sampling.

[ReactiveTrafficState](../Interaction/ReactiveTrafficState.lean) reconstructs
the same audit from existing service recall at every actual prefix. This adds
neither runtime memory nor player observations. Its normalization invariance
lets the final raw-response lift preserve the actual randomized settlement law.
[Replay traffic soundness](../Vegas/Game/RevealServiceReplayTraffic.lean) and
[signed departure evidence](../Vegas/Game/RevealServiceSignedDeparture.lean)
discharge the concrete checker obligations for the revelation service. The
[signed capstone](../Vegas/Game/RevealServiceSignedCompilation.lean) needs no
strategic reporting, zero-utility player or broadcaster attribution. The
projection to signed evidence occurs before partial sampling. Account liability
is not a theorem about physical senders or cryptographic key sharing. Soundness
is proved for every retained history and each actor's first departure; a general
non-framing property after arbitrary other departures is not established.

The source-to-permitted-runtime proof must establish observations,
conditional laws and consistent beliefs. Single-trace membership does not
establish those facts. These gates are checked for the revelation calendar and,
through the full-language roster service, for every source constructor: fresh
bindings, public chance and guarded disclosure are classified site by site
(`Vegas.DecisionSiteKind`), not excluded.

## Checked service instance

The [general extension theorem](../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean),
[private-alias lifting](../Vegas/Pending/ReactiveAliasEquilibrium.lean), and
[scalar certificate checker](../GameTheoryExtensions/Analysis/EnforcementSynthesis.lean)
are checked. Decision-site recall now suffices for the general theorem, and
[nested reactive menus](../Interaction/ReactiveMenuRestriction.lean) instantiate
its structural restriction. Their composition with the actual source/native
correspondence is checked for the revelation service. The
[roadmap](se-preservation-roadmap.md) records current
results and broader research boundaries.

For the actual initialized fixture, [C/W/N menus](../Vegas/Examples/MonitoredGuessing/Restricted.lean),
[their inherited decision clocks](../Vegas/Examples/MonitoredGuessing/RestrictedClock.lean),
and the [W → N → T equilibrium extension](../Vegas/Examples/MonitoredGuessing/WatcherRaw.lean)
are checked. The watcher extension allows arbitrary fixed ordinary-player
utilities and requires watcher utility zero at every history. The raw lift
preserves every joint observation/payoff law invariant under the proved private
normalization. The [S → C equilibrium theorem](../Vegas/Examples/MonitoredGuessing/RestrictedEquilibrium.lean)
and [all-profile joint law](../Vegas/Examples/MonitoredGuessing/RestrictedLaw.lean) are
checked for arbitrary declared integer tables with zero watcher payoff. The
ordinary-player continuation comparisons are checked for every retained history
and arbitrary paired profiles. Their
[C → W → N → T composition](../Vegas/Examples/MonitoredGuessing/RestrictedExtension.lean)
is also checked. The
[literal-source capstone](../Vegas/Examples/MonitoredGuessing/DeclaredCompilation.lean)
composes these edges: every SE of the actual two-reveal program has a full raw
native SE with the same joint initial-bit/result/net-payoff law. Its deposits
are fixed from the declared table; watcher returns are zero.

The reusable backend is assembled in
[RevealService](../Vegas/Game/RevealService.lean), using the existing runtime.
The following obligations establish its arbitrary-length theorem:

| Obligation | Status |
| --- | --- |
| Existing reveal-only syntax, repeated owners, both disclosure choices | Checked, including source store and completion-history agreement after either choice. |
| Fixed service, deadlines, C menu inside the full effective menu | Constructed, with initialized and prefix execution correspondence. |
| Finite alphabet covering every supported initial value | Checked; extending the alphabet retains every previously admitted raw response. |
| C actions project to opening/withholding with fully supported split perturbations | Checked at all actual native decision sites; source fully mixed perturbations compile to fully mixed native profiles and converge to the compiler profile. |
| Native decision view determines the source decision view | Checked from typed store and completion-history agreement. |
| Source view reconstructs native semantic observation and initial candidate catalogue | Checked at reachable ranked prefixes, including public service fields; the focal selector also reconstructs the sender's replay recall. |
| Common decision depths for C/W/N/raw menus | Checked at all legal histories using the existing public clock and actor observations. |
| Bounded settlement under arbitrary responses | Checked for every finite response menu and every legal terminal history, including zero-probability histories. Remaining suffixes settle whenever preceding events have completed. |
| Full monitored block agrees with its source reveal | Checked for every ordinary response, including published-replay aliases of withholding; typed source store and action history agree afterward. |
| Initialized compiler execution law for arbitrary reveal sequences | Checked for all source policies and all alias-splitting weights, with correlated valid initial bindings. |
| Source information prerequisites | Checked common decision depths and a fully mixed reference policy; finite legal histories require no finite ambient secret type. |
| Reverse information correspondence and checkpoint prefix laws | Checked at actual native boundary and owner-decision depths; includes correlated initialization and replay selectors. |
| Consistent native beliefs | Checked: one common perturbation sequence preserves the source-state posterior at every owner information site, including aliases with zero limiting probability. |
| Source-to-C sequential rationality | Checked against arbitrary whole continuation policies through conditional local comparisons and the posterior one-shot principle. |
| Conditional monitoring, packet classification and persistent evidence | Checked in actual behavioral continuations at every hidden history satisfying the operational checkpoint invariant. |
| Ordinary-player net-utility comparison | Checked at every retained information history; every retained continuation is clean and every extra ordinary response has the required conditional collection bound. |
| Fixed deposits | Actual finite watched-history extrema yield sufficient real-valued range/rate deposits before an equilibrium is chosen. This is mathematical synthesis; executable rational-table inference is a separate checked result. Collection rates and monetary implementation remain backend obligations. |
| C → W extension | Checked for every retained SE, preserving retained strategies, beliefs and the full history/net-payoff law. |
| W → N → raw equilibrium extension | Checked for arbitrary reveal sequences, normalization-invariant observations/utilities, and zero watcher utility at every history. |
| Terminal-audit enforcement | Checked: the actual public checker accepts every retained prefix and every extra effective response produces forbidden traffic. Authentic partial sampling plus fixed all-player deposits gives the full raw SE and actual joint randomized settlement law. |
| End-to-end SE for arbitrary reveal sequences | Checked under either terminal auditing or the separate indifferent-reporter service assumptions. Both preserve every original source SE and the exact joint typed terminal-state/net-payoff law. |

The source-to-C belief proof compares distributions over the existing
source protocol state. That state retains initial private values and source
action memory. Standard source continuation values can therefore be evaluated
from this marginal, while retaining the original history-based SE assessment.
This avoids reconstructing a source execution history from every native history.
The checked native selector accounts for recorded replay aliases, including at
zero-probability information sets of the limiting strategy.

For the full-language boundary,
[hidden-binding analysis](research/se-hidden-binding.md) separates a public
audit limitation from the strategic question. A native unusable binding can be
publicly indistinguishable from valid binding followed by withholding. Within
source semantics, however, value-only continuations match every such behavioral
deviation from an arbitrary posterior over residual configurations. The native
opponent-view simulation and consistent extension remain proof obligations.

For the calendar boundary, [opening-timing analysis](research/se-opening-timing.md)
exhibits a real remembered timing channel between two otherwise valid opening
opportunities. The phase-and-ledger traffic audit does not distinguish those
traces. This refutes an information-isomorphism proof for that extension, not
SE preservation itself: a forward construction may use type-independent timing
perturbations. Their conditional-law and sequential-incentive proofs remain open.

## Stack: one runtime, several strategic games

The emitted program still follows SourceProgram + Setup → EventGraph → native
application/service. The strategic proof uses the following derived games:

The terminal-audit capstone takes the direct path:

```text
S  Original source game
   | Source choices, conditional incentives and common consistent beliefs
   v
C  Source-representable responses in the actual native service
   | Sound terminal traffic audit and fixed deposits for every player
   v
N  Every effective native response
   | Proved private-response aliases
   v
T  Every bounded raw native response
```

This path has no strategic reporting edge. Its auxiliary player may have any
source utility; the audit deters its extra transmissions like every other
player's. The existing calendar and its auxiliary activations are still present.
The reporting-based instance uses the following alternative enforcement path:

```text
S  Ordinary source game
   |  Compile through EventGraph; expand decisions into service blocks
   v
C  Native service with all source-representable choices;
   prescribed reporting; harmless published replays represent silence
   |  Restore ordinary players' other effective responses
   v
W  Full effective ordinary-player menus; prescribed reporting
   |  Restore the watcher's other effective responses
   v
N  Full effective native menus, including strategic watcher
   |  Lift through proved private response aliases
   v
T  Full bounded raw native game
```

C, W and N use the existing reactive application, initial distribution,
activation calendar, observation rule, transition function, deadlines and
settlement decoder. They differ in response menus. They are genuine game
instances, with their own legal histories, constructed using
[ResponseMenu](../Interaction/ReactiveResponseMenu.lean). T is the original
bounded raw instance; the last edge uses the existing operational alias theorem.
There is no new interpreter or programmer-written intermediate language.

The effective menu removes only private response distinctions with a proved
normalization. It retains every publicly different packet, malformed payload,
meaningful binding choice and disclosure capability. Deposits and the liability
rule are identical throughout the native stack. Source-representable play
incurs zero additional charge.

For the reusable reveal class, C also includes rebroadcasts of already published
envelopes as alternative implementations of silence. The source correspondence
must account for the sender remembering that choice. These replays are not
globally erased from the full target: with unpublished off-path traffic present,
a sampler may react to the changed pending list. The final alias edge remains
limited to the exact-effect private submission normalization.

All games use the same player carrier for the restriction edges. The initial
fixtures already contain an inactive, zero-payoff source watcher. Supporting a
compiler-added watcher requires an explicit harmless-player source adapter;
do not silently change the player universe in a theorem application.

### Why each edge earns its place

| Edge | Contract | Main proof obligation |
| --- | --- | --- |
| S → C | Expand source decisions into concrete service blocks; preserve all source choices, continuation incentives and consistent beliefs. | Relate meaningful decision information and checkpoint laws despite different step counts. |
| C → W | Every C equilibrium has a W equilibrium with matching retained behavior, beliefs and net outcomes. | Actual legal-comparator inequalities for every ordinary player's added response, with the watcher constrained to report. |
| W → N | Restore the watcher's full effective menu while retaining the equilibrium just constructed. | Initially use identically zero watcher utility at every history. Each extra watcher action then has value equal to its prescribed comparator. |
| N → T | Restore private response representations without changing public packets or strategic outcomes. | Instantiate the checked alias theorem; prove the payoff/charge decoder is invariant under normalization. |

The W → N edge is checked for the reusable reveal service. All traffic caused by ordinary-player deviations is already possible
in W. Its reporting decisions are therefore retained by the second extension.
New sites reached through watcher deviations receive rational completions.
This is a forward-existence argument: it does not establish strict reporting,
uniqueness, paid participation or coalition resistance. An interested watcher
needs a different incentive certificate.

The last two edges are composed for both the fixture and the reusable service in
[RevealServiceWatcher](../Vegas/Game/RevealServiceWatcher.lean). The
[continuation-horizon lemma](../GameTheoryExtensions/Protocol/ContinuationHorizon.lean)
proves that evaluating with remaining fuel or a full global bound gives the same
context, so the extension and alias theorems use exactly the same equilibrium
notion. The composed law retains both observations and actual utilities, subject
to their explicit normalization invariance; a utility of private response names
would not satisfy that premise.

Each edge must extend every equilibrium of its actual preceding game. Showing
two capabilities harmless in separate extensions of S would not justify their
combined extension. No game or fine may be chosen after seeing the source SE.

## First program class and service

### Checked fixture

The actual [two-publication payoff-table family](../Vegas/Examples/MonitoredGuessing/Payoffs.lean) has
valid initialized commitments, Bob's reveal followed by Alice's reveal, and
literal integer return tables. It retains **both opening and withholding at both
source decisions**, under arbitrary source strategies. Its S → C proof does
not rely on Alice opening in equilibrium.

For C, opening uses the actual matching-certificate packet and
withholding with silence followed by expiry. This gives omission a source
meaning without assuming that passive packet monitoring detects silence.
An explicit withholding packet is extra observable traffic. The checked service
laws cover both source branches.

Ordinary-player payoff tables may be arbitrary; the watcher is assigned zero
utility. Every additional ordinary response has an actual comparison certificate
under the fixture's stated service and observation rule.

### Reusable reveal class

Generalize by induction to finite sequences of guard-free revelations of valid
initialized commitments, in a fixed public order, with finite setup support and
arbitrary declared terminal payoffs. Owners may recur; setup types and
commitments may be correlated. Retain every source withholding choice. Express
membership as a predicate/certificate on existing programs, not new syntax.

[RevealSequence](../Vegas/Source/RevealSequence.lean) defines this predicate on
existing syntax and proves that the open-obligation index counts the remaining
decisions. From an empty guard registry, every reveal returns its bound result
or failure according to the player's disclosure choice, and every policy
satisfies guard acceptance. The [repeated-owner source check](../Vegas/Examples/RevealSequence.lean)
retains withholding followed by later openings in an Alice → Bob → Alice
sequence. This check does not assert native SE preservation for that sequence.

Fresh commitment generation, deferred guards, adaptive activation calendars and
unbounded traffic are outside this first theorem. Initial binding validity is a
setup assumption. It does not establish a cryptographic setup protocol or
security under key/secret sharing.

The constructed block for event rank `k` activates the event's owner,
attempts reserved inclusion, activates the watcher, includes its report, advances
the clock `k+1` times, and expires the event. It issues no grant: the owner acts
on the event its public view shows ready. Its relative deadline is `k+1`.
The owner is activated once per source event; arbitrary intervening broadcast
opportunities are outside this backend contract. All other players' passive
sampling rules remain parameters.

This roster restricts transmission opportunities, not just total traffic.
For example, an owner whose first source decision is later cannot broadcast
before an earlier owner's decision in this instance. A theorem for this service
must not be presented as preservation against arbitrary ambient communication.
Lifting that restriction requires monitored off-turn opportunities and an
enforcement argument for early current-event openings; the ordinary packet
format and other-event rejection tests alone do not establish it.

[Finite initial-value coverage](../Vegas/Pending/ReactiveInitialValues.lean)
extends the declared packet alphabet with the values in the finite setup law.
It preserves the original raw menu, including malformed traffic and independent
evidence. [Checkpoint coverage](../Vegas/Game/RevealServiceBounds.lean) then
proves an authentic initialized opening available whenever the checkpoint retains
its initial binding tables. The theorem needs neither finite value types nor
a bound selected after seeing an equilibrium.

The repeated-owner source regression uses Alice → Bob → Alice. A
successful owned opening and a forwarded certificate can emit the same packet
while leaving different private response recall. A later decision makes this
relevant to the universal comparator premise. The proved alias
normalization handles such requests before the ordinary-response extension;
invisible private distinctions cannot be audited. Replays of old envelopes also
need a service-insensitivity argument, since old public content can still change
the service's input history.

The [successful-evidence regression](../Vegas/Examples/SuccessfulEvidenceAliases.lean)
checks two available raw requests with identical external effects and different
private recall. [EvidenceNormalization](../Vegas/Pending/EvidenceNormalization.lean)
merges requests exactly when they resolve to the same certificate. It prefers
valid forwarding references, preserving received evidence even when its value
is outside the menu's owned-issuance bounds. Selection respects the packet
resolver's first matching message ID on arbitrary known lists. The finite
compiler remains in the raw menu; the existing alias-SE theorem handles the
separate normalization edge.

For general pending visibility, monitor each ordinary response opportunity and
prove a conditional collection bound before settlement. Detection may follow a
recipient's reading: the payoff-range bound covers the resulting gain. The audit
must retain the phase in which the packet was sent, or receive its report before
the phase advances. Otherwise an early opening can become permitted before it
is audited. On compliant paths the reporter remains silent and canonical
traffic settles before the next meaningful source decision.

[ReactiveMonitoring](../Interaction/ReactiveMonitoring.lean) implements the
sampling-to-evidence step using ordinary watcher activation, local replay,
public at-most-once inclusion, and receipt persistence under arbitrary later
policies. The [Vegas phase lemma](../Vegas/Pending/ReactiveMonitoring.lean)
proves that any packet addressed outside the current ready public event is
rejected in a barrier-ordered graph. Timely reporting therefore records an
early opening before it can become legal; no authenticated send-time field is
needed for this service. Rejection alone is not a general misconduct test:
the source correspondence must still prove canonical calls accepted and
classify all additional responses.

[MessageReplayObservation](../Interaction/MessageReplayObservation.lean) proves
that pending traffic already published in the ledger cannot provide new private
observations, under any sampling rule. Replaying a published identifier preserves
that property. This does not erase the network input or sender's action recall;
the [reserved inclusion selector](../Vegas/Pending/ReactiveReplaySelection.lean)
also ignores spent pending copies. The source correspondence still needs the
strategic proof that these C responses duplicate silence, including consistency
at the additional private information sites.

The intended projection is confined to C histories. Canonical openings settle
before the watcher, and the watcher is silent; every other permitted pending
envelope is already published. Erase those pending copies, retain each envelope's
original input, and map each remembered spent replay and its emission to a silent
response. The proof should lift one common source perturbation sequence using
the existing action-splitting machinery, transport conditional beliefs, and
derive local incentive equality. The existing local-to-whole-policy theorem can
then establish sequential rationality. This argument remains to be completed;
no full-target replay quotient is asserted.

The general source correspondence needs induction over the existing reveal
program and its service blocks. The fixture's explicit history classification
and fair-bit posterior do not supply that induction or handle arbitrary
correlated setup and off-path source decisions.

[Source checkpoint agreement](../Vegas/Game/RevealServiceState.lean) proves
initial store agreement and its preservation by actual native completion and
source revelation. The local source decoder finds the authentic opening using
the owner's view and the binding invariant.
[Information recovery](../Vegas/Game/ServiceInformation.lean) recovers
the exact source decision view from store and completion-history agreement.
[Action splitting](../Vegas/Game/RevealServiceActions.lean) projects C actions
to the source Boolean choice and lifts fully supported distributions; silence
and spent replay share the withholding fiber. These facts still need the
whole-history induction and reverse information correspondence.
The [reverse observation lemmas](../Vegas/Game/ServiceObservation.lean)
recover the native graph observation and candidate catalogue from the source
view at reachable ranked prefixes. They reduce complete before-view equality
to the actual public accepted-handle, clock, activation, ledger, leak
and receipt invariants. They do not assume information-fiber equality or a
belief-preserving target assessment.
The [policy adapter](../Vegas/Game/RevealServicePolicy.lean) uses the existing
source-to-event compiler for the disclosure law and implements it using these
action fibers. Its support belongs to C at every local input; the source-law
equation additionally requires the operational checkpoint invariants.

[Checkpoint Bayes projection](../GameTheory/GameTheory/Analysis/Protocol/BeliefTransport.lean)
allows different source and native prefix depths. Its premises are actual
prefix-law projection and reflection of the selected information fiber; it
does not assume a belief-preserving target assessment. The compiler must still
discharge those premises along the source assessment's common perturbation
sequence, including source sites with zero limiting probability.
Its focal-selector corollary cancels the focal player's own reach probability
using decision recall, so private replay distinctions need not become source
observations. The selected-prefix projection and fiber premises remain to prove.

### Calendar requirements to prove

- Fix the activation roster independently of player responses. Inclusion
  decisions may vary only within the proved service contract.
- A canonical owner response is followed by its inclusion attempt before any
  other player activation. The watcher then reports any remaining unpublished
  traffic before ticks and expiry. For an off-address departure the current
  event is still ready; on a canonical opening path it has already completed.
- Prove timely opportunities and completion for every source opening/withholding
  branch, and terminal settlement under every final raw policy.
- Prove that compliant activations reveal no additional pending information.
  A forced response alone does not make an observation harmless: it can be
  remembered and used later.
- Derive a common decision depth from the fixed roster and existing own-response
  recall. Do not expose an otherwise hidden scheduler position to players.

Grants are not inclusion authorization in the current handler. A successor's
deadline starts when its predecessor completes, potentially before the previous
visit's ticks finish. Both facts need explicit treatment when constructing the
calendar; a fixed list of commands alone supplies no timeliness theorem.

[ReactiveRevealBlock](../Vegas/Pending/ReactiveRevealBlock.lean) proves the local
opening and silence/expiry equations for the existing service, preserving the
actual network, receipts, and recall. Readiness, opening acceptance, freshness,
and expiry timing are explicit premises. The program induction must supply
these premises for the complete calendar; a local block equation alone does
not establish them for every source execution.

[Monitored settlement](../Vegas/Pending/ReactiveRevealSettlement.lean) composes
the actual watcher/report, clock ticks and expiry into a deterministic tail
for either source branch. It permits spent pending copies and retains the
watcher's real silent response recall. No private sampling restriction is
needed on these source-representable paths.

[Sequential deadline lemmas](../Vegas/Pending/EventSequentialTiming.lean) prove
that completing an event activates its immediate successor at the actual
completion time. Early completion followed by `k+1` ticks leaves the successor
younger than its deadline `k+2`; completing at expiry leaves age zero. This
supplies the local timing step for both source choices. The full-calendar
invariant is still part of the source correspondence proof.

## Early risks and decisive gates

Run these gates before committing to a general source adapter or a large
certificate extractor. Their outcomes determine the backend contract.

### G1. Recall required by the theorem

**Checked.** The native model uses an empty information value while a player is
inactive. [DecisionRecall](../GameTheory/GameTheory/Protocol/DecisionRecall.lean)
requires equal own-play records only at genuine decision sites. The generic
completion, switching, one-shot and extension proofs use this premise, and
[every reactive response menu](../Interaction/ReactiveOwnPlay.lean) satisfies it
with the existing observations.

The branch-regret proof assigns zero allowance to non-decision information.
A [regression](../GameTheoryExtensionsTests/DecisionRecall.lean) checks that a
model failing global recall still satisfies this premise and admits an SE by
the generic theorem. Common decision depth is a separate calendar obligation;
no clock or memory observation is added to satisfy it.

For the reusable reveal backend,
[RevealServiceClock](../Vegas/Game/RevealServiceClock.lean) proves common
decision depth at every raw history and for every response menu of the same
service. The public clock identifies the block, since every earlier block
advanced it a known number of times. Actor identity
distinguishes its owner and watcher opportunities, with a watcher distinct
from all source owners. The formulas include both actual environment steps
and prior player responses; they do not assume source-conforming play.

The [full raw fixture](../Vegas/Examples/MonitoredGuessing/NativeClock.lean) has common
decision depths at all legal information sets: initial Alice at 2, Watcher at 4,
Bob at 8, and final Alice at 14. The C/W/N games inherit this certificate through
their actual history embeddings. Alice's two sites are distinguished by her
existing observations; the proof adds no public clock.

### G2. Effective responses versus invisible aliases

[ReactiveNormalization](../Vegas/Pending/ReactiveNormalization.lean) removes
ineffective opening material and canonicalizes requests by their resolved
certificate, including failed requests and successful aliases. The owned check uses
the candidate after the same atomic submission, so fresh creation followed by
disclosure remains possible. Packet and submission effects are proved equal.
Withholding cannot register private commitment material; its irrelevant opening
field is a representation alias.

An owned request and a forward can carry the same certificate, as can forwards
from two known envelopes. The normalization merges these private names with
checked packet equality and finite-menu closure. Source canonical requests need
normality only at their retained checkpoints; the raw compiler's requests need
not be normal at arbitrary off-path histories.

Enumerate canonical-packet response aliases in the bounded fixture. Extend
normalization only with proofs of identical submission and packet effects, or
prove a suitable alias lift. Keep valid extra certificates as real actions.
Do not treat invisible differences as punishable or automatically assume the
stronger uniform local comparator condition holds for them.

**Exit:** every omitted response is assigned to a proved private alias or a
genuine effective extra action. The final alias lift restores the original raw
menu, including arbitrary raw deviations.

### G3. Source-wide fidelity and timing

Check all eight initial-bit/Bob-choice/Alice-choice branches of the two-reveal
fixture, including withholding. Then prove checkpoint and information laws for
arbitrary policies. Include a repeated-owner fixture before claiming the
arbitrary-length class. Check candidate/serial choices, ledger contents, own
recall, deadline progress and observations at intervening activations.

The eight [concrete branch laws](../Vegas/Examples/MonitoredGuessing/RestrictedExecution.lean)
are checked, including the initial bit, both public results and zero pilot charge.
The [meaningful checkpoint inputs](../Vegas/Examples/MonitoredGuessing/RestrictedInformation.lean)
have one Bob input and four distinct Alice inputs, and both source choices are
legal at each checkpoint. The all-history Bob and Alice classifications and
consistent assessment correspondence are also checked.

The [reference-run support proof](../Vegas/Examples/MonitoredGuessing/RestrictedSupport.lean)
also classifies every legal C Bob decision as a quiet checkpoint, and every Bob
information site as the same source-representable input. The
[Alice classification](../Vegas/Examples/MonitoredGuessing/RestrictedAliceSupport.lean)
identifies both her forced initial responses and every final decision. Her final
information determines the complete continuation state; Bob's consistent belief
has the initial fair-bit distribution. These facts support the checked
[source equilibrium theorem](../Vegas/Examples/MonitoredGuessing/RestrictedEquilibrium.lean)
without assuming a target belief or rational completion.

The existing compiler withholds a guard-rejected value:
[compiled_packet](../Vegas/Examples/CommunicationNative.lean) checks that case.
Raw disclosure after guard failure is consequently an extra-action issue for
that compiler. Collapsing the source's true/false intentions into the same
packet is a separate recall obligation, deferred with guarded programs.

**Exit:** all source choices have faithful implementations, and all allowed C
behavior has a source account. Equality of initialized outcome laws alone is
insufficient. No selected equilibrium is used to define C.

### G4. Observable deviations by every player

A [checked operational witness](../Vegas/Examples/MonitoredGuessing/Conformance.lean)
exposes a gap in the pilot's collector: Bob can attach a
valid certificate to an accepted withholding packet. Alice then sees a new
ledger observation. Against a paired source profile where Alice withholds after
either legal Bob choice, an extending target profile may open only after this
extra packet. If Bob receives one for Alice opening and zero otherwise, every
legal source comparator yields zero and this extra action yields one. The
pilot's Alice-only charge does not apply.

This comparison-failure argument concerns the universal comparison premise,
not SE preservation: the premise ranges over irrational continuations too.
The checked regression establishes acceptance, changed observation and lack of
pilot liability; a full profile-level comparator counterexample is not yet
formalized. Restoring watcher choices last does not solve this ordinary-player
issue.

The generic route therefore needs sound comparisons for all ordinary players:
publicly checkable conformance violations, including accepted side packets,
need collection; harmless effective actions need actual legal comparators.
Rejecting calls alone, checking only evidence shape, or filtering unauthorized
inclusion does not establish this contract.

**Exit:** an exhaustive response classification for the fixture, including
accepted extra evidence, wrong addresses, early openings, replay, malformed
packets and silence. A real undetectable profitable class is an obstruction to
this certificate/backend; do not hide it by reducing the final menu.

The [coverage audit](research/monitored-response-coverage.md) tracks the concrete
classes. Two operational comparison gates are checked:

- At the canonical final-Alice checkpoints, [every raw response has a legal C
  comparator](../Vegas/Examples/MonitoredGuessing/RestrictedFinalComparison.lean),
  selected from Alice's information and the response. It preserves the terminal
  result and weakly increases her utility for arbitrary declared result tables
  and nonnegative rejection charges. No future player response is needed.
- At the quiet Bob checkpoint, [unselected Bob submissions](../Vegas/Examples/MonitoredGuessing/BobContinuation.lean)
  leave Alice's entire next input equal to the C silent branch. Known replay is
  unavailable there. The proof uses Alice's empty passive sample; a service that
  allows her to read this pending traffic needs a different comparison or
  additional monitoring.

The [early](../Vegas/Examples/MonitoredGuessing/RestrictedInitialComparison.lean),
[receiver](../Vegas/Examples/MonitoredGuessing/RestrictedBobComparisons.lean), and
[final](../Vegas/Examples/MonitoredGuessing/RestrictedComparisons.lean) comparison
theorems now connect actual service suffixes to behavioral continuation
contexts. They cover every retained hidden history and arbitrary paired
continuation profiles. Extra Bob-addressed packets have unit persistent
liability; wrong-addressed packets preserve his joint result/net-payoff law
against the matched legal Alice response. No rationality premise supplies any
of these bounds.

### G5. Reporting, attribution and collection

In W, prescribe reporting at every watcher observation through its singleton
menu. Prove collection from actual passive sampling, reporting and inclusion,
at every retained hidden history and selected departure, uniformly over every
paired continuation profile required by the capstone. A bound averaged over an
equilibrium belief is insufficient for this theorem. Existing snapshot sampling
bounds are ingredients, not this execution theorem.

The [ledger audit](../Interaction/ReactiveLedgerConformance.lean) now proves
public detection at inclusion and persistence under arbitrary raw continuations.
Its native regression accepts the canonical matching-certificate opening,
detects the accepted extra evidence and missing-certificate packet, and leaves
silence/expiry clean. The
[whole-outcome payoff bounds](../Vegas/Examples/MonitoredGuessing/EnforcementPayoffs.lean)
use Alice's deposit twice her payoff range and Bob's deposit equal to his range.
These bounds and the actual response coverage discharge the fixture's
conditional inequalities. Monetary collectibility remains an assumption of the
utility interpretation. Attribution uses the original author; it does not
automatically identify who causes a replay.

Prototype two complementary evidence paths in the existing runtime:

| Traffic | Candidate evidence path | Obligation |
| --- | --- | --- |
| Included packets, including accepted side evidence | Audit the public ledger/receipts after inclusion. | Check source-wide conformance, attribute the actual departure and collect before settlement. Application acceptance alone is not conformance. |
| Pending traffic, whether or not later included | Passive sampling during explicit extra-response windows, followed by reporting. | Prove a history-wise collection bound and retain all observations available to ordinary players. Sampling alone is not collection. |

This candidate keeps canonical response/inclusion pairs together; an audit of
already-public traffic need not insert a private observation between them.
Whether these paths cover the full effective response menu is G4/G5's question,
not a backend assumption to assert by definition. If monitoring needs an
intervening activation on compliant play, prove its information effect in S → C.
Bound the probability of the combined event: timely attributable ledger evidence
or a timely attributable pending report. Do not condition the sampling rate on
eventual non-inclusion; later inclusion can depend on the report itself. Count
the actual collectible loss, without charging twice for the same liability.

Prefer liability computed from existing public evidence and receipt/history
data. Phase-dependent violations need an immediate monitor window or
authenticated historical context. Test source-wide soundness, including delayed
lawful packets. A replay can expose the original sender's identity without
proving who caused the new broadcast; charge attribution must follow the
evidence actually available. Never inspect the ideal private commitment catalog
to supply an ordinary monitor's evidence.

**Exit:** no false positives for C, adequate additional collectible loss for
each harmful departure, and persistence under arbitrary later W play. Restore
the zero-utility watcher's menu only after this proof. Monetary collectibility
remains an explicit backend assumption until an escrow implementation is proved.

## Implementation work packages

Relative effort describes proof scope, not elapsed-time estimates. Proposed
module names below are provisional; reuse existing modules when the dependency
direction permits it. All generic additions belong in root GameTheoryExtensions,
never the GameTheory submodule.

| Package | Deliverable and owner | Depends on | Effort / principal risk |
| --- | --- | --- | --- |
| A | Decision-site recall and capstone refactor in GameTheoryExtensions; native instance in Interaction. **Checked.** | G1 audit | Closed for the existing information model. |
| B | Menu-to-menu action restriction in Interaction; all-history fixture clocks. **Checked.** | Existing ResponseMenu; A for SE use | Generic roster inference remains outside the fixture result. |
| C | Private submission/packet normalization and compiler compatibility, including successful-request aliases. **Checked.** | G2 | Published replay is handled separately in the source-representable menu. |
| D | Concrete C/W/N menus, service checkpoints, all-history decision classification and source assessment correspondence. **Checked for arbitrary finite reveal sequences.** | B, C, G3 | Broader rosters require a new conditional information proof. |
| E | Persistent evidence, exhaustive response comparisons and fixed deposit bounds. **Checked for the revelation service, including terminal auditing.** | B, G4, G5 | Signed-author attribution without rebroadcaster evidence remains open. |
| F | Source-to-C SE and all-profile joint typed state/payoff law. **Checked for arbitrary finite reveal sequences.** | A, D | Fresh binds and guarded programs remain outside this correspondence. |
| G | Original source → C → W → N → T composition with the same fixed deposits and utility. **Checked for arbitrary finite reveal sequences.** | A–F | Collectibility remains a backend assumption. |
| H | General activation rosters, native unusable-binding continuation repair and weaker audit attribution. | G | The direct terminal-audit instance is checked; resolve the remaining strategic gaps before optimizing deposits. |

### Parallel execution order

1. **Feasibility wave:** A's core recall lemmas; B's restriction constructor and
   fixed-calendar audit; G2–G5 on the concrete fixture. The lead maintains the
   response-classification table and records proved facts versus assumptions.
2. **First gate review:** decide whether the proposed monitor can cover all
   harmful effective responses. Choose its public evidence and liability rule
   before fixing the service instance. No hidden stronger observer is admitted.
3. **Proof wave:** D/F build source correspondence and belief lifting while E
   proves collection under arbitrary remaining policies. Share the same frozen
   runtime parameters and menus. Avoid parallel copies of the fixture.
4. **Composition:** G closes one end-to-end theorem using the generic capstone;
   then generalize by service blocks. Only afterward expand extraction work.

With three parallel implementation lanes, assign A/F to the generic proof lane,
B/D to the runtime/source lane, and C/E to the normalization/enforcement lane.
Freeze their shared menu and calendar definitions after the first gate review.
The lead owns G, the assumptions table and integration; run one shared
warning-strict build at milestones. Each lane supplies a small compiling
regression before its dependent work expands.

If G4/G5 blocks the generic route, a direct theorem for payoff tables where
Alice strictly prefers final opening and Watcher has zero payoff remains a
separate, useful fallback. It uses credible continuation play as the pilot does.
It must be reported as a direct class theorem, not evidence that the universal
comparator certificate was discharged. A theorem selecting restricted rational
completions is another research route; do not add it unless a concrete blocker
justifies the additional proof machinery.

## Source-to-C proof design

Use fixed service blocks first. Each block implements one source decision;
other player responses are forced. Establish checkpoint transitions, meaningful
decision information and own-action correspondence from local execution facts.
Reuse graph compilation laws inside this proof without requiring a new
standalone graph SE semantics.

Lift the source's fully mixed consistency sequence through the choice mapping.
Singleton response menus need no extra strategic tremble. Derive Bayes belief
projection at meaningful native decisions from checkpoint reach laws and
information fibers; take one common limit for forced-site beliefs. Transfer
local incentives at meaningful decisions, use singleton legality at forced
ones, and apply the decision-recall one-shot theorem to whole policies.

This is a proof plan. It must derive assessment correspondence rather than
take the existence of a preserving native assessment as a premise. Forced
service observations and sampling noise need their own information argument;
the first clean calendar aims to make pending observations empty on C play.

For the immediate fixture, prove the information fibers directly before
extracting a general block adapter: Bob's meaningful fiber contains the two
equally likely initial bits; Alice's meaningful fibers identify her bit and
Bob's published choice. The initial Alice and watcher responses are forced.
Use the existing consistent-completion theorem and the actual checkpoint reach
laws to establish these beliefs, then transfer local incentives. This avoids
requiring a new generic assessment interface before the concrete case checks.

## Inference and acceptance criteria

Start with conservative range/collection certificates covering **all**
continuations quantified by the theorem. The pilot's sender lower bound covers
opening outcomes only; inserting it into the universal certificate would be
unsound. For its original table, the crude all-outcome calculation is
`(1 - (-4)) / (1/2) = 10`, compared with the direct proof's charge two. This is
certificate conservatism, not a new lower bound on SE implementability.

The existing scalar checker handles supplied rational rows. General extraction
requires explicit finite enumerators, rational kernels or certified bounds,
and a paired pure-plan averaging proof: corresponding source/target decisions
share the same sampled choices. Comparator-lottery synthesis, vector deposits,
and exact real-algebra SE diagnosis follow later.

### Expanding source coverage

The reveal class is the first compositional theorem, not coverage of the whole
language. Keep small feasibility witnesses for subsequent features while proving
that class; do not build another generic semantics for each one.

| Extension | Required evidence before adding it to the theorem |
| --- | --- |
| Deferred guards | Account for source intentions compiled to the same withholding packet; cover raw disclosure through accepted packets with the actual enforcement rule. |
| Fresh commitments | Account for irreversible unopenability and meaningful binding/candidate choices. Opaque invalid bindings cannot simply be assigned a positive detection probability. |
| More flexible calendars | Derive timing, decision recall/depth and information correspondence without adding observations to players. |
| Nonzero-payoff reporters | Prove reporting incentives, attribution and collection under the reporter's actual utility; zero-utility indifference no longer supplies the second extension. |

Each extension either discharges the same edge contracts, supplies a precise
backend assumption, or exposes a scoped obstruction. Merely failing the current
comparison certificate establishes none of these possibilities by itself.

### Acceptance

The first composed result is accepted only when it:

- Uses actual SourceProgram/Setup returns and the existing native interpreter.
- Quantifies over every source SE with one fixed game and deposit configuration.
- Includes source withholding, every final bounded raw response, off-path
  information sites and whole continuation-policy deviations.
- Preserves the exact joint type/result/net-payoff law, with zero additional
  charge on the implementing play.
- States bounded traffic, initial validity, service/monitor powers, utility
  interpretation and collectibility explicitly.
- Passes warning-strict Lean builds, axiom pins, module boundaries, and focused
  positive/negative regressions; has no proof admissions.

The final user-facing configuration is a program, declared payoffs and a backend
contract with a checked certificate. There is no per-obstruction collection of
language flags. Cryptography, paid watchers, coalitions, arbitrary asynchronous
calendars and unbounded communication remain separate extensions.

## Consolidating Nash preservation after SE

After the SE edges are instantiated, assess whether the existing Nash/Bayesian
and epsilon-Nash proofs should share their operational infrastructure: response
restrictions, execution correspondence and private-alias normalization. Preserve
the existing theorem's backend scope and fixed playerwise translation guarantees;
the SE construction currently allows completion to depend on the whole assessment.

An epsilon-Nash transport theorem needs an explicit bound on deviation gains
and any accumulated approximation loss. Reusing the stack does not by itself
establish that bound, or identify the command-policy and reactive services.
This consolidation follows the first composed SE result.

### Enforcement can support a smaller source game

Commit-time failure is already eliminable for Nash and same-error epsilon-Nash
under the existing public-outcome observation. The
[value-binding edge](../Vegas/Game/ValueBindingEdge.lean) and
[pending composition](../Vegas/Game/PendingCompositions.lean) replace an
unusable binding by a value binding followed by withholding, preserving the
public failure outcome. This does not require a rejecting guard or a watcher.
The related type/outcome law also permits type-dependent utilities.
[ValueBindingContinuation](../Vegas/Source/ValueBindingContinuation.lean)
extends the source comparison to arbitrary residual beliefs and behavioral
continuations, preserving the joint parameter/public-result law. Native SE
still requires corresponding opponent observations and a consistent extension
after hidden departures. A one-action comparison cannot simply assume that an
unusable binding becomes openable.

A global deposit rule can instead supply the incentive premise for removing
withholding, or move failure-penalty conditionals out of programmer-written
payoffs and into a common backend rule. These are stronger enforcement
assumptions supporting a smaller source strategy space. The current SE fixture
keeps withholding and initializes valid commitments; it does not establish
these further source simplifications. Its new enforcement role is chiefly to
control strategically consequential extra communication.

For required disclosure, enforce an attributable missed obligation using a
deadline and a collectible penalty. Passive packet monitoring alone cannot
detect silence. Compliant players must have a proved timely opportunity to
perform the obligation, so source play incurs no false charge.

An unusable commitment need not be publicly recognizable when submitted if its
owner must later provide a valid opening or incur sufficient loss. This route
requires the obligation and collateral to survive every relevant continuation:
an earlier abort, refund, or skipped disclosure cannot silently release the
liability. Validity proofs at submission are an alternative backend mechanism.
Neither mechanism is implemented by the current fixture, which initializes
valid commitments.

The permitted behavior must represent every legal source action and deviation,
not a single equilibrium strategy. For NE, comparisons start at the initial
game; for SE, retained decision histories need conditional comparisons and
post-violation histories still need consistent rational completions. A player
who has already made an unusable commitment cannot be assumed able to open it.
The existing extension theorem is a candidate proof route; its premises must
be instantiated for each smaller source game. No completeness or reflection
claim follows merely from deterring these departures.

### Watcher responsibilities

A concrete watcher backend separates three tasks: obtain evidence of traffic,
classify that evidence against the permitted game behavior, and authenticate
the party responsible. The contract can apply a specified collectible penalty
after receiving sufficient evidence. Observing pending traffic is a separate
capability from inspecting included transactions, and a public conformance test
does not prove the observer saw every relevant packet.

The theorem needs an explicit conditional bound on timely attributable
collection, rather than a claim that every sent message is recorded. Perfect
recording is one possible stronger service assumption; the checked fixture uses
partial sampling plus ledger evidence. The classification rule represents all
legal source choices, not a selected equilibrium profile. Its soundness,
observation coverage, attribution, and collectibility are separate obligations.
Phase-sensitive reports additionally need timely inclusion or evidence of the
phase in which the monitored departure occurred. Realizing these roles as an
oracle and contract components is a backend refinement, not implemented here.
