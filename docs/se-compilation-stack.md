# SE compilation stack and implementation plan

## Objective and status

Implement a source-to-native sequential-equilibrium theorem for a reusable
class of VegasCore programs, with all bounded raw responses available in the
final game. Fix the program, service, monitoring rule, utilities and deposits
before selecting an equilibrium. Preserve the joint initial-type, public-result
and actual net-payoff law of **every source SE**.

The [general extension theorem](../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean),
[private-alias lifting](../Vegas/Pending/ReactiveAliasEquilibrium.lean), and
[scalar certificate checker](../GameTheoryExtensions/Analysis/EnforcementSynthesis.lean)
are checked. Decision-site recall now suffices for the general theorem, and
[nested reactive menus](../Interaction/ReactiveMenuRestriction.lean) instantiate
its structural restriction. Their composition with a general source/native
correspondence remains open. Proposed backend certificates below are not
existing theorems. The [roadmap](se-preservation-roadmap.md) records current
results and broader research boundaries.

For the actual initialized fixture, [C/W/N menus](../VegasTests/MonitoredGuessingRestricted.lean),
[their inherited decision clocks](../VegasTests/MonitoredGuessingRestrictedClock.lean),
and the [W → N → T equilibrium extension](../VegasTests/MonitoredGuessingWatcherRaw.lean)
are checked. The watcher extension allows arbitrary fixed ordinary-player
utilities and requires watcher utility zero at every history. The raw lift
preserves every joint observation/payoff law invariant under the proved private
normalization. S → C and C → W
are still open; the existing guessing-game pilot is a separate completed result.

## Stack: one runtime, several strategic games

The emitted program still follows SourceProgram + Setup → EventGraph → native
application/service. The strategic proof uses the following derived games:

```text
S  Ordinary source game
   |  Compile through EventGraph; expand decisions into service blocks
   v
C  Native service with all source-representable choices;
   prescribed reporting; canonical private response representation
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

The actual fixture's W → N edge is checked. All traffic caused by ordinary-player deviations is already possible
in W. Its reporting decisions are therefore retained by the second extension.
New sites reached through watcher deviations receive rational completions.
This is a forward-existence argument: it does not establish strict reporting,
uniqueness, paid participation or coalition resistance. An interested watcher
needs a different incentive certificate.

The last two edges are composed for the fixture. The
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

### Immediate fixture

Use the actual [two-publication payoff-table family](../VegasTests/MonitoredGuessingPayoffs.lean):
valid initialized commitments, Bob's reveal followed by Alice's reveal, and
literal integer return tables. Keep **both opening and withholding at both
source decisions**, under arbitrary source strategies. The first S → C proof
must not rely on Alice opening in equilibrium.

For C, implement opening with the actual matching-certificate packet and
withholding with silence followed by expiry. This gives omission a source
meaning without assuming that passive packet monitoring detects silence.
An explicit withholding packet is then extra observable traffic. Prove this
implementation's service laws; the pilot's false branch transmits a withholding
packet and does not already establish the required silent branch.

For the generic enforcement route, ordinary-player payoff tables may be
arbitrary; the watcher is assigned zero utility. Every additional ordinary
response still needs an actual comparison certificate. This requires more than
the pilot's Alice-only rejected-receipt penalty.

### Reusable class after the fixture

Generalize by induction to finite sequences of guard-free revelations of valid
initialized commitments, in a fixed public order, with finite setup support and
arbitrary declared terminal payoffs. Owners may recur; setup types and
commitments may be correlated. Retain every source withholding choice. Express
membership as a predicate/certificate on existing programs, not new syntax.

Fresh commitment generation, deferred guards, adaptive activation calendars and
unbounded traffic are outside this first theorem. Initial binding validity is a
setup assumption. It does not establish a cryptographic setup protocol or
security under key/secret sharing.

### Calendar requirements to prove

- Fix the activation roster independently of player responses. Inclusion
  decisions may vary only within the proved service contract.
- A canonical owner response is followed by its inclusion attempt before any
  other player activation; expiry and the next decision follow the checked
  deadline schedule. Monitor extra-response windows separately.
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

## Early risks and decisive gates

Run these gates before committing to a general source adapter or a large
certificate extractor. Their outcomes determine the backend contract.

### G1. Recall required by the theorem

**Checked.** The native model uses an empty information value while a player is
inactive. [DecisionRecall](../GameTheoryExtensions/Protocol/DecisionRecall.lean)
requires equal own-play records only at genuine decision sites. The generic
completion, switching, one-shot and extension proofs use this premise, and
[every reactive response menu](../Interaction/ReactiveOwnPlay.lean) satisfies it
with the existing observations.

The branch-regret proof assigns zero allowance to non-decision information.
A [regression](../GameTheoryExtensionsTests/DecisionRecall.lean) checks that a
model failing global recall still satisfies this premise and admits an SE by
the generic theorem. Common decision depth is a separate calendar obligation;
no clock or memory observation is added to satisfy it.

The [full raw fixture](../VegasTests/MonitoredGuessingNativeClock.lean) has common
decision depths at all legal information sets: initial Alice at 2, Watcher at 4,
Bob at 8, and final Alice at 14. The C/W/N games inherit this certificate through
their actual history embeddings. Alice's two sites are distinguished by her
existing observations; the proof adds no public clock.

### G2. Effective responses versus invisible aliases

[ReactiveNormalization](../Vegas/Pending/ReactiveNormalization.lean) removes
ineffective opening material, failed owned-evidence requests, and forwarding
requests whose selected packet supplies no certificate. The owned check uses
the candidate after the same atomic submission, so fresh creation followed by
disclosure remains possible. Packet and submission effects are proved equal.
Withholding cannot register private commitment material; its irrelevant opening
field is a representation alias.

Successful requests can still have several private representations: an owned
request and a forward can carry the same certificate, as can forwards from two
known envelopes. Prove these alternatives unavailable on the first-use retained
histories of the fixture. Before generalizing to repeated owners, normalize or
lift the relevant successful-request aliases; their names are not punishable
public evidence.

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

The eight [concrete branch laws](../VegasTests/MonitoredGuessingRestrictedExecution.lean)
are checked, including the initial bit, both public results and zero pilot charge.
The [meaningful checkpoint inputs](../VegasTests/MonitoredGuessingRestrictedInformation.lean)
have one Bob input and four distinct Alice inputs, and both source choices are
legal at each checkpoint. Classification of all C histories and a consistent
assessment correspondence remain required.

The [reference-run support proof](../VegasTests/MonitoredGuessingRestrictedSupport.lean)
also classifies every legal C Bob decision as a quiet checkpoint, and every Bob
information site as the same source-representable input. The corresponding
all-history Alice classification and assessment proof remain open.

The existing compiler withholds a guard-rejected value:
[compiled_packet](../VegasTests/CommunicationNative.lean) checks that case.
Raw disclosure after guard failure is consequently an extra-action issue for
that compiler. Collapsing the source's true/false intentions into the same
packet is a separate recall obligation, deferred with guarded programs.

**Exit:** all source choices have faithful implementations, and all allowed C
behavior has a source account. Equality of initialized outcome laws alone is
insufficient. No selected equilibrium is used to define C.

### G4. Observable deviations by every player

A [checked operational witness](../VegasTests/MonitoredGuessingConformance.lean)
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
  comparator](../VegasTests/MonitoredGuessingRestrictedFinalComparison.lean),
  selected from Alice's information and the response. It preserves the terminal
  result and weakly increases her utility for arbitrary declared result tables
  and nonnegative rejection charges. No future player response is needed.
- At the quiet Bob checkpoint, [unselected Bob submissions](../VegasTests/MonitoredGuessingBobContinuation.lean)
  leave Alice's entire next input equal to the C silent branch. Known replay is
  unavailable there. The proof uses Alice's empty passive sample; a service that
  allows her to read this pending traffic needs a different comparison or
  additional monitoring.

These are actual service laws. Applying them inside the universal restriction
certificate still requires retained-history classification and the bridge from
service suffixes to behavioral continuation contexts. Bob's other included
packets require the proposed ledger charge and its exhaustive collection law.

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
silence/expiry clean. This is evidence availability, not full response coverage
or monetary collection. It identifies the original author, not a replay's
current broadcaster.

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
| C | Private submission/packet normalization and compiler compatibility. **Checked; successful-request alias coverage remains open.** | G2 | Prove unavailable or harmless on retained histories before extending to repeated owners. |
| D | Concrete C/W/N menus **checked**; service checkpoints and source assessment correspondence in progress. | B, C, G3 | Source observation and deadline correspondence dominate. |
| E | Generic persistent ledger evidence and concrete conformance witnesses **checked**; exhaustive ordinary-response comparisons and collection open. | B, G4, G5 | Check actual receiver observations and attribution before scaling D. |
| F | SE lifting over fixed service blocks in GameTheoryExtensions; source instantiation and payoff laws in Vegas/Game. | A, D | Large; one common consistent belief sequence is essential. |
| G | C → W → N → T composition and fixed deposits in Vegas/Game; **fixture W → N → T checked**. | A–F | C → W remains open; instantiate actual collectible utility and readout in the composed result. |
| H | Generalize fixture to the finite reveal class, then extract sharper finite rational certificates. | G | Separate increments; keep solver engineering off the first critical path. |

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
