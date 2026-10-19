# Concurrent SE mechanization

## Goal and order of work

The immediate deliverable is a checked end-to-end theorem implementing every
selected intended-source sequential equilibrium in the actual concurrent raw
phase runtime, under the explicit sufficient assumptions of the
[reviewed mathematical proof](se-reserved-service-preservation.md).
It must preserve the initialized joint input, public-outcome and realized-payoff
law, with no exclusions or audit charges on its paths.

Reach that theorem before broad cleanup or assumption minimization. Then use its
checked statement and instances to protect refactoring, simplification and
generalization. The long-term targets are NE preservation, asynchronous serial
SE preservation and asynchronous concurrent SE preservation on one operational
runtime, each with its own weakest justified assumptions. Sufficient assumptions
are not described as minimal merely because a proof uses them.

Fixed-calendar preservation is not a deliverable, intermediate milestone or
fallback. A source phase partition is a dependency/barrier structure, not a
script of activations and deliveries. Actual service orders and processing
times remain uncertain. Existing calendar dependencies may continue to compile
until their users are replaced; no new proof work is allocated to them.

This plan tracks the conditional reserved-service theorem. It does not close or
weaken obligations in the [asynchronous checklist](se-async-checklist.md).

## One operational runtime

Use `PhaseRuntimeState` and `phaseApplication` as the operational carrier for
the concurrent proof and the future common implementation. Preserve signed raw
submissions, immutable preparations, pending packets, receipts, deadlines from
readiness, authentic evidence, permanent exclusion, phase drain and
commitment-only checkpoint rollback. Source values do not change during the
publication interval.

Execution policy chooses graph dependencies, configured deadlines and service
rules. It does not create a second packet language, state machine or settlement
mechanism. Sequential and concurrent implementations should eventually differ
only in required dependency constraints and justified service requirements.
The underlying runtime should admit weaker service/observation policies than
the first concurrent theorem requires.

Existing NE results use `serviceApplication`; the checked serial recovery SE
result uses `recoveryApplication`. The phase dispatcher rolls back whole private
blocks, so graph-mode transport alone does not identify these games. Porting
those results requires an explicit simulation or a new proof over the common
carrier. That work is outside the first concurrent theorem's critical path.
The existing serial theorem remains a regression during this work.

Do not import the strong concurrent certificate into every runtime definition.
Keep operational data separate from finiteness/resource facts, service laws,
observation guarantees and economic assumptions. NE and serial SE must be able
to use weaker hypothesis sets without changing the operational semantics.

## Freeze the theorem contract first

Write the intended capstone type and its dependency contracts before splitting
implementation work. Runtime parameters, service law, utility bounds, exclusion
payoffs and audit funding are fixed before selecting the source equilibrium.
The constructed runtime assessment and its tremble sequence may depend on it.

The external assumptions are source well-formedness and the stated initial-law
conditions; finite representations/resources; the explicit reserved, correlated,
block-frozen service; complete pending observation; state-based utilities and
the global exclusion floor; and authentic audit coverage/funding. General
guards and raw deviations remain in scope.

The capstone must NOT assume source-posterior equality, counterpart existence,
pooled gain inequalities, rational reset continuations, survival of a proposed
client, or existence of the desired common consistency sequence. These are
proof obligations. Internal lemmas can expose adapters while being developed;
the final theorem must discharge them from operational hypotheses.

The payoff model is source-state utility with exclusion settlement and the
terminal audit. Additional gas, clock or traffic transfers need a separate
accounting argument. The theorem is about the bounded reactive runtime; an
always-online frontend and a particular chain's guarantees require explicit
refinement proofs. Neither follows from calling a scheduler asynchronous.

## Parallel implementation tracks

### Enriched source recovery

Use a focused concrete action/observation refinement of the existing auxiliary
`CommitRecoveryState`. Keep its semantic state, checkpoint, close, retry and
rank operations. Add a publication label representing a truthful proposal whose
delivery fails. Its logical projection uses the existing failed/withheld
successor; its observation retains the proposal computed from the pre-step
stored value. Guard-rejected truthful proposals must also be retained.

Prove one erase-step/trace projection to the existing protocol, then reuse its
debt, termination and readout facts through that projection. Accumulate the
typed proposal/address delta in perfect-recall public signal history.
`StepEvent` already supplies source state, joint move and target state. Derive
the canonical archive from that history instead of adding independent archive
state or copying the recovery implementation. Keep source-layer addresses
independent of native packet identifiers. The intended source semantics and
native phase application are unchanged. This is a mathematical refinement,
not a compatibility wrapper or a universal new refinement framework.

Refined observations and own recall retain the declared proposal; the base
semantic configuration/history records the projected action. Prove finiteness
from the existing bounded rank and finite added labels, not from injectivity
of the many-to-one trace projection.

Lift erasure, NoMiss and genuine-query proofs to these labeled traces, then
instantiate the existing component completion for the normalized pools.
Erasure preserves the archive because canceled opaque attempts
never published. At fixed failure controls prove actual Bayes/action-vector
equality; across NoMiss copies prove the affine form `c + d * V`, `d >= 0`.
Select one global pooled witness, preserving the selected intended assessment
and initialized law. Avoid changing the full existing information tuple across
its large dependency tree before the first capstone. The serial capstone does
not import this recovery tower, so its strategic proof need not be rewritten
to start this work. Consolidate the refinement into its final owning APIs after
the end-to-end contract protects that change.

The source constructor must accept caller-chosen omission, delivery-failure,
bad-preparation and domain-floor rates, with their positivity and convergence
conditions and explicit relative-passage/hierarchy bounds. These rate choices
precede free optimization. It returns the one pooled sequence, actual Bayes
beliefs, gain bounds, convergence and selected-source law. Do not hide rate choice behind an
existential that prevents the native track from imposing its required hierarchy.
The existing source construction already exposes this kind of rate control.

### Shared-epoch service on the actual runtime

Construct a scheduler family using existing scheduler-implementation and mixture
APIs. A finite arbitrary joint tape controls shared processing epochs and
bounded-gap owner activations, including variable owner order. Correlation is
allowed; the tape is independent of hidden source data and its law is frozen
through the full commitment/publication block.

Use reserved processing for all bounded raw traffic, with actual include,
activation, expiry and clock commands of `phaseApplication`. Derive opportunity,
receipt/completion for all raw policies, acceptance for timely valid packets,
same-tape monotonicity and foreign-service invariance. Malformed and late
packets need not be accepted.
`AsyncContract` alone does not supply these stronger properties. Independent
per-event seeds and the older private-success quotient are not substituted for
the correlated-tape construction.

Avoid a circular capacity bound. First bound logical clock ticks using finite
source/attempt/deadline progress. Bound submissions from that tick bound and
the activation-rate limit. Reserve enough processing slots for that traffic;
then derive the physical horizon and finally fresh-candidate capacity. All
these guarantees quantify over raw policies, not only intended clients.

Build a supported instance with two distinct owners simultaneously ready and
their valid packets pending together before processing, with two possible
service orders. Include a genuinely
correlated tape. This must be checked early, alongside the generic certificate,
so a vacuous or accidentally serialized service cannot satisfy the milestone.

### Native transport and incentives

Extend the actual observable source query with the canonical proposal archive.
Use complete pending observation and retained envelopes to reconstruct all old
truthful proposals before the next value decision, including guard and delivery
failures. Preserve actual early publication observations; use the pointwise
earliest-truth comparison there instead of asserting source-belief equality.

Define one fully mixed counted reference profile using the enriched source
domain laws, own-coordinate timing coins and actual submission-preimage alias
weights. Prove complete counted-menu coverage. Fix complete-response floors
before bad-preparation rates and before optimizing free components.

Prove the all-foreign bad-preparation shadow on complete focal input fibers.
Same handles/envelopes and forced publication WAITs preserve observations,
public Nature, failures and counts. The posterior bound has the form
`M * badRate / responseFloor ^ horizon`, tending to zero. Hidden utilities
need not be equal. Known own bad preparations use debt/reset arguments, not
rarity. On the remaining worlds derive the actual likelihood transport.

Retain the complete foreign failure/address record and old proposal archive in
retry couplings. Derive binding/source deviation comparisons, publication
ordering and uniform future-fault errors. Assemble all comparisons against
the SAME source and native consistency sequences.

## Integration and checked milestones

Source and service work start together after their interfaces are agreed.
Native query/menu work starts immediately; probability and incentive consumers
join as the source witness and service laws become available. Root coordinates
interfaces, integration and review; proof authors work on disjoint owning
modules. Implement whole dependency batches in parallel, build their targets,
fix integration errors, and run the full build at stable checkpoints.

These are new checked-statement milestones, not estimates of effort or counts
of helper lemmas. Each closes only with an actual theorem reference, its stated
quantifiers and a passing build. The labels below never enter Lean names.

| Track | Checked statement | Status |
| --- | --- | --- |
| Source | Proposal moves/signals retain guard- and delivery-failed values; intended restriction is unchanged | Checked: concrete intended restriction, information embedding and initialized full-history law; failed truthful disclosures remain in the proposal trace |
| Source | Archive-preserving erasure/NoMiss queries and pool antichains | Checked: genuine normalized representatives preserve the same labeled attempt-entry archive; full failure-control classification and query antichains are checked; see the source evidence below |
| Source | Actual conditional Bayes/action-vector exchange at fixed controls | Checked: original fully mixed Bayes beliefs, arbitrary legal action values and deviation gains agree on equal old erased-information/archive fibers; see the source evidence below |
| Source | Affine NoMiss comparison and one joint pooled consistency witness | Checked: one caller-rate pooled Bayes witness, ordinary-copy gain equality, failed-copy indifference and limiting retry comparison |
| Source | Enriched source SE extending the selected intended SE and joint law | Checked: all legal information sites, selected intended strategy and exact initialized full-history law; see the source evidence below |
| Runtime | Concrete correlated, block-frozen reserved scheduler family | Partial: joint tape and exact scheduler-mixture realization checked; block service certification remains open |
| Runtime | All-raw opportunity/receipt/completion, timely-valid acceptance and noncircular budgets | Partial: actual correlated-mixture AsyncContract, noncircular budgets, paired counted successor requests and protected fresh-successor receipts checked; whole retry/chain coverage remains open |
| Runtime | Same-tape admission monotonicity and foreign-service invariance | Partial: all-owner original acceptance words with exhaustive pending/rejected/unsent frontier classification and finite tape bits checked on one closing image; paired all-owner law remains open |
| Runtime | Complete proposal reconstruction and required fresh-slot reserve | Checked: actual full raw inputs reconstruct all submitted proposals, and the horizon reserve supplies fresh active slots; the counted execution fold identifies the same source archive; see the runtime evidence below |
| Runtime | Supported concurrent instance with variable service orders | Checked: both orders have supported actual prefixes with distinct owners' typed, timely, handler-admissible packets pending together; see the fixture evidence below |
| Transport | Genuine enriched native query, alias masses and full counted support | Checked: actual genuine enriched query, exact alias projection and full reference support on every original-law counted input, including earlier deviations |
| Transport | Good-store likelihood transport, including failed proposals | Partial: actual installed phase-word law and same-checkpoint scalar source getter checked; conditional full-input likelihood and chronological source-kernel identification remain open |
| Transport | Uniform foreign-bad posterior bound and separate own-debt cases | Partial: native and source full-input foreign-bad posterior bounds and observable saved-debt zero gain checked; current cancelable-debt reset comparison remains open |
| Transport | Publication timing dominance with actual early observations | Open |
| Transport | Whole-policy binding/retry comparison with the same reset continuation | Open |
| Transport | One native Bayes sequence with vanishing gain and initialized-law errors | Open |
| End-to-end | Counted SE and exact initialized joint law | Open |
| End-to-end | Raw SE, exact settled joint law, zero exclusions/charges and instantiated service | Open |

Compact progress display: **Source 5/5 · Runtime 2/5 · Transport 1/6 · E2E 0/2**.
Runtime frontier: all old frontier categories have exact bits in the original all-owner word; paired exit and outside-interval failure law next.
Transport frontier: actual installed phase-word law, both past-bad posteriors and observable saved-debt zero gain checked; conditional likelihood, chronological source law and current-debt/reset joins remain.
Update counts from checked statements and name the current bottleneck. Existing
reusable proofs are dependencies, not new completed milestones.
Current bottlenecks are the stopped service coupling, cross-world likelihood
transport and native deviation comparisons. The raw concurrent capstone remains open.

Checked prerequisites: `proposalRecoveryEraseTrace` preserves semantic endpoints;
`recoveryProposal_reveal_success` reads disclosed values from the pre-state;
`ReservedEpoch.realize` uses the existing scheduler-mixture semantics;
`ReservedEpoch.processing_epoch_clears` drains bounded pending traffic against
arbitrary raw policies; `PhaseProposal.observedArchive_eq_submitted` reconstructs
every submitted proposal from actual complete decision inputs; and
`PhaseProposal.archive_coordinate_unique` proves uniqueness on counted histories.
`PhaseProposal.splitResponseLaw_project` and
`PhaseProposal.splitResponseLaw_fullSupport` preserve a local response-class
law and give support to all its actual permitted preimages.
`proposalRecovery_supported_suffix_of_erased_history_eq` retains the complete
proposal transcript through supported suffixes. The caller-controlled encoder
has full support and `proposalRecoveryTrembledDomainLaw_value_lower` gives an
ordinary-response floor independent of optimized domain weights.
`PhaseProposal.submitted_proposal_binding_meaning` recovers each counted
proposal's actual original callback and successful typed binding.
`proposalRecovery_lift_joint_word` decorates the original trace and chance
outcomes; `proposalRecovery_info_eq_of_semantic_public_coordinate` reconstructs
full enriched information from semantic information, proposal chronology and
the owner's labeled choices. These do not assert a conditional Bayes identity.
`proposalRecoveryArchive_eq_of_same_address` makes the canonical archive a
partial function of its address; `proposalRecovery_prefix_eq_of_same_query`
proves that normalized-query copies form an antichain along actual histories.
`PhaseProposal.recorded_disclosure_submitted` traces recorded truthful openings
to actual submitted packets even when their guard excludes the author.
`source_proposal_delta_of_readback` retains exact typed proposal values through
the existing source-order replay; whole enriched-history correspondence still
requires matching physical publication attempts to source generations.
`consumed_publication_phase_archive` identifies the exact archive of one
consumed publication phase on that same annotated source replay, retaining
guard-failed and expired submitted disclosures. The global normalization and
counted execution archive fold and archive-preserving virtual query repair are
checked below.
`PhaseProposal.sourceArchive_future_bucket_empty` rules out submitted proposal
buckets from future physical phases on arbitrary raw histories; it also applies
to later phases drained inside one environment step.
`ReservedEpoch.clock_history` accounts for every physical tick;
`ReservedEpoch.expiry_round_decreases` gives strict finite-work progress at an
actual due-expiry round. `ReservedEpoch.runRounds_complete` bounds all-raw
completion by `(workBound + 1) * (maximumDeadline + 2)` cycles, independently
of packet capacity. `ReservedEpoch.implementation_terminal_history_complete` derives
completion for every raw history under the actual correlated mixture and an
arbitrary initial input law. It extracts a supported original tape rather than
assuming a pointwise service property survives behavioral mixing. Packet
capacity and the physical horizon are derived from this cycle bound; timely
service and the remaining coupling obligations are separate.

`proposalRecovery_information_fiber_equiv` gives an invertible map between
complete histories with matching erased information and proposal archives.
It preserves the initialized chance path, all proposal chronology, opponents'
full enriched information and the actual erased history.
`proposalRecovery_bayes_eq_of_erased_information_archive` transports the actual
fully mixed Bayes beliefs through this map. These statements include failed
disclosures. `proposalRecovery_bayes_stopped_eq` and
`proposalRecovery_bayes_terminal_eq` extend the comparison to actual stopped and
terminal full-image laws under normalized continuations, using the existing
stopped-kernel comparison engine.
`proposalRecovery_conditional_value_eq`, `proposalRecovery_baseline_value_eq`
and `proposalRecovery_conditional_gain_eq` prove the corresponding action
vectors and deviation gains for the original fully mixed Bayes assessment.
`proposalRecoveryComponentChoice` is an equivalence with the entire legal
menu, so these comparisons cover arbitrary legal action laws, including all
valid proposal labels. The shared prescription is an internal strategy
representation, not an assumed belief or continuation-law equality.
These are fixed-control copies: their old erased information and proposal
archive agree. The limiting retry comparison and selected source SE are checked below.
The source dependency tests pin the standard axioms for these hard consumers.
`ReservedEpoch.implementation_asyncContract` supplies opportunity, receipts and
completion under the actual mixed scheduler, for every raw history and
arbitrary initial input law, at the derived capacity and horizon.
`ReservedEpoch.implementation_first_submission_admissible` proves immediate
first-response handler admissibility, while
`ReservedEpoch.active_fresh_candidate` supplies a fresh slot at every active
raw decision when the candidate reserve covers the horizon.
`PhaseProposal.observedSourceArchive_eq_submitted` gives the typed source-address
readout from the same complete raw input. Arbitrary raw proposals are not
assumed to form a functional source archive. Accepting first-response receipts
are checked below; complete sender coverage and same-tape incentive couplings
remain separate obligations.

`proposalRecovery_query_ordinary_of_history` constructs a genuine normalized
representative from the same labeled attempt-entry prefix, preserving its full
proposal archive. `proposalRecovery_query_fiber_cases` classifies the remaining
copies using their actual failure controls. Together with the existing query
antichain, these supply archive-preserving NoMiss queries.

`exists_consistent_proposalRecovery_pool` constructs one fully mixed Bayes
sequence and common consistent limit with caller-selected rates and domain
floors. `proposalRecovery_pooled_ordinary_component_optimal` transfers its pooled
conditional bound to each ordinary component. The ordinary agents have the same
actual conditional gain and positive cardinality; the complement contributes
zero by the actual failed-attempt law and the derived common omission marginal.
`proposalRecovery_normalized_accepted_failure_conditional_value_le` compares an
unusable declaration with the same attempt's domain choices under the actual
stopped law. `proposalRecovery_pooled_ordinary_limit_domain_optimal` and
`proposalRecovery_normalized_failed_limit_localOptimal` transfer the pooled
inequality through the same limit: ordinary copies share their conditional
gain, and failed copies are indifferent at the same omission marginal.
`proposalRecovery_pooled_commitment_limit_localOptimal` covers the entire
legal commitment menu; the noncommit consumer covers all other sites.

`exists_proposalRecovery_sequentialEquilibrium_construction` supplies the
enriched source SE extending the selected intended SE. It returns the original
caller-rate sequence, shared domain weights and fully mixed Bayes assessments,
with one strict subsequence for their common limit. Its initialized law is an
exact pushforward of the entire intended history, retaining the original
initializer and Nature draws; the outcome and payoff vector follow jointly.
`exists_proposalRecovery_sequentialEquilibrium_extension` derives the auxiliary
sequence, positive reach bounds and rates directly from any supplied intended
SE, with no extra witness or history-finiteness assumption at that interface.
The floor assumption here is the source payoff lower bound. Native settlement
and its required deterrence bounds remain separate obligations.

`ReservedEpoch.implementation_first_response_receipt` proves accepting delivery
for a certified valid response at the first offered callback, with the sender's
count-sound prefix and counted continuation and arbitrary foreign raw play.
The certificate supplies a binding call or an opening of the currently accepted
candidate; handler success is derived, including for semantically rejected guards.
`ReservedEpochCertifiedConcurrency.valid_concurrent_service` joins the actual
resource bounds, mixed service contract, timely deadlines and candidate reserve
with supported concurrent prefixes in both service orders.

`recoverySourceCheckpoint_proposalArchive_history` folds actual counted
executions from the original setup law, retaining the same chosen source
checkpoint and its consumed archive. It covers submissions, inclusion, expiry
and automatic normalization. Surviving observers retain proposals from every
author, including authors subsequently excluded. `ArchivedProposals.binding`
reads the complete archive at commitment decisions.
`proposalRecovery_virtual_labeled_archive` preserves that same archive through
the actual virtual repair. `phaseProposalQuery?_genuine_of_counted_binding`
then derives a genuine enriched source decision, its actor and rank from the
actual counted trace, with proposals from every author retained.

`phaseProposalBaseClasses_fullSupport_of_counted` proves full support at every
original-law counted input, with arbitrary earlier deviations, omissions and
debt. `phaseProposalReferenceClasses_eq_of_counted` removes the support fallback
there, and `phaseProposalReferenceResponses_project_of_counted` identifies the
actual alias marginal. These use complete pending observation, covered typed
values, maximal phases, full-support domain laws and positive tremble rates;
they require neither a clean history nor a supplied source counterpart.

The concrete fixture is checked for every source input bit and both service
orders. `ReservedEpochConcurrency.concurrent_prefix_supported` supplies the
actual mixed-scheduler prefixes; `two_packets_pending` and
`distinct_pending_owners` give simultaneous distinct-owner traffic;
`pending_binding_timely`, `pending_binding_admissible` and
`pending_binding_usable` give actual deadline, handler and typed-preparation
validity. `correlated_order_and_epochs` ties the activation order to processing
availability, so this is not an independent-delay or fixed-order instance.
`ReservedEpoch.processing_epoch_application` reads the actual FIFO evaluator;
`processing_owned_packet_congr`, `phase_owned_expiry_pair` and
`phase_binding_successor_pair` transport real receipts and normalization under
the same initial world. These are operational consumers, not the whole stopped
service coupling or a cross-world likelihood theorem. Those joins and the
native incentive/consistency assembly remain open.

`counted_processing_owned_successor` derives the counterpart successor request
from actual paired counted FIFO processing and accepted-handler provenance.
`successor_response_receipt` derives first-response protection from an actual
unfinished predecessor and the unchanged enabling-step recall. The excluded-owner
drain retains the consumed attempt's accepted/catalogue binding record. These
are single-step and chain-drain consumers, not the whole stopped-attempt law.

`BindingShadow.PhaseStateFrame.normalize` transports actual settlement and
checkpoint restoration with a dynamically restricted output mask, arbitrary
existing exclusions and retained public archives.
`BindingShadow.include_owned_binding_external_of_history` constructs the paired
accepting handler and preserves the complete external observation, including
every other player's entire recall and current input. The actual expiry
consumer similarly passes through general normalization. Whole chronological
repair and its posterior likelihood estimate remain separate obligations.

`CompiledSuffix.resolve_read_cone` bounds actual compiled resolve-node reads
using registry and revelation bounds derived on the same compiled suffix.
Current-block publication operands are the author's own; other operands precede
the block. This is a guard-operand result, not publication timing dominance.
`proposalRecovery_future_foreign_flags_withinTV` compares complete source future
histories from any starting history, keeping an arbitrary focal policy fixed.
Its uniform error has no conditioning-reach denominator.

Native clean-future transport must use the actual selected virtual source query.
Ordinary typed values with rejected guards remain literal. Own unusable-binding
repair can change the query key, so arbitrary policy tables cannot be identified
across that repair: focal unusable choices need the same-reset or standing-debt
floor argument, and past foreign unusables need the separate posterior bound.

Use the existing component/pooled completion, asymptotic likelihood, affine
comparison, local-simulation limit and terminal-audit engines. The underlying
`PhaseCount.onePacket_raw_sequentialEquilibrium` provides the final audited raw
extension with the joint law of complete terminal history and settled payoffs.
Project the initialized input and public outcome together from that history to
retain the required full joint law. Its specialized
`phase_counted_raw_sequentialEquilibrium` wrapper exposes terminal-store readout
and payoffs. Reuse the existing enforcement proof for the broader projection.

## Protect the result, then simplify

The capstone and concrete service instance enter default build roots. Add an
explicit theorem-application contract with exactly the approved hypotheses;
axiom checks alone do not detect added assumptions. Pin standard-axiom guards
and actual dependency checks for the new capstone and its hard consumers.
The evidence checker currently roots calendar theorems; concurrent evidence
must be rooted in the concurrent capstone, not credited through those roots.

Required regression cases exercise two owners' valid packets pending together,
correlated orders, general rejected guards, a truthful late opening that
discloses then fails, indistinguishable unusable/withheld openings, and commitment retries with
retained catalogs. They test the theorem's hard cases, not duplicated helper
implementations. Preserve the current serial theorem during source changes.

At stable checkpoints run plain `lake build` under the centralized strict
options, module/build-root checks, source-policy checks, documentation checks,
theorem-evidence checks and the repository check tests. Commit and push each
verified checkpoint. Completion requires a built raw capstone with all adapters
discharged, a nonvacuous instantiated service and no admissions or extra axioms.

Afterward, keep this contract passing while extracting shared operational
adapters, merging duplicated proofs and removing unnecessary modules. Make the
serial SE and NE results operate on the same phase carrier, with explicit
proofs of their semantics and their own assumption sets. Remove calendar
dependencies and obsolete APIs once their actual users are migrated; no
compatibility aliases or duplicate legacy implementations are required.

Track every hypothesis to its uses. Separate proof artifacts (tremble hierarchy,
floors and pooling choices) from runtime requirements. Weaken resource bounds,
initial independence, observation completeness, service freezing/isolation and
the payoff floor individually only when the corresponding checked theorem
supports it. Do not substitute NE consequences of the SE theorem for a direct
NE result with weaker assumptions. Backend fees, cryptographic hiding/finality
and an always-online submission interface remain explicit refinement tasks.

The [stopped binding proof](../Vegas/Game/ReservedEpochStoppedBinding.lean)
classifies every newly excluded owner by its literal earlier request and
original no-acceptance record; fresh prescribed successors cannot miss.
The [saved-debt payoff proof](../Vegas/Game/PhaseProposalReservedDebt.lean)
derives permanent exclusion and exact continuation payoff under arbitrary raw
and behavioral futures, using actual reserved-service phase exhaustion.
The [ordinary draw](../Vegas/Game/PhaseProposalOrdinaryDraw.lean) and
[emitted draw](../Vegas/Game/PhaseProposalEmittedDraw.lean) identify the actual
current preparation PMF with the shared table on the SAME chosen source replay.
The actual fresh stopped commitment-phase word law is checked below.
Conditional likelihood at intermediate information fibers and identification
with the chronological literal-source continuation remain open.

The [repair trace inclusion](../Vegas/Pending/PhaseProposalShadowIncludeTrace.lean),
[environment transport](../Vegas/Pending/PhaseProposalShadowEnvironment.lean)
and [truthful opening](../Vegas/Pending/PhaseProposalShadowOpening.lean) construct
actual matching operations with general guards, retries and complete external
recalls. The [intrinsic chance bound](../Vegas/Game/PhaseProposalRepairChance.lean)
uses the fixed finite native game and its existing own-play factorization.
Together with the initialized history repair below, these cover the whole
physical repair and its checked posterior estimate. The paired stopped law
and concurrent equilibrium theorem remain open.

The [initialized history repair](../Vegas/Pending/PhaseProposalShadowHistory.lean)
constructs an actual counted trace under the original joint initializer and
scheduler, preserving every other owner's complete recall and own-play word.
It covers rejected packets, general guards, existing exclusions and retries;
submitted typed meanings persist independently of canceled logical cells.
Its quantitative posterior bound is checked below.

The [original stopped image](../Vegas/Game/ReservedEpochStoppedImage.lean)
retains the actual closing operation, original accepted table and old proposal
archive before checkpoint restoration. The
[whole-word readback](../Vegas/Game/PhaseProposalCommitWord.lean) identifies each
recalled preparation at its original rank in the same decoded source attempt.
Neither statement assumes or proves the complete phase probability law.

The [generated-preparation posterior](../Vegas/Game/PhaseProposalPreparationPosterior.lean)
proves `exists_phaseProposal_generatedPreparation_posterior_bound` and its
all-foreign-owner union bound at every positive full native decision fiber.
The intrinsic chance and length constants are fixed before response rates;
the complete repaired-response floor is fixed before bad rates, source pins
and free pool weights. The estimate preserves the original joint initial draw
and cancels every non-designated owner's literal response-word factor.
It does not establish the separate conditional ordinary-world likelihood law
or discharge current cancelable own debt.

The [original owned word](../Vegas/Game/ReservedEpochStoppedWord.lean)
proves `phaseProposalUnflagged_stopped_owned_word` on the actual stopped run.
Each existing anchor request determines its entire owner's accepted suffix;
active owners with no old frontier have every row accepted. The actual
pre-normalization closing image, candidate tables, failure/address record and
old proposal archive are retained. `original_binding_receipt_accepted` reads
the exact handle from the actual closing primitive, including an inclusion
which itself closes the attempt. Inherited-excluded rows remain literal, and
the retired list appends exactly the original drained record when a new miss
occurs. Every pending frontier substitutes the actual finite next-processing
epoch bit into this SAME closing image, including absent or out-of-horizon
epochs. The unsent first-offer-versus-due-expiry bit and the rejected-packet zero bit
are checked on this same image, with exhaustive frontier classification.
The paired all-owner exit law remains open.

The [observable binding debt](../Vegas/Game/PhaseProposalOwnBindingFailure.lean)
uses the original typed own source view and its saved-rank projection. The
[checkpoint bridge](../Vegas/Game/PhaseProposalObservableDebt.lean) identifies
the SAME actual saved source checkpoint, retaining canceled own attempts only
as memory. The [information-fiber payoff](../Vegas/Game/PhaseProposalObservableDebtPayoff.lean)
proves `phaseProposalSavedBindingFailure_gain_eq_zero` for arbitrary beliefs
and whole-policy alternatives on the ENTIRE full native information fiber.
Current cancelable debt still needs the separate paired reset comparison.

The [stopped pending tape word](../Vegas/Game/ReservedEpochStoppedTapeWord.lean)
extends the literal closed prefix using the existing behavioral evaluator.
`stopped_pending_binding_receipt_iff_epoch` gives the old packet's exact bit at
original attempt closure, with the original readiness stamp and finite epoch
bound. The [retired receipt proof](../Vegas/Game/ReservedEpochRetiredReceipt.lean)
rules out a later first accepting receipt after that namespace is retired.

The [fresh commitment-phase law](../Vegas/Game/PhaseProposalBindingPhaseLaw.lean)
proves `phaseProposalUnflagged_stopped_binding_word` for the actual anchored
asynchronous stopped run. It derives the supported callback frames and returns
the original closing trace and full drained recovery state, including its
accepted table, permanent exclusions, saved entry and proposal archive. Its
addressed binding-word projection has the frozen canonical continuation law.
The [entry archive](../Vegas/Game/PhaseProposalBindingKernel.lean) refreshes
pending identifiers only in the auxiliary potential; runtime observations are
unchanged. Actual first-entry installation is derived below. Chronological source-law
identification and the conditional skeleton likelihood are still required.

The [source past-preparation posterior](../Vegas/Game/ProposalRecoveryPreparationPosterior.lean)
and [foreign-owner union](../Vegas/Game/ProposalRecoveryForeignPreparationPosterior.lean)
bound the actual source Bayes mass on every full positive observer fiber.
The [selective initialized repair](../Vegas/Source/ProposalRecoveryPreparationRepairHistory.lean)
works even when the repaired owner is excluded. It keeps every other owner's
full information and own play, original initialization and all proposal labels.
The intrinsic chance constants and positive response floor precede bad noise,
source pins and free pool weights; running-history prescriptions match the
actual common source witness. This supplies the source past-bad error, not the
conditional native likelihood identity.

The [actual installed word](../Vegas/Game/PhaseProposalInstalledWord.lean)
derives the fresh idle entry, equal saved/current exclusions and archived
source checkpoint from the real original history. Its
[same-checkpoint scalar getter](../Vegas/Game/PhaseProposalBindingSourceKernel.lean)
identifies the frozen draw with an actual source trace on the live-values
branch. The full chronological source kernel, including inherited-excluded
automatic steps, is still a composition obligation.

The [old unsent binding](../Vegas/Game/ReservedEpochStoppedUnsentBinding.lean)
uses the first actual owner offer or due expiry before the original closure.
`ReservedEpoch.UnsentQualification` retains the original readiness stamp and
finite processing horizon; it has no value, policy or final-clock argument.
The original whole word internally classifies every old request as unsent,
pending or already rejected and attaches its exact acceptance bit to the SAME
raw/drained image. Outside-interval failure equality and the paired joint
failure/address/ordinary-value law remain open.
