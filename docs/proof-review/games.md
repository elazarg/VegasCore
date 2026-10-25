# Vegas.Game proof review and implementation

The conditional-prior recovery route, product timing bounds, recorded-entry
reuse and commitment-interval ports pass the complete production build.
The full unconditional-prior specialization, correlated-prior regression,
twenty review experiments and exact standard-axiom audit pass. The
[main review](../proof-review.md) records integration and measurements.
GameTheory, source/runtime execution rules and the fixed SE checklist remain
unchanged.

## Public signals throughout the actual recovery proof

The production recovery theorem now accepts private initial cells independent
conditional on a publicly determined signal. Its two prior guards are
`setup.PrivateInputsIndependentGiven signal` and
`setup.PublicInitialSignal signal`. The latter is the exact factual property
`Vegas.SourceProgram.Setup.PublicInitialSignal` in
[OnePacketPublicInitialSignal](../../Vegas/Game/OnePacketPublicInitialSignal.lean):
agreement on every public compiled initial input implies equality of the
signal. It does not require agreement on private inputs or add public leakage.

The same owner contains `Vegas.splice_public_initial_inputs` and
`Vegas.public_signal_preserved`. They prove that hidden-cell splicing preserves
every public initial input and consequently every signal satisfying the public
observability guard. The public-aware `Vegas.ownerSwap_baseLawAgrees` and
`Vegas.ownerSwap_baseLawAgrees_late` derive preservation internally. The lower
prior-scaling theorem retains its more general explicit preservation premise.

The source/native bridge is in
[OnePacketSplicePoint](../../Vegas/Game/OnePacketSplicePoint.lean).
`Vegas.initial_public_cells_eq` and `Vegas.initial_public_inputs_eq` derive
source-public-input equality from both actual `Vegas.InitialCellsAt` witnesses
and `Vegas.PublicCellsAgree`. `Vegas.drawn_splicePoint` then establishes support
of the actual spliced draw within the signal fiber. These are factual
producers, not assumptions that a desired law or posterior already agrees.

`Vegas.forcedAgent_of_splice` in
[OnePacketSpliceForced](../../Vegas/Game/OnePacketSpliceForced.lean) uses that
bridge with public agreement derived from its existing source-view equality.
Its well-formedness, covered binding fields, decoded/intended points, static
point, ready-own condition, changed-commitment success, arbitrary trace prefix
and non-focal responder guards are retained. The original complete forced-agent
consumer and the factual public-signal adapters were checked in isolation.

The implementation threads these guards through the actual responder repair,
`Vegas.reach_le_counterpart_certificate_of_repairs`,
`Vegas.OnePacketCounterpartInputs.ofBindingRepairs`,
`Vegas.RecoveryOnePacket.nativeBaseInputs`, late-record comparisons and the
recovery value/comparison chain. The resulting production root is
`Vegas.recovery_intended_raw_sequentialEquilibrium_preserved` in
[RecoverySequentialCompilation](../../Vegas/Game/RecoverySequentialCompilation.lean).
Its conclusion still covers the actual raw-menu assessment, sequential
rationality at its continuation contexts, zero equilibrium count charges and
the joint law of typed source readout and realized settled payoffs. Finite
Nature/source-history, service/opportunity/inclusion/completion, payoff bounds,
capacity, coverage, deposits and all original deviation/opponent scopes remain.
The public wrapper in [Paper](../../Paper.lean) has the same conditional guards.
The complete production root and public wrapper pass their normal builds and
exact standard-axiom guards.

The existing stronger `Vegas.ownerSwap_priorClosed` remains an unconditional
mathematical statement without a same-public-key guard. It is not used to
smuggle unconditional independence into the conditional recovery route.

Two scope checks accompany the implementation:

- [ConditionalPublicPrior](../../VegasTests/ConditionalPublicPrior.lean) contains
  `VegasTests.ConditionalPublicPrior.publicInitialSignal` and
  `VegasTests.ConditionalPublicPrior.conditional_scope_is_strict`. The actual
  nondegenerate eight-state noisy-public-bit prior satisfies both new guards
  and fails unconditional private-input independence. Its splice-preservation
  regression instantiates the generic public-signal theorem.
- An isolated exact consumer retains the complete original unconditional
  public theorem's header and full SE/no-charge/joint-law conclusion. It
  specializes the generalized root to the Unit signal, using unconditional
  independence pointwise. This is a scope regression, not a production
  compatibility alias. Its exact guarded replay passes in the
  [probe appendix](checked-probes.md#independentrecoveryscope).

The conditional implementation spans 27 existing Game modules and adds 166
production lines. This includes 163 lines in the 26 unshared owners and 3
conditional-prior lines in the shared late-record owner; its normalization
changes are counted separately. The permanent scope regression adds 12 lines separately. This adds mathematical coverage rather than compressing proofs. Existing machinery
supplies the conditional cross-product identity, support closure and common
ratio. The substantial work is the actual source/native adapter and complete
constructor propagation, rather than a new probability framework.

## Product retention through settlement and Nash ports

`Vegas.TurnTiming.deferralError` in
[SourceServiceTurnPolicy](../../Vegas/Game/SourceServiceTurnPolicy.lean) is

```
delta = 1 - product(event, 1 - deferral(event)).
```

The production owner
[ServiceTimingCoupling](../../Vegas/Game/ServiceTimingCoupling.lean) now exposes
`Vegas.overriddenTurnProfile_fix_roundsFrom_bind_lower`. For every readout
outcome it proves

```
(1 - deferral(event)) * P(fix event at zero, outcome) <= P(timing, outcome).
```

The proof uses the actual full run's timing-slot mixture from initialization;
the empty recall identifies its posterior with the original timing law. The
common-start lift instantiates the existing supported-domination API. Unowned
events and overridden owners have exactly equal laws. The all-event lower bound
`Vegas.overriddenTurnProfile_roundsFrom_bind_lower` composes these inequalities
multiplicatively, and `Vegas.overriddenTurnProfile_roundsFrom_bind_within`
converts the retained mass to total variation. Initial law, scheduler, horizon,
execution mode, deadline, source profile, arbitrary policy overrides and common
readout remain arbitrary. **No statistical-independence premise is added.**

`Vegas.TurnTiming.deferralError_mem_Icc` bounds the error between zero and one;
`Vegas.TurnTiming.deferralError_le_sum` recovers the additive bound. Two
deferrals of 0.2 yield 0.36 instead of 0.4.

The production honest/deviated wrappers and
`Vegas.sourceServiceTurnPolicy_execution_settlement_lawError` in
[SourceServiceTurnSettlement](../../Vegas/Game/SourceServiceTurnSettlement.lean)
use this error. The settlement theorem preserves its actual typed-outcome and
sampled audited-payoff joint law, first-turn source law, timely asynchronous
contract, authentic partial audit, utility and deposit parameters. Its complete
actual consumer was already checked with the product bound in isolation.

The product error is now propagated through the production value and
best-response bridges in
[AsyncServiceNash](../../Vegas/Game/AsyncServiceNash.lean), including
`Vegas.AsyncServiceSpec.isεBestResponse_of_clientProfile` and
`Vegas.AsyncServiceSpec.isεBestResponse_clientProfile_of_firstTurn_bounds`.
The approximation error is `epsilon + 2 * timing.deferralError * range who`.
Raw-menu, intended, opening and monetary clients in
[AsyncServiceRawNash](../../Vegas/Game/AsyncServiceRawNash.lean),
[AsyncServiceDeviationBound](../../Vegas/Game/AsyncServiceDeviationBound.lean),
[IntendedAsyncNash](../../Vegas/Game/IntendedAsyncNash.lean),
[IntendedOpeningNash](../../Vegas/Game/IntendedOpeningNash.lean),
[ProgramPaymentAsyncNash](../../Vegas/Game/ProgramPaymentAsyncNash.lean) and
[Paper](../../Paper.lean) are ported. Their complete production verification passes in the normal build; it is not
inferred solely from the isolated coupling proof. Actual admissibility, full native-deviation scopes
and realized audited-payoff ranges remain load-bearing.

This is a quantitative strengthening with code growth, not a proof-shrink
claim. Event-specific payoff oscillation remains a separate unproved
refinement requiring continuation-value guards. Excluding the overridden
player's owned-event factors from a forward deviation error is another
unimplemented refinement; reflection compares two honest profiles and does
not get that reduction.

## Terminal-supported count bounds

The production
`Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported` in
[RecoveryCountIncentives](../../Vegas/Game/RecoveryCountIncentives.lean) now takes
base-payoff interval bounds only on actual protocol-terminal states. Its bad
committed, safe and aggregate continuation laws use their actual terminal
support. Integrability follows from these support bounds and the existing
terminal-continuation API, rather than an assertion about arbitrary laws.
`GameTheory.Enforcement.TerminalAudit.utility_abs_le` in
[TerminalAudit](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
bounds audited utility by the actual base bound plus the absolute deposit.
The strict collected-deposit margin, all information histories, all admitted
opponent policies, safe comparator and coverage guards remain. The complete production port and its terminal regression pass normal
integration and exact axiom checking.

The public cleanliness guard is now stated on the observed own outputs;
`Vegas.EventGraphRuntime.Recovery.ownerCountClean_of_past` establishes the
corresponding fact for every actual information-fiber history using InputRecall.
The separate [runtime report](runtime.md) owns the locality proof and its
missing-recall obstruction. One selected clean anchor does not suffice.
Terminality includes horizon exhaustion and unfinished graph/source outcomes,
including the runtime default output and audit charge. Bounds on completed
source outcomes alone remain insufficient.

## Exact recorded-entry reuse

`Vegas.recordsEntry_transition` in
[OnePacketFirstActivation](../../Vegas/Game/OnePacketFirstActivation.lean)
instantiates `Interaction.ReactiveApplication.transition_recall_prefix`.
The unchanged statement preserves the exact ordered split
`earlier ++ entry :: later`, extending it to
`earlier ++ entry :: (later ++ tail)`. It does not weaken the result to entry
membership. Arbitrary initial law, scheduler, horizon, joint response and
transition-support premises remain. Event-success, openable/unintended
commitment and recovery foreign-failure callers require no adapters.

The complete producer declaration changes from 40 to 20 physical lines:
**20 lines removed**, with no new owner API or wrapper. The exact isolated
consumer and the production owner pass strict checking.

## One commitment-interval descriptor for four actual consumers

`Vegas.CompiledSuffix.commitPrefix_bind_interval` in
[ServiceCommitTail](../../Vegas/Game/ServiceCommitTail.lean) is the public
interface for an event in `[offset, offset + count)`. The existing indexed
structural induction is private. The interval proof obtains a residual index
from the actual suffix count equality, the event's whole-graph bound and its
rank equality; it needs no service execution or desired-law hypothesis and
no high-level `CommitPrefix.le_eventCount` import.

All four production consumers now instantiate this owner:

- `Vegas.HonestLaw.commits_step` in
  [ServiceHonestLaw](../../Vegas/Game/ServiceHonestLaw.lean);
- `Vegas.asyncDeviation_deviationLaw` in
  [AsyncDeviationLaw](../../Vegas/Game/AsyncDeviationLaw.lean);
- `Vegas.asyncDeviation_withholdLaw` in
  [AsyncWithholdLaw](../../Vegas/Game/AsyncWithholdLaw.lean);
- `Vegas.ConcurrentPhaseEnds.boundary` in
  [ServiceOpeningHonestLaw](../../Vegas/Game/ServiceOpeningHonestLaw.lean).

Their sealed/block boundaries, relaxed execution order, deadlines, scheduler,
source profile and full behavioral-law guards are unchanged. There is no new
prefix hierarchy or result certificate. Four 16-line blocks become four
2-line calls: 56 lines removed, with 29 physical lines added at the common
owner, for **27 net lines removed across the complete family**. Together with
recorded-entry reuse this removes 47 lines. The actual interval owner and all
four complete consumer modules pass the normal owning build.

## Coverage and rejected leads

The fresh surface scan covers 824 Vegas.Game Lean files, about 270845 physical lines, plus Paper.lean. `games-surface.txt` was generated through lean-defs.py. Lexical scans found 4880 theorem/lemma/def heads and 4431 cross-file exact 10-nonblank-line windows; these are search aids, not checked declaration counts or proof-size measurements. Deep reads focused on current conditional-prior/source-splice and counterpart pipelines, recovery comparisons and gain bounds, count incentives/terminal/audit guards, exact first-entry provenance, async service law families, typed compiled suffixes, timing coupling, audited settlement and actual native best-response consumers. This is broad inventory plus selected complete deep reads, not a claim to have manually read every line of the entire Game family.

Important rejected/limited leads:

- The highest 8-file Recovery windows (CommitBeliefValue, CommitmentComparisons, GainBounds, DisclosureComparison, KeyedCommitmentComparisons, NonLateNativeComparisons, SilenceComparison, UnintendedComparison) largely repeat **return-type let scaffolding**. The prior parser mistook the first return-type `let ... :=` for the proof assignment. Their actual proof tails are small/generic already. They do not support a whole-family proof-saving claim; the shared Python scanner is now corrected.
- Three first-activation consumers repeat a small setup and tuple unpack. After the genuine helper header and needed factual hypotheses, savings appear only ~5-20 lines. No proposal is ranked without a complete whole-family pilot.
- Four scale-limit consumers have similar vanishing arguments, but some already instantiate the existing scale_vanishing methods. A new wrapper would need the long actual native-input context and can cost as much as their ~10-line proofs. No larger compression claim is justified.
- `Vegas.exists_outcome_of_read` is a 14-line private choose/factorization helper with two uses. Mathlib `Function.FactorsThrough`/the extension evaluation lemma fit mathematically, but supported-subtype and fallback plumbing likely erase the savings. Do not introduce an unused factorization API.
- Native one-packet finite history already follows from the finite native menu via `Interaction.ReactiveApplication.ResponseMenu.historyFintype`; `RecoverySequentialCompilation` already installs it. This does not remove unrestricted source-action or global consistency obligations. No global finiteness removal is proposed from bounded horizon alone.
- An EventCode at binding-kind output has only the bind constructor, suggesting a potential typed nodeView_bind_of_binding simplification. The current codeEq argument may be redundant, but a broad NodeView/datatype change has hundreds of consumers and no measured whole-family gain. Not ranked.
- No counterexample to an existing production theorem or theorem-scope bug was established in these selected families. The implementation retains actual payoff/integrability, positive-normalizer, full-information-fiber, deviation/opponent and runtime/source guards. Whole-build acceptance is distinct from the checked isolated kernels.
