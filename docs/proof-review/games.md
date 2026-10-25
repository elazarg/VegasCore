# Current Vegas.Game proof review and mining

The production Lean baseline is `ec4de15c`. This report identifies remaining
opportunities and separates checked probes from production migrations. No
production Lean, GameTheory source, gitlink, SE target, checklist or semantics
is changed. Experiments are reproducible from the [probe appendix](checked-probes.md).


## Ranked findings

### 1. The missing public-source-splice adapter is provable from existing factual guards

**Value:** a real new producer closes the previously missing bridge from public source observations to conditional-prior splicing. This is stronger than a proposed adapter assumption. **Status:** `SourcePublicSplice.lean` (146 physical lines) strictly checked with the central Lake options, actual exit 0. It includes the full current forced-agent consumer proof, not only an abstract helper.

Current owners and gap:

- `Vegas/Game/OnePacketSwapInputs.lean:189`, `InitialCellsAt`, relates every source initial variable to its actual native cell.
- `Vegas/Game/SourceSwapPairs.lean:154`, `PublicCellsAgree`, compares every public cell present at the two native points.
- `Vegas/Game/OnePacketSplicePoint.lean:296`, `initialCellsAt_splicePoint`, already reconstructs a spliced native point's source initial state.
- `Vegas/Game/OnePacketSplicePoint.lean:308`, `drawn_splicePoint`, still instantiates the conditional splice support theorem with the constant Unit signal, requiring unconditional private-input independence.
- `Vegas/Game/OnePacketSpliceForced.lean:235` derives public agreement from the actual information-view equality; its call to `drawn_splicePoint` at line 246 was the missing conditional-prior adapter.

The checked probe proves:

1. initial_public_cells_eq (line 15): `InitialCellsAt mine p`, `InitialCellsAt others w`, and `PublicCellsAgree setup p w` give equality of each public source initial variable.
2. initial_public_inputs_eq (line 22): those premises give equality of **all graph public input coordinates**. This uses the current initial context coverage and `encodeInputs_get` APIs, including the actual dependent casts.
3. drawn_splicePoint_given_public (line 44): for an arbitrary signal `signal`, `PrivateInputsIndependentGiven signal`, and the same graph-public-input observability premise already used by the new conditional base law, the actual spliced native point remains in the supported prior draws. Signal equality is **derived** from the two actual `InitialCellsAt` witnesses and `PublicCellsAgree`; it is not supplied as a desired conclusion.
4. forcedAgent_of_splice_given_public (line 67): the entire current forced-agent proof works under that conditional independence. Its same-view fact supplies public agreement, which feeds the new producer.

The observability premise is exactly: agreement on every public graph input implies equality of the signal. No full private-input equality or extra public leakage is assumed. All existing well-formedness, covered binding fields, decoded/intended history, same information view, static/ready-own, changed-success, arbitrary prefix and non-focal responder guards remain. This is source-input conditioning connected to actual native cells, not merely a finite probability lemma.

**Actual route remaining:** `Vegas.forcedAgent_of_responder_preserving_repair` (line 31, actual forced-agent call line 155), then `OnePacketRepairCertificateCounterpart`, `OnePacketBindingRepairAssembly`, and `Vegas.RecoveryOnePacket.nativeBaseInputs` (line 36), followed by the existing recovery comparison/capstone chain. The concrete forced-agent producer is checked; a complete conditional recovery sequential-equilibrium theorem is **not** checked or claimed.

Propagation audit: current `PrivateInputsIndependent` occurs 32 times in 25 Vegas.Game files, including documentation and an unused standalone unconditional closure result. Direct Unit specializations are the splice-point producer, `Vegas.keyedRecord_near` (line 281), and `Vegas.ownerSwap_priorClosed` (line 111). The latter deliberately proves a stronger closure without a same-public-key guard; the existing conditional base-law path uses `ownerSwap_priorClosed_given_public`, so its old statement need not be weakened. The LateRecords call can already target the generalized owner-swap base law but needs its signal/hypotheses threaded through its consumers. Most remaining changes are constructor/signature propagation plus verification, but there are enough of them that the complete extension must not be inferred from one successful probe.

A second current API guard is now accounted for: `Vegas.ownerSwap_baseLawAgrees` (lines 54-64) and `Vegas.ownerSwap_baseLawAgrees_late` require private splicing to preserve the signal in addition to public observability. `PublicSignalPreserved.lean` strictly checked with the central Lake options, actual exit 0 with no warnings, proves that actual source hidden-cell splicing preserves every public graph input. The existing public-input observability premise therefore implies signal preservation. This factual adapter needs no support, finiteness or probability premise. When ported, the public-aware base-law API can derive preservation internally instead of asking for another independent guard. The lower prior-scaling theorem can retain its more general explicit preservation premise. The complete conditional recovery sequential-equilibrium route is still unported and unchecked.

**Proposed API ownership:** keep graph input/cell adapters and conditional splice support in the existing one-packet source-splice owners; the conditional forced-agent theorem belongs beside its actual unconditional consumer. No new abstract certificate record is needed. A Unit specialization recovers the old mathematical result; zero compatibility requirements allow choosing the clean final API during implementation.

**Cost:** not a compression proposal. Three factual helpers add roughly 50 lines, while the ~80-line forced-agent proof should be generalized in place rather than duplicated. Downstream signature propagation is unmeasured. High confidence in the checked missing bridge; medium confidence in total propagation effort.

### 2. Timing error can be a product-retention error under the same hypotheses

**Value:** genuine quantitative strengthening, separate from the still-open event-specific payoff-oscillation refinement. Current timing coupling sums deferral probabilities; the actual existing mixture construction retains a multiplicative amount of the first-turn law.

**Status:** `TimingSettlement.lean` strictly checked with the central Lake options, actual exit 0 under central options. This self-contained probe proves the full actual one-event minorization, all-event product induction, total-variation corollary, and complete actual audited typed-outcome/payoff settlement consumer. `TimingRetention.lean` and `TimingRetentionProduct.lean` retain smaller diagnostic subsets. No conclusion is inferred from total variation alone.

Current actual proof:

- `Vegas/Game/ServiceTimingCoupling.lean:184`, `overriddenTurnProfile_fix_roundsFrom_bind_within`, handles arbitrary initial native-state law, scheduler, horizon, bound, source profile, arbitrary policy overrides and arbitrary common execution readout.
- Its non-overridden-owner case rewrites the **full run from initialization** as the timing-slot PMF mixture using `ReactiveApplication.runRounds_policyMixture`. The initial empty recall makes the posterior equal to the original timing distribution. It then invokes `PMF.WithinTV.of_bind_point` at line 271.
- `GameTheoryExtensions/Math/Probability/TotalVariation.lean:193`, `WithinTV.of_bind_point`, already proves a retained-branch atom bound internally before converting to TV. The missing interface is this stronger intermediate atom bound.

The checked actual one-event producer proves, for every readout outcome `x`,

`(1 - timing.deferral event) * P(fix event at 0, x) <= P(timing, x)`.

Unowned events and overridden owners give exactly equal laws. Otherwise the factor is the actual slot-0 mixture mass, not a postulated event probability. The common-start lift instantiates the existing `GameTheory.Math.Probability.bind_supported_domination` (line 46) with initial factor 1. The tiny mixture atom helper is extracted from the current `WithinTV.of_bind_point` proof. No new expectation, coupling or probability framework is needed and GameTheory need not change.

The checked all-event induction follows `Vegas.overriddenTurnProfile_roundsFrom_bind_within` (line 286): use `TurnTiming.fix_deferral_of_ne` (line 90) on the remaining distinct events; multiply the one-event lower bound by the nonnegative remaining retained mass; use `TurnTiming.fixFirst_all` (line 65). The resulting all-event lower bound is

`product(event, 1 - deferral event) * P(first-turn law, x) <= P(timed law, x)`.

Existing `PMF.WithinTV.of_domination` (TotalVariation line 30) then yields

`delta = 1 - product(event, 1 - deferral event)`

instead of `sum(event, deferral event)`. Both formulas refer to actual current timing objects. For two events with deferral 0.2 each, this gives 0.36 instead of 0.4; it also automatically stays at most 1. **There is no statistical-independence assumption:** the product comes from composing lower bounds between full run laws. Events and their behavioral decisions can remain dependent.

**Complete current consumers inspected:**

- `Vegas/Game/SourceServiceTurnSettlement.lean:154`, `sourceServiceTurnPolicy_execution_settlement_lawError`, ends with the honest timing coupling at line 183. The common readout is the actual audited typed-outcome/payoff settlement law; all authentic-audit/deposit, timely-contract and first-turn source-law guards remain. The complete consumer clone in `TimingSettlement.lean` is strictly checked with the product error; it directly specializes the checked overridden-profile theorem to no overrides.
- `Vegas/Game/AsyncServiceNash.lean:463`, `isεBestResponse_clientProfile_of_firstTurn_bounds`, uses `deviatedTurnProfile_roundsFrom_bind_within` at line 605, then converts it to a player payoff gap at line 612. The deviation is the arbitrary native admissible policy already decoded/restricted by the proof. The same product delta replaces the sum there, and the honest value bound must be updated consistently. The existing `epsilon + 2 * delta * range who` structure then uses the improved delta. Reflection at line 313 likewise compares two honest client-profile values.

**Adapter work not checked:** named honest and one-player override wrappers (current ServiceTimingCoupling lines 332 and 352), AsyncServiceNash's value/BR results and public capstones. The complete SourceServiceTurnSettlement joint-law consumer is already checked in the scratch clone. Recover the current sum-bound theorem using the elementary product/union inequality if that statement remains useful; do not preserve aliases for compatibility. Event-specific payoff oscillation still requires an event-sensitive value proof and is not solved by this finding.

A further unproved refinement is available from the same factual case split: events whose owners are overridden have exactly unchanged laws. In the forward native best-response transfer, the deviator is already overridden everywhere, so its own event factors can be replaced by 1. The forward error would use honest delta_all plus deviation delta_excluding_focal_owned_events, rather than twice delta_all. Reflection compares two honest client profiles and does not get that reduction. This extra port is not staged or claimed checked.

**Cost:** a strengthening, not a shrink claim. Refactor the one-event proof to expose domination and derive its old TV corollary, then replace the current sum induction by the product induction. Tiny common-prior and atom helpers can live in existing local probability owners if useful elsewhere. Initial scratch duplicates the current producer solely for verification. Production net cost expected +30-70 lines before consumer signature changes, medium confidence; no family line-saving claim.

### 3. Count-support exclusion can require payoff bounds only on actual terminal histories

**Value:** a useful semantic strengthening of existing support exclusion. Current `Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported` (line 254) takes global interval bounds at lines 263-264 for every native state, while the actual continuation and committed/safe laws put mass only on protocol-terminal histories.

**Status:** `TerminalAuditBounds.lean` strictly checked with the central Lake options, actual exit 0. It proves a terminal base-payoff bound for the actual `TerminalAudit.utility`, then instantiates the existing actual continuation-integrability API. The full RecoveryCount consumer port is not staged or checked.

Reusable current APIs:

- `GameTheory/GameTheory/Protocol/BehavioralTerminal.lean:57`, `InformationModel.runBehavioralTerminalFrom_support_terminal`;
- line 160, `payoffIntegrable_runBehavioralTerminalFrom_of_bounded_terminal`;
- line 218, `BehavioralAssessment.continuationContext_support_terminal`;
- line 238, `continuationContext_integrable_of_bounded_terminal`.
- `GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean`, `charge_mem_Icc`, gives each actual charge in [0,1].

The checked first adapter proves `|base final who| <= C` on protocol terminals implies `|TerminalAudit.utility ... final who| <= C + |deposit who|` on those same terminals. The second adapter uses the actual assessment, site, well-founded-history certificate and entire arbitrary alternative behavioral policy with the core continuation-integrability theorem. It adds no finite-history or independence assumption. It retains the Fintype Player assumption actually required by the core context integration API.

**Concrete consumer change:** replace the current global baseBound and arbitrary-law integrability helpers around RecoveryCountIncentives lines 312-341 by terminal support bounds for the actual bad committed, safe, and aggregate continuation laws. Derive interval/absolute bounds on those supports and continue the existing strict-margin argument. Keep every information history, all admitted opponent policies, coverage, safe comparator and strict gain/penalty margin. The runtime review's separate information-local cleanliness result is complementary and is not duplicated here.

**Critical scope:** actual protocol terminality includes horizon exhaustion and unfinished graph/source outcomes. A bound solely on completed source outcomes is insufficient. The bound must cover the runtime's default output and audit charge on every exhausted terminal state as well. This proposal changes a mathematical hypothesis from all native states to actual terminals; it must not silently substitute source completion for runtime terminality.

**Ownership/cost:** local terminal-audit owner for the small utility adapter; existing RecoveryCountIncentives for actual consumer reasoning. Expected +0-25 net lines in that consumer plus ~25 reusable adapter lines, low-medium estimation confidence. Not a compression claim. The desired full consumer strengthening is still work, not a completed theorem.

### 4. Recorded-entry preservation is an existing exact recall-prefix instance

**Value:** small reliable proof shrink with no statement change. Current complete consumer `Vegas/Game/OnePacketFirstActivation.lean:66`, `recordsEntry_transition`, manually splits transition cases to keep an exact recorded entry. `Interaction/ReactiveHistory.lean:58`, `transition_recall_prefix`, already supplies the after control and each player's exact appended recall.

**Status:** `RecordedEntryPrefix.lean` strictly checked with the central Lake options, actual exit 0. It contains the unchanged actual consumer header and the short proof, with the required header wrapping.

The new proof splits `before = none`/`some`, obtains the actual after control and prefix extension from `transition_recall_prefix`, and turns `earlier ++ entry :: later` into `earlier ++ entry :: (later ++ tail)` using list associativity. It preserves the exact ordered split, not merely entry membership. Arbitrary scheduler, initial law, joint response, horizon and transition-support premises remain.

Actual downstream callers include `OnePacketEventSuccess.lean:145`, `OnePacketOpenableCommitment.lean:113`, `OnePacketUnintendedCommitment.lean:219`, and `RecoveryForeignFailureBound.lean:149`; they need no adapters or edits.

**Whole-family cost:** one complete producer declaration 40 physical lines becomes 20 after style wrapping; existing prefix API costs zero new production lines, all callers unchanged: **net 20 lines**, high confidence. No new wrapper/alias or general machinery is needed.

### 5. Four static commitment-interval inversions can share the existing descriptor owner

**Value:** modest engineering compression. This is the remaining interval-to-suffix-index fact, distinct from the previously implemented phase-boundary extraction.

Four full actual consumers repeat a 16-line `have bindings` block:

- `Vegas.HonestLaw.commits_step` (line 510), block 575-590;
- `Vegas.asyncDeviation_deviationLaw` (line 567), block 833-848;
- `Vegas.asyncDeviation_withholdLaw` (line 573), block 736-751;
- `Vegas.ConcurrentPhaseEnds.boundary` (line 166), block 229-244.

Each block proves: every event in `[offset, offset + count)` has an actual typed binding `nodeView`. It computes index `event.val - offset`, proves bounds with `omega`, identifies `embedding.event index = event` via the existing `rankEq`, and then invokes the same `CompiledSuffix.commitPrefix_bind`.

**Existing owner:** `Vegas/Game/ServiceCommitTail.lean:290-345`, `CompiledSuffix.commitPrefix_bind`, already owns the structural induction and actual typed bind code. `Vegas/Compile/EventGraphSuffix.lean:25`, `CompiledSuffix`, supplies countEq, rankEq, and actual nodeEq. Add an interval-form public theorem beside that owner, using the current indexed induction internally. No second prefix hierarchy or execution/source-law hypothesis is justified.

All four full surrounding consumers were read; this helper only replaces their static interval descriptor setup. Sealed/block boundary, relaxed execution order, deadlines, scheduler, source profile and all behavioral law premises remain untouched. There is no desired-law certificate in the proposed helper.

**Whole-family physical-line estimate:** 4 x 16 = 64 current block lines; ~28-35 new helper lines including its real dependent header and ~8-12 replacement call lines. Conservative expected **20-30 net lines**, medium confidence. Not checked or implemented; first port all four consumers to establish actual cost before keeping it.

## Coverage and rejected leads

The fresh surface scan covers 824 Vegas.Game Lean files, about 270845 physical lines, plus Paper.lean. `games-surface.txt` was generated through lean-defs.py. Lexical scans found 4880 theorem/lemma/def heads and 4431 cross-file exact 10-nonblank-line windows; these are search aids, not checked declaration counts or proof-size measurements. Deep reads focused on current conditional-prior/source-splice and counterpart pipelines, recovery comparisons and gain bounds, count incentives/terminal/audit guards, exact first-entry provenance, async service law families, typed compiled suffixes, timing coupling, audited settlement and actual native best-response consumers. This is broad inventory plus selected complete deep reads, not a claim to have manually read every line of the entire Game family.

Important rejected/limited leads:

- The highest 8-file Recovery windows (CommitBeliefValue, CommitmentComparisons, GainBounds, DisclosureComparison, KeyedCommitmentComparisons, NonLateNativeComparisons, SilenceComparison, UnintendedComparison) largely repeat **return-type let scaffolding**. The prior parser mistook the first return-type `let ... :=` for the proof assignment. Their actual proof tails are small/generic already. They do not support a whole-family proof-saving claim; the shared Python scanner is now corrected.
- Three first-activation consumers repeat a small setup and tuple unpack. After the genuine helper header and needed factual hypotheses, savings appear only ~5-20 lines. No proposal is ranked without a complete whole-family pilot.
- Four scale-limit consumers have similar vanishing arguments, but some already instantiate the existing scale_vanishing methods. A new wrapper would need the long actual native-input context and can cost as much as their ~10-line proofs. No larger compression claim is justified.
- `Vegas.exists_outcome_of_read` is a 14-line private choose/factorization helper with two uses. Mathlib `Function.FactorsThrough`/the extension evaluation lemma fit mathematically, but supported-subtype and fallback plumbing likely erase the savings. Do not introduce an unused factorization API.
- Native one-packet finite history already follows from the finite native menu via `Interaction.ReactiveApplication.ResponseMenu.historyFintype`; `RecoverySequentialCompilation` already installs it. This does not remove unrestricted source-action or global consistency obligations. No global finiteness removal is proposed from bounded horizon alone.
- An EventCode at binding-kind output has only the bind constructor, suggesting a potential typed nodeView_bind_of_binding simplification. The current codeEq argument may be redundant, but a broad NodeView/datatype change has hundreds of consumers and no measured whole-family gain. Not ranked.
- No new counterexample or theorem-scope bug was established. The checked adapters and remaining strengthening proposals preserve actual payoff/integrability, positive-normalizer, full-information-fiber, deviation/opponent and runtime/source guards; unproved downstream propagation is explicitly separated from checked producers.

## Suggested implementation order

1. Apply exact recorded-entry prefix reuse as a small verified checkpoint.
2. Implement the static commitment interval owner only if all four actual ports confirm the modest net saving.
3. Land the conditional public-source-splice producer and generalize its actual forced-agent consumer in place; then thread signal/hypotheses through the explicitly audited remaining recovery route. Do not close any sequential-equilibrium checklist box merely from this producer.
4. Expose the checked timing minorization/product result and port the already checked audited-settlement consumer into production, then propagate both honest/deviated Nash errors and public capstones together. Retain actual admissibility and payoff-range guards; those Nash ports remain unproved.
5. Strengthen count support exclusion to terminal-supported payoff bounds with a full actual bad/safe/context proof; keep it only if the source/runtime terminal boundary stays explicit and the resulting API is clearer.
