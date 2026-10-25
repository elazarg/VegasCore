# Vegas.Game proof review and mining

Baseline: `7272a57e`. Read-only audit; no production file, theorem statement,
option, runtime semantics, SE target or checklist was changed. This report
deliberately looks beyond the recently completed payment adapters.

## Coverage and method

All **819 Vegas.Game modules, 271,630 physical lines**, were included in the
module/import, declaration-surface and duplicate-window inventories. Root's
lexical inventory counts **3,999 proof-bearing bodies / 159,792 body lines**;
these are useful engineering measurements, not Lean AST measurements. My
independent declaration scanner found 5,045 top-level declaration-like heads,
including definitions, structures and instances. The different counts have
different denominators.

Artifacts:

- `ephemeral/proof-review/modules.csv`, `ephemeral/proof-review/declarations.csv`, `ephemeral/proof-review/duplicates.json`, `ephemeral/proof-review/inventory.json`: root's
  tracked-source inventory and exact eight-line proof-window matches.
- `games-surface.txt`: `lean-defs.py Vegas/Game Paper.lean`, the entire owning
  declaration surface; `source-correspondence-surface.txt`,
  `native-information-surface.txt`, `likelihood-surface.txt`: focused surfaces.
- `games-file-lines.csv`, `games-declarations.json`,
  `games-duplicate-windows.txt`: independent line/head inventory and exact
  twelve-line windows. Windows can include section scaffolding and are leads,
  not proof that an abstraction saves lines.

The following classification partitions the 819 modules by filename family;
it is mechanical, not a claim that all bodies were deeply read. QualifiedBinding
is its directory; the remaining labels are the first capitalized filename word.

| Family | Modules | Physical lines | Semantic review performed |
| --- | ---: | ---: | --- |
| OnePacket | 226 | 60,049 | Deep review of completion provenance, residual decoding/masses, initial invariants, owner prior/swap, certificate and late decomposition seams; surface inventory of all others |
| QualifiedBinding | 12 | 54,500 | All twelve declaration surfaces; selected long proofs in Likelihood, ReplayCoverage, SourceCorrespondence, SourceAlignment, BindingReadback, ForeignPosterior, OrdinaryContinuation and StoppedPayoff |
| Phase | 135 | 50,247 | Deep review of current/publication/clean binding gains, native source information, domination, future flags, common perturbations and consistent sequence; all surfaces inventoried |
| Recovery | 140 | 27,893 | Capstone/limit/local-comparison chain, keyed comparisons, prior transport, checkpoints, initialized laws and foreign failure bound reviewed; other surfaces inventoried |
| Proposal | 69 | 15,434 | Public class constancy/factorization, closed fibers, equilibrium construction and pooled completion seams reviewed |
| Service | 28 | 15,312 | Honest execution, block/reveal congruence, roster evidence and asynchronous service interfaces reviewed |
| Source | 59 | 13,404 | Residual decoding/head law, decoded invariants, canonical decision and decided completion, source protocol Nash, timed-local comparison reviewed |
| Reserved | 32 | 12,283 | Publication comparison, focal/original/stopped words, checkpoint reset and reserved implementation assumptions reviewed |
| Async | 12 | 7,145 | Declaration surfaces plus deviation/withhold laws, foreign congruence, Nash and deviation error composition reviewed |
| Commit | 35 | 4,670 | Recovery payoffs/restriction/reference and omission/word density interfaces inventoried; selected constant-payoff consumers checked |
| Compiled | 31 | 3,737 | Commitment/reveal phase and prefix readback declaration surfaces inventoried; inspected via their long semantic consumers |
| Intended | 10 | 2,011 | Intended preservation, exclusion, Nash/opening and initialization scopes reviewed |
| Concurrent | 3 | 1,282 | Original preservation contract and capstone fully reviewed at public boundary, selected local proof sections reviewed |
| Reveal | 9 | 1,155 | Base utility/readout/audit interfaces reviewed |
| Program | 4 | 630 | Recent payment work excluded from the main recommendations |
| Other small families | 14 | 1,878 | All surfaces inventoried; EventCompilation/EventScheduling and exclusion extension examined |

`Paper.lean`'s 23 theorem bodies and public headers were inventoried. I inspected
the public SE, public scheduling, source/ideal Nash, arbitrary-timely runtime
Nash and late-leak obstruction scopes. I found **no new proof-scope mismatch**.
This is not a line-by-line correctness audit of 271,630 lines. The coverage
ledger makes that limit explicit rather than presenting inventory as deep review.

Reusable owning APIs checked include `ReactiveMenuInvariant`,
`ReactiveServiceInvariant`, `ReactiveLumping`, `ReactiveSchedulerImplementation`,
`ReactiveSchedulerSeedTrace`, `ReactiveSchedulerTerminalMixture`,
`LocalSimulationLimit`, `SourceGainTransport`, `SuccessRanking`,
`AffineKeyedPools`, `RestrictedDisintegration`, `StoppedKernelComparison`,
`ExpectationBind`, `WithinTV` and `SupportedChoices`.

## How to read the estimates

“Net saving” means an estimated decrease in **all production lines**, including
the new reusable proof, all concrete adapter obligations and caller changes.
It is not the size of the old proof alone. Positive numbers below mean fewer
lines. These estimates are engineering hypotheses until a checked patch exists;
they must not be summed because several opportunities overlap. “Feature growth”
is explicitly not a compression claim. A large old body does not make its
semantics or provenance obligations redundant.

## Ranked findings

### 1. Prove owned-completion provenance once, with all the facts consumers need

**High priority; high duplication confidence; medium extraction risk.**

The same environment-command analysis is independently performed by:

- `Vegas.actor_completion_cause` (`:213`, 152 body lines);
- `Vegas.completion_content` (`:162`, 177);
- `Vegas.completion_cases` (`:30`, 191);
- `Vegas.completion_pending_or_due` (`:20`, 91);
- `Vegas.environment_completion_cause` (`:188`, 132).

That is **743 measured proof-body lines**, with exact repeated handling of
activate/wait, absent or rejected inclusion, automatic sample completion,
expiry timing, and uniqueness of the completed event/action. The differences
are useful projections: pending origin, accepted ledger receipt, actor,
decoded call content, candidate ownership, accepted-table update and expiry
failure. They should be retained in one rich outcome, not discarded to obtain
a common weak statement.

Proposed API: a factual completion classification for an actual environment
step reaching a specified graph step. Its accepted-packet branch records the
original pending message, receipt, event and sender, decoded content and table
facts; its expiry branch records due time, unchanged table and exact failing
action. The ownerless sample branch must remain available for the currently
unconditional `environment_completion_cause` use. Derive the existing consumer
facts as projections and update callers, rather than retaining compatibility
wrappers.

The present import order matters: `CompletionContent` imports `ActorRecord`
but introduces `callContent`, so the shared payload reader/classifier needs a
lower file or a split. This is a real adapter cost.

**Estimated net saving: 250–450 production lines**, after a roughly 200–300
line enriched classifier, lower-reader movement and small concrete projections.
This is the strongest sizable candidate; a probe should first check that
receipt and table facts coexist in the accepted branch.

### 2. Add the missing initialized decoded-invariant induction

**High priority; high confidence; low risk.**

`decodedHolds_transition` in `SourceServiceDecodedDebt.lean:111` already proves
the difficult preservation step for every `StepClosed` source predicate. Yet
the following proofs repeat the same native trace induction and setup-draw
decoding:

- `OnePacketHonestForced.decodedState_intended_or_owes:49` (27 body lines);
- `OnePacketDisclosureResolves.decodedState_intendedFor_or_owes:216` (26);
- `OnePacketPublishedBindings.decodedState_publishesOrFails:223` (26).

Proposed theorem: if a predicate is `StepClosed` and holds at the entry of every
supported initial source configuration, every initialized menu history with
an actual control satisfies `DecodedState` for it. Use `SourceResidual.initial`
once for initialization and `decodedHolds_transition` once for induction.
The predicate's initialization proof remains a caller obligation: well-formed
guards, intended-for-owner and publishes-or-fails are not interchangeable.

This is a more precise first step than a new generic invariant hierarchy.
*ReactiveMenuInvariant.ServiceInvariant.history* already handles the analogous
execution-level lifting; do not duplicate that framework.

**Estimated net saving: 35–55 lines for these three callers**, potentially more
only after finding additional complete consumers. Proposed probe below.

### 3. Expose one residual-head operational correspondence, then derive masses

**Medium-high priority; medium confidence; medium dependent-type risk.**

`SourceResidual.step` (`SourceServiceReachedDecoding.lean:128`, 241 body lines),
`SourceResidual.chanceMass` (`OnePacketChanceMass.lean:33`, 162),
`SourceResidual.actorStepMass` (`OnePacketActorCompletion.lean:35`, 59), and
`SourceResidual.head_law` (`SourceServiceFirstTurnMixture.lean:99`) repeatedly
recover the head event from rank, identify its layout/code, build tail refs and
prove the same decode square. The behavioral head law does **not** itself
replace fixed-action/chance atom correspondence; those are different claims.

Proposed interface: a dependent view of the residual's current head, carrying
rank/layout/code/action decoder, supported successor decoding and injectivity
of that decoder on the fixed graph-step support. Derive fixed-action law/atom
correspondence, then behavioral bind correspondence, with the source policy
obligations separate. Also expose the source fact that an active owned
instruction's fixed-joint step is pure; `actorStepMass` currently opens the
entire source syntax to prove this.

**Estimated net saving: 70–150 lines** across these actual consumers, including
the dependent view and probability adapters. This estimate is deliberately
smaller than the 462 measured lines in the first three bodies.

### 4. Factor phase-boundary advancement out of honest/deviation/withhold induction

**High payoff, medium confidence, medium-high refactoring risk.**

`ServiceHonestLaw.HonestLaw.sample_step:401` and `.commits_step:532` contain
boundary advancement and PhasePoint support arguments copied into
`AsyncDeviationLaw.asyncDeviation_deviationLaw:600` and
`AsyncWithholdLaw.asyncDeviation_withholdLaw:572`. Exact repeated windows
include `completionRun_boundary_step`, `blockRun_boundary`, prefix embedding
and tail refs, and the decoded source-tail bind.

First extract small factual successors: a sample PhasePoint preserves horizon
and yields the next `CompletionBoundary`; a commit block gives the corresponding
end-boundary and typed tail readout. Then use those facts from the three
induction theorems. Do **not** start with a large abstract simulation whose
premise is the desired continuation law: the focal deviation law, withholding
branch and honest source law must still be proved.

**Estimated net saving: 90–180 lines**, including new lemmas/adapters. A wholesale
single simulation proof may save more, but is currently unestimated; it risks
moving almost all of the old proof into relation fields.

### 5. Make mapped reactive-round congruence an Interaction API

**Medium-high priority; medium confidence.**

`foreignRound_readout_congr` (`AsyncDeviationForeign.lean:75`, 207 body lines),
`blockRound_readout_congr` (`ServiceBlockCongruence.lean:614`, 150), and
`revealRound_readout_congr` (`ServiceRevealCongruence.lean:450`, 179) each unroll
round, dispatch, sampled activation, invocation, inclusion and application
commands. Exact common code begins with equality of environment recall/view,
then *PMF.map_bind*, then the command case split.

`Interaction.ReactiveApplication.ResponseMenu.run_map_withinTV` lifts one-step mapped comparisons
to whole runs. The missing reusable layer is the **round constructor theorem**:
equal scheduler inputs plus mapped activation/invocation and environment-step
laws imply equal mapped round laws. Model adapters would still prove traffic,
mark, submitted-event and receipt behavior. This is an observational congruence
theorem, not a new runtime or the assertion that every hidden difference is
unobservable.

**Estimated net saving: 90–180 lines**, after a 50–80 line round theorem and
retaining all model-specific response/inclusion obligations. Overlaps with
finding 4 if a larger simulation extraction is chosen.

### 6. Lift the hidden-seed path-likelihood identity out of reserved-tape replay

**High mathematical reuse; medium confidence; modest immediate shrinkage.**

`QualifiedBinding/Likelihood.lean` privately proves
`sourceReplay_scheduler_density:66`, `sourceReplay_tape_step_density:111`,
`sourceReplay_transition_tape_factor:184`, and then
`sourceReplay_native_tape_factor:209`. The first three have 94 measured proof
lines. Their mathematical content is generic: multiplying a behavioral path
atom by the posterior mass of one original hidden seed equals its prior mass
times the fixed-seed path atom. The current proof specializes it to
`ReservedEpoch.Tape`, even though `SchedulerImplementation.command_disintegrate`,
*posterior_snoc* and `scheduler_eq` already expose the Bayesian mechanism.

Proposed API in Interaction: an atomwise trace likelihood identity for arbitrary
`app`, seed prior and immutable scheduler family. Keep the actual recorded path
and its support; include zero command atoms using the existing zero-safe
fiber-posterior density identity. Behavioral own-play products should be a
separate corollary using `exists_continuation_ownPlay_factor`.

**Estimated net saving: 0–35 lines immediately** (generic proof replaces one
specialized proof); the main benefit is removing the reserved-tape assumption
from reusable probability reasoning. Further savings require actual second
consumers, not promised future ones. Do not claim this makes arbitrary-builder
concurrent SE immediate: the reserved service's timing and factual replay
obligations are untouched.

### 7. Extract conditioning-cost bounds with explicit excluded mass

**High confidence; medium priority.**

`PhaseProposalCleanBindingGain.conditioned_gain_le:2050` has 62 body lines of
pure probability calculation. It bounds a payoff after filtering to foreign
good histories by the original expectation plus payoff oscillation times bad
posterior mass. Much of the proof converts filter mass to a finite sum of
generated-preparation histories.

Proposed generic theorem: for a nonzero event and payoff in `[lo,hi]` on the
original support, conditioned expectation differs by at most
`(hi-lo) * P(eventᶜ)`. Use `filter_mass_mul`,
`WithinTV.of_domination` and `WithinTV.expect_sub_le`. State it for arbitrary
PMFs with supportwise bounds; no finite history type is needed. The source
adapter then proves only that the bad event is the named existential generated
preparation event, and presents its finite sum when required by the capstone.

**Estimated net saving: 20–40 lines for this consumer**, after the generic
proof and exact event-mass adapter. The same bound may serve other conditional
comparison modules, but those savings are not counted.

### 8. Publish retained/residual gain algebra, without global finite carriers

**High confidence as an extraction/generalization; not yet a shrink win.**

`PhaseProposalCleanBindingGain.retained_history_gain_le:2966` (23 body lines)
and `averaged_retained_gain_le:3002` (21) contain no Vegas object in their
statements. They separate a retained payoff from a residual continuation,
allow a bad-event penalty, and commute baseline and belief expectations.

Move the mathematics to a model-independent comparison module. Strengthen
the history-level lemma from `[Finite α]` to integrability of the mean and the
relevant residual functions under the baseline; the existing bound already
provides mean integrability. Strengthen the averaging lemma using explicit
Fubini/integrability, or first use the existing
`expect_comm_of_support_finite_left` to require finite baseline support only
and allow an infinite belief carrier. Keep conditional comparisons on their
actual supports.

**Estimated net saving: -15 to +5 lines initially**; clearer owning APIs and
strictly better probability generality are the return. No whole infinite-game
SE generalization follows: compactness and off-path action spaces elsewhere
still require their own finiteness hypotheses.

### 9. Remove the exact duplicated support-order expectation theorem

**Very high confidence; low impact.**

`PhaseProposalCurrentBindingGain.lean:22` and
`PhaseProposalPublicationGain.lean:17` contain the same private
`expect_le_expect_of_support_order` declaration and proof verbatim. It is a
generic cross-support order bound between two integrable expectations.

The scratch probe `SupportOrderProbe.lean` proves the slightly stronger
additive-slack version using existing expectation APIs, without finite carriers
or supports, and checks recovery of the exact old statement at zero slack.
The two private copies can be removed and actual calls updated to the general
lemma. Integrability must remain: these real expectations have a defined
nonintegrable fallback, so arbitrary order does not justify dropping it.

**Estimated net saving: 8–15 lines**, including the shared theorem and both
call adapters. This is a useful checked small probe, not evidence of a major
compression. Root checked both probe declarations successfully under the exact
central lakefile options (compiler session `83123`, actual exit 0).

### 10. Share domination operations rather than model-specific map/mix lemmas

**High confidence; small engineering win.**

`PhaseProposalBaseDomination.map_retains_mass:45` and
`PhaseProposalOrdinaryDomination.ordinary_map_lower:27` are the same mapped
atom-domination proof. The same files contain one-sided mix retention and
two-sided mix domination. The general layer already has
`prob_bind_ge_mul`, `bind_supported_domination` and mixture atom algebra.

Prefer a small general domination interface with map and common-mixture
operations, or direct instances of those existing theorems if that is shorter.
Keep the source constructor's normalization and absent-query branches in the
Vegas adapters: all-flags-removed and ordinary-only references are different
laws and must not be merged.

**Estimated net saving: 0–15 lines initially**. Avoid introducing a large new
record merely to replace two six-line lemmas. The useful strengthening is
composable supported kernel domination, which is already mostly present.

### 11. Give approximate local comparisons monotonicity and finite-case algebra

**Medium priority; medium-high confidence; modest gain.**

`RecoveryLocalComparisons.recovery_local_comparisons:43` constructs
`abs(nonlateError)+abs(keyedError)`, proves convergence, classifies owing/keyed/
nonlate sites, and repeats the same “direct bound or mixture-source bound”
error enlargement. The same pattern appears in `RecoveryKeyedComparisons:47`
and the final current/publication/clean classification in
`ConcurrentRawEquilibrium.concurrentRaw_local_gain_le:114`.

Use a small generic relation saying a target local gain is bounded directly
or by a mixture of source local gains plus an error. Supply *mono_error*,
case combination and pure-mixture conversion lemmas, then feed the existing
`LocalSimulationLimit`/`CopiedSiteLimit` result. An error combination theorem
must retain **one common assessment sequence/subsequence**; independent
subsequences from independently optimized cases are not valid substitutes.

**Estimated net saving: 20–50 lines** across the actual three assembly points,
including the relation and all instances. Bundling the gigantic hypothesis
lists alone is assumption repackaging, not a mathematical extraction or a
proved shortening.

### 12. Repair the dependent provenance interface before attacking giant bodies

**High maintainability priority; low quantified shrink confidence.**

The largest bodies are `BindingReadback.source_admitted_binding_row:65`
(1,906 body lines), `SourceAlignment.sourceReplayAlignment:420` (1,747),
`ReplayCoverage.sourceRawReplay_closed_key:6272` (1,299), and
`SourceCorrespondence.sourceReplay_step_selected_agreement:7109` (roughly 500).
These retain real distinctions between current, entry and retired snapshots,
physical drain origin, source row, attempt/generation and accepted handle.

They repeatedly construct and destruct long dependent existential packages.
For example, `sourceReplaySelectedImage` in `SourceCorrespondence.lean:102`
combines mapped history, current/saved configurations, prefixes, state/view,
depth, exclusion/generation and snapshot agreement. The later branch theorems
manually repackage the same fourteen coordinates. Introduce a precise structure
for this invariant with checked constructor/update lemmas for same attempt,
retry and actual close. Similarly expose the already-proved factual admitted
binding origin as a reusable record whose projections carry the **same**
handle and raw pre-restore image.

This is primarily proof engineering. It must not replace the closing-origin,
historical-query or likelihood theorems by fields asserting their conclusions.
Nor may current clean source images be identified with final snapshots merely
because both are clean. The accepted handler/readback facts are the substance.

**Estimated net saving: 0–100 lines, low confidence** until a single branch is
converted and all adapters measured. I do not support a “thousands of redundant
lines” claim from the size of these proofs alone. A first branch conversion is
a better experiment than a new all-encompassing correspondence abstraction.

### 13. Generalize owner-prior transport to public-fiber independence, cautiously

**Potential substantive game-theoretic extension; medium-high risk.**

`OnePacketOwnerPriorSite.ownerSwap_priorClosed:111`,
`Vegas.ownerSwap_priorScaled`, and
`OnePacketSplicePoint.drawn_splicePoint:308` consume
`PrivateInputsIndependent`. `Vegas/Source/PrivateInputsIndependent.lean:102`
defines unconditional independence of each player's hidden cells from every
other initial cell. The concrete proof ultimately needs supported splice
closure and a common prior ratio within the compared owner fibers.

A useful stronger theorem would allow a publicly observed initial signal and
require the cross-product/splice identity **only within that public signal's
fiber**. This permits private types correlated through a public signal. Start
by proving the owner-swap lemmas under those local conditions. To port the
full recovery result, prove that every compared late key and splice fixes the
same public initial signal, and audit every remaining use of unconditional
splice support. That factual key condition is not currently supplied merely
by naming a conditional prior.

This is standard conditional probability and symmetry, but a real new model
adapter, not deletion of an unused assumption. Arbitrarily correlated private
types are not covered by this proposal. The existing concurrent theorem's
different treatment of correlated initial data does not prove the recovery
adapter.

**Estimated size: feature growth of 80–200 lines plus caller changes**; no
compression claim. This is a plausible insight-producing extension after the
small refactors, and should be tested on an explicit common-signal prior.

The local implementation provides a source conditional cross-product predicate,
actual public-input readers for every history at a late-key site, restricted
owner-prior scaling, and same-key supported splice closure. Its shared set
intersects the supported hidden-input fiber with the observed public-signal
fiber. Hidden-input agreement alone does not fix that signal. The scaling law
requires splice preservation; the site laws require that public initial inputs
determine the signal. A full-support public-bit regression with conditionally independent private
noise satisfies these guards and disproves unconditional independence. The canonical two-site base-law proof
can consume these producers without copying the swap/disintegration argument;
its unconditional record-comparison caller uses a constant public signal.

The recovery equilibrium capstone continues to require its original
unconditional hypothesis. Its independent source-recovery obligation is actual
splice support between two decoded points. Relaxing that obligation requires
proving that every represented source draw at both points has the same public
signal, using their public-cell agreement. The late-key site theorem alone does
not establish this different source-recovery fact. No conditional-prior recovery
SE theorem is claimed.

### 14. Obtain event-sensitive Nash errors before changing runtime contracts

**Potential useful quantitative theorem; medium risk.**

`AsyncServiceNash` and `AsyncServiceDeviationBound` use
`2 * (∑ event, timing.deferral event) * range`. The proof first obtains a
global TV error and then multiplies by one global audited payoff range. This
forgets which event deferred and whether its continuation affects a given
player's utility.

Proposed stronger statement: with checked per-event continuation oscillation
bounds, obtain separate honest/deviation expectation errors weighted by those
event sensitivities, then add those two errors for Nash transport. A simple
first result allows player-specific ranges, with the same scheduler and
deviation quantifiers. A genuinely event-specific bound needs the existing
phase coupling to retain the first deferral/event tag before applying the
oscillation inequality; it does not follow from the final unlabelled TV bound.

This can show that timing uncertainty at payoff-irrelevant events is free, a
useful game-theoretic conclusion. It remains a Nash statement under the existing
asynchronous contract, not an arbitrary-builder concurrent SE proof.

**Estimated size: feature growth of 60–180 lines**, depending on how much of the
tagged phase coupling can be reused; any proof shortening is unestimated.

The implemented first result uses each player's complete audited payoff range
and retains every native/source deviation and both expectation guards. Existing
scalar Nash conclusions follow by choosing a constant range function. It does
not establish event-specific sensitivity. The event-slot coupling already
compares each adjacent hybrid timing with error bounded by that event's deferral;
the whole-run TV proof then sums those errors. A weighted payoff result must
retain those hybrids and prove uniform continuation oscillation bounds for each
one, including unfinished outcomes and audit charges. Honest and deviating
continuations need their own guards. No such bounds follow from a final
unlabelled TV estimate, so no unused tagged-coupling framework was added.

### 15. Turn strict enforcement margins into a local support-exclusion theorem

**Near-reachable conditional result; high confidence in the final argument.**

The count-audit extension uses a weak sufficient bound: coverage times deposit
covers the utility spread. The underlying collection statements quantify over
actual committed continuations, while
`BehavioralAssessment.not_supported_choice_of_uniform_gap` in
`GameTheory/GameTheory/Analysis/Protocol/SupportedChoices.lean:117` already rules out a
choice uniformly worse than a feasible continuation under sequential rationality.

Under a **strict** charge margin and a checked safe continuation with the
required lower payoff and zero future charge, combine those two APIs to show
that a forbidden current choice has zero probability at a clean information
site of any sequentially rational assessment. State the bounds over every
history in the information fiber, with integrability and runner factorization;
do not infer them from the fact that one selected equilibrium has clean paths.
An already-triggered deposit or an information fiber mixing previously
sanctioned histories can invalidate the naive strict argument.

This is a useful partial reflection/robustness theorem, not full reflection of
all native SE and not proof that all off-path histories are clean. Most of the
final game-theoretic argument already exists; actual safe-continuation and
collection adapters are what must be checked for each runtime.

**Estimated size: feature growth of 40–100 lines plus concrete safe-policy
adapters**, with no claimed net reduction. No new equilibrium mathematics is
required after the stated uniform hypotheses are established.

## Checks on tempting but invalid shortcuts

- The three count-audit extension modules still share a committed-response
  plumbing block (fuel subtraction, committed one-step state, then collection).
  The recent audit refactor already extracted the supported-bind expectation
  step. A further generic “commit a response then terminal continuation” lemma
  is plausible, but I did not count it as a new major finding: its remaining
  adapter hypotheses may consume most of the roughly 30 repeated lines.
- `GameTheory.Protocol.PublicScheduler.expanded_sequentialEquilibrium` already transports SE
  through a recoverable public scheduler expansion. Composing it with a current
  capstone gives a useful protocol-level corollary but does not discharge the
  physical recovery/phase adapter or admit an arbitrary timely builder.
- A positive shared coefficient in posterior transport is not disposable.
  At zero fiber mass, posterior support and Bayes interpretation differ even
  though unnormalized density identities remain valid. Existing
  `RestrictedDisintegration` should be instantiated before adding another
  posterior package. Extraction of a chosen anchor alone does not prove the
  factual historical callback/query equality.
- There are several elementary interval/absolute-value bounds
  (`OnePacketLateDecomposition.expect_mem_Icc:153`,
  `OnePacketCertificateAssembly.exclusionPayoffs_bounded:97`,
  `ConcurrentRawEquilibrium.concurrent_payoff_bound:55`). General expectation
  bounds can help, but the zero/exit/source branches and global sum over
  players are different. No large saving is justified by treating all of them
  as identical.
- Finite global histories are not generally a cosmetic assumption: common
  Bayesian completion, compactness and all off-path information sites use
  them. Local probability lemmas can often use finite support or explicit
  integrability instead; that is not a general infinite-game SE theorem.
- I found no justification for altering fixed SE checklist statements or
  replacing the reserved concurrent implementation by an arbitrary timely
  scheduler. Large repeated proofs do not remove that research gap.

## Targeted probes and order of work

1. **Authored, frozen:** `SupportOrderProbe.lean`. It checks an arbitrary-space
   additive-slack generalization and exact zero-slack recovery of the duplicated
   support-order lemma. Root checked it under the exact central lakefile options;
   actual exit 0, session `83123`. No production extraction is made by this audit.
2. **Proposed:** one *decodedState_history_of_stepClosed* scratch theorem and
   the three exact old initialized-predicate applications. This has a small,
   complete adapter boundary and a measurable 79-body-line baseline.
3. **Proposed:** enrich one completion classification with both accepted receipt
   and decoded content, then derive `actor_completion_cause` and
   `completion_content` from it without reopening the command split. This tests
   the largest credible saving before moving the whole family.

Recommended sequence: probes 1–2; the completion classifier; mapped round
congruence and phase-boundary facts; conditioning-cost and comparison algebra;
then a single dependent provenance branch. Pursue public-fiber priors,
event-sensitive Nash errors and strict enforcement as explicitly new results,
with examples and their exact extra hypotheses. Do not count mathematical API
growth as proof compression until all concrete consumers are measured.

## Probe result

**PASS:** root compiler session `83123`, actual exit 0, using a setup-JSON clone
of the exact central lakefile options. Both the arbitrary-space additive-slack
theorem and exact old zero-slack statement compile. This validates the small
mathematical extraction candidate; the numerical net saving remains an estimate
until actual production callers are changed and measured. No production
implementation or broader scope claim is made here.
