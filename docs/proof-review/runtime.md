# Runtime proof review

Audit baseline: `7272a57e`. Scope: every Lean module under `Interaction`,
`InteractionTests`, `Vegas/EventGraph`, and `Vegas/Pending`—616 modules,
86,301 source lines, and 41,337 lexical body lines in the root inventory.
No production files were edited and this auditor ran no compiler.

The complete declaration surfaces were extracted with:

```text
python -X utf8 lean-defs.py Interaction InteractionTests Vegas/EventGraph Vegas/Pending
python scripts/proof-inventory.py --output ephemeral/proof-review
```

The root inventory's `ephemeral/proof-review/modules.csv`, `ephemeral/proof-review/declarations.csv`, and `ephemeral/proof-review/duplicates.json`
corroborate the sizes and repeated proof windows. These generated scratch
inventories are lexical measurements, not proofs of equivalence or
removable-line counts.

Coverage means an exhaustive module/declaration inventory and family-level surface
screen, followed by targeted reading of signatures and proof bodies in the hard
families below. It does **not** mean every tactic in all 41,337 body lines was
manually reverified. The ledger at the end distinguishes those levels explicitly.

## Findings in priority order

Savings are rough **source-line** estimates: “gross” is existing material plausibly
replaced, “kernel” is new shared declarations and proofs, “adapters” includes all
model-specific obligations and caller repairs, and “net” subtracts both. They are
not benchmark results. Estimates overlap, particularly invariant, handler,
normalization, and projection work; do not add their upper bounds.

### 1. Give accepted-event ownership one owner

`Vegas.EventGraphRuntime.handle_event_actor` (`Vegas/Pending/AcceptedEventOwnership.lean:16`)
and `Vegas.EventGraphRuntime.handle_event_actor` (`Vegas/Pending/EventOpponentFrame.lean:24`)
independently declare the same fully qualified name and statement. Both modules
are imported by `Vegas/Pending.lean`. Their roughly 43-line proofs do the same
packet/readiness/timeliness/node-kind split.

Import `AcceptedEventOwnership` from `EventOpponentFrame` and delete the latter
local declaration. Its downstream `handle_opponent_completed_iff` already works
with exactly that statement. The scratch
`ReducedEventOpponentFrame.lean` preserves that
downstream theorem's type and proof verbatim; it deliberately does not import the
original `EventOpponentFrame`. Root compilation is the verification authority.

Estimate: gross 49, kernel 0, adapters 1 import, net about 48 lines.
Feasibility/confidence: very high. This is definite ownership duplication, not a
claim that the imported environment is unsound or that the full build fails.

### 2. Finish using the existing invariant hierarchy before inventing another

`Interaction/ReactiveInvariant.lean` already lifts application `Invariant` and
`StepRelation` certificates through response, inclusion, environment, transition,
and history. `ReactiveServiceInvariant` adds a fixed scheduler's supported-command
restriction; `ReactiveMenuInvariant` adds the legal menu-action restriction.
Nevertheless `ReactiveProvenance.transition_provenance/history_provenance` repeat
the entire control-state transition induction, as do several recall/provenance
wrappers. `Interaction.ReactiveApplication.serialsBeforeNextInvariant`,
`Interaction.ReactiveApplication.pendingOrPublishedInvariant`, and
`ReactiveMessageIdentity` repeat almost identical network-operation lifts.

First replace the direct provenance induction by an existing `ServiceInvariant`
instance. Add small constructors for conjunction, implication, and lifting a
`MessageNetwork` invariant through the three real network operations (submit,
learn, include). This is not a reason to merge all invariant definitions:
unrestricted responses, legal menu responses, and fixed-policy-supported
responses have different quantifiers.

Nearby theorem: a scheduler-independent execution invariant with obligations for
all commands induces every `ServiceInvariant scheduler`; a scheduler-relative
one induces a menu-relative one. These should be proved by instantiation, with
initial-law support handled separately, not by assuming history preservation.

Estimate across the first provenance/network callers: gross 250–400, kernel
50–90, adapters 60–100, net 100–220. High confidence; pilot provenance first.

### 3. Factor the four-way environment lift, without discarding execution data

The root duplicate inventory identifies the same `wait/activate/include/application`
support decomposition in `ReactiveInvariant`, `ReactiveRecall`, `ReactiveReceipts`,
`ReactiveSubmissionSerial`, `ReactiveEvidence`, and `ReactivePacketEvidence`;
the same shape recurs in `Vegas.EventGraphRuntime.MessageBounds.candidateValues_environment`,
`Vegas.EventGraphRuntime.signedBindings_environment`, and both phase stamp histories.

A useful kernel is an **eliminator for the existing environment-step law**: return
the exact source command case, sampled activation/leak set or accepted handle
result, and the unchanged network/recall/receipt coordinates. An invariant or
relational certificate then consumes those primitive cases. This is smaller and
safer than an all-purpose simulation structure whose main premise would be the
desired transition law.

The same componentwise machinery can build *ExclusionProjection.execution*,
`PhaseNativeProjection.execution`, and *PhaseBindingRepairProjection.execution*
and derive observation/recall/map laws. However the maps of application state,
payload, commands, and observations must commute with real operations, and leak
laws need map compatibility. A packet map alone is insufficient.
The existing recovery/native transition transport is conditional on its clear
record domain; those local map laws do not give a global native simulation
through phase namespace changes or rollback. Keep that domain obligation visible.

Reuse already present: `SubmissionNormalization` proves local packet/submission
effects, and `Interaction.ReactiveApplication.SubmissionNormalization.runBehavioral_projection` uses
`ExecutionProtocol.runRandomizedFor_map_of_oneStep` to obtain the complete
continuation law. A projection cleanup should supply the missing local adapters
to that runner, rather than introduce another execution evaluator. The alias
consistency chain also discharges its advertised Bayes-projection premise in
`Interaction.ReactiveApplication.SubmissionNormalization.splitBayes_projection`; the final existence result does not
leave that desired posterior law as an unexplained assumption.

Estimated first-stage saving: gross 300–500, kernel 90–150, adapters 100–180,
net 50–220; medium/high confidence. A general projection framework is a second
stage with uncertain net saving. Rollback must retain pending traffic, global
serials, player recall, environment recall, and receipts; never rebuild them from
the restored semantic checkpoint.

### 4. Automatic draining already has the trace needed for almost every frame

*ExclusionCompletion.drainFuel* and *PhaseCompletion.drainFuel* have nearly
identical recurrences and proofs of trace, quiescence, unchanged exclusion,
tables, reachability, and invariants. The phased version only restricts eligible
events to `phase.events`. Many later files induct on *drainFuel* again:
`PhaseStoredCheckpoint`, `PhaseHistoryCheckpoint`, `PhaseBindingStamp`,
`PhaseCompletionStamp`, `PhaseFailureOrder`, and `PhaseSavedExclusionReadback`.

The first improvement needs **no new execution operator**. Use the existing
`drainFuel_trace : ReflTransGen AutomaticStep state (drainFuel fuel state)`:

```lean
(∀ before after, AutomaticStep before after → P before → P after) →
  P state → P (drainFuel fuel state)
```

The scratch *RuntimeKernelProbes.drainFuel_preserves* tests this exact route.
Frame equalities follow by taking `P next := read next = read state`.
Next factor the ordinary/phase recurrences over an eligibility predicate or an
eligible-step function with an independently proved decreasing remaining count.
Keep the existing automatic-event semantics and choose no stronger scheduler.

Estimate: gross 330–500, kernel 60–100, adapters 70–130, net 150–280.
Confidence: high for the trace lift, medium/high for operator consolidation.

### 5. Ordinary exclusion evidence is the zero-frontier instance of suffix evidence

`ExclusionPublicRecord.PublicExclusionRecord` stores receipts plus “excluded iff
some owned event publicly failed”. `SuffixExclusionRecord low inherited` adds
the saved-prefix boundary and inherited exclusions. At `low = 0` and
`inherited = ∅`, their propositions are equivalent. Their `advance`,
*new_event_eq*, *failureCompletionStep*, *completeFailure_publicFailure*,
*inclusionResult*, and expiry/environment proofs are visibly duplicated.

The scratch *public_record_iff_suffix_zero* tests the equivalence. Consolidation
requires extracting common definitions/step lemmas to a lower module: today the
suffix file imports `ExclusionSameConfiguration` and `PhaseCompletion`, so simply
making the ordinary file import the suffix owner risks a cycle.

Stronger nearby theorem: a frontier-indexed record transports along a
`CompletionStep` whenever only newly completed events can introduce new evidence;
the original zero-frontier and phase suffix records become instances. The
evidence direction must stay an iff, not merely “every excluded owner has a
failure”, because public-view reconstruction and clearance use both directions.
Accepted unusable bindings must remain distinguished from omission failures.

Estimate: gross 550–750, shared lower kernel 280–380, adapters 70–110,
net 120–300. Confidence: high mathematical equivalence, medium implementation.

### 6. Count-verdict persistence and collection are application-independent

The three versions of *countForbidden_reaches* in `ReactiveCountAudit`,
`ExclusionCountCollection`, and `PhaseCountCollection` use the same proof:
traffic gives an input-list prefix; serial ordering shows that all earlier
same-author packets were already in the prefix; the verdict depends only on
those packets. The audit collection and arbitrary-policy continuation proofs
are also almost literal copies. Their payload-specific `countPermits/permits`
congruence theorems are the actual adapters.

Extract the earlier-input equivalence first; *RuntimeKernelProbes.earlier_inputs_congr*
is the small test. Then abstract a verdict `V : List (Message P Payload) → Message P Payload → Bool`
with the concrete law that it depends only on earlier same-author identifiers.
Derive persistence from serial-ordered input prefix extension. Put observation
and conditional-delivery coverage around the existing
`sampledTrafficAudit_collection` and `EvidenceReportService.sample_coverage`.
Do not replace conditional coverage by an independence assumption.

Candidate stronger theorem: with a complete deterministic sample, charge for
`who` is zero iff every retained packet attributed to `who` is permitted. For a
randomized authentic sample the reverse implication additionally needs positive
coverage of each forbidden packet; authenticity alone only proves soundness.

Estimate: gross 400–600, kernel 100–170, adapters 80–140, net 150–300.
Confidence: high. Keep attempt-addressed phase verdicts and their event keys.

### 7. Candidate freshness should use one generic recorded-resource invariant

`ReactiveCandidateBudget` and `PhaseCandidateSupply` duplicate
*responseCandidateSlot*, *submittedCandidateSlots_respond*, and almost all of
*candidateRecall_respond*, including the same list-membership derivation.
Both express the stronger invariant “an unrecorded prepared serial is fresh”,
not merely “the next chosen serial is fresh”. The difference is the application
state projection (*application.candidates* versus *application.current.native.candidates*).

A generic recorded-resource lemma needs: a response-to-key extractor;
the current player's recall append law; nonacting players' recall retention;
submission locality at keys not named by that response; packet emission preserves
the extracted key; and a no-spontaneous-allocation property for handle/environment.
Existing `submission_candidate_other` supplies the hard native operation.
The phase adapters must additionally prove `settle_physical` retains candidate
meanings across restore. That is a real obligation, not definitional forgetting.

The generic theorem should produce the unrecorded-key invariant, then derive the
bounded fresh slot via the existing pigeonhole argument; don't bake a particular
catalogue size into the kernel.

Estimate: gross 180–300, kernel 50–90, adapters 50–90, net 70–140.
Confidence: high for response/list part; medium for full handle origin factoring.

### 8. Prove a useful elimination theorem for `PhaseRuntimeState.settle`

`Vegas.EventGraphRuntime.PhaseRuntimeState.settle` has four meaningful outcomes: remain in the installed
phase; advance without a retry; archive and restore a still-live commitment
attempt; or archive and advance an exhausted attempt. Independent inductions
over this same recursion occur in `settle_physical`, `settle_archive`,
`PhaseArchiveGeneration`, `PhaseArchivedOwnPrefix`, `PhaseStoredCheckpoint`,
`PhaseHistoryCheckpoint`, `PhaseFailureCoverage`, `PhaseFrontier`,
`PhaseSavedExclusionReadback`, and `PhaseProposalShadowNormalization`.

Prove a dependent eliminator giving each actual branch and its concrete
*phase.drain*, `restore`, archive append, and recursive-tail arguments. Derive
read-only component frame laws through it. A bundled normalization certificate
may then combine genuinely compatible facts. Do **not** introduce a record
whose fields are all the desired final invariant theorems and ask each caller
to supply them; that just moves proof text into constructors.

Preserve the physical/semantic distinction: restore copies semantic config and
accepted handles from entry, but keeps current candidate catalogue, clock,
exclusions, and all outer execution history. Dynamic private shadow repair may
change its mask; `settle_phaseStateFrame` correctly compares retired *public*
snapshots rather than demanding equality of retired private states.

In contrast, `PhaseBindingRepair.Frame` explicitly assumes both sides clear and
their archives empty. It is a useful narrower adapter, but it cannot substitute
for the full `PhaseProposalShadow` repair argument. Choosing the narrow frame as
the common interface would remove precisely the excluded/canceled-attempt cases
that the stronger theorem proves.

Estimate in the first ten repeated consumers: gross 700–1,100, eliminator and
shared facts 140–220, semantic adapters 250–400, net 250–500.
Confidence: medium; this is the largest promising local engineering project.

### 9. Share first-attempt-exit metadata, not the phase-specific snapshot conclusion

`Vegas.EventGraphRuntime.phase_attempt_stopped_results`,
`Vegas.EventGraphRuntime.phase_attempt_stopped_receipt_snapshot`, and
`Vegas.EventGraphRuntime.phase_attempt_stopped_exclusion_origin` independently
recover ordering, same-attempt phase identity, initialized controls, strict
prefix length, and the first-exit property from `runBehavioralUntil_support_first`.
The latter two repeat a substantial trace-prefix induction.

Add a first-exit metadata certificate around the **existing stopped runner**:
every proper prefix stays in the starting namespace, retains installed phase
identity, and has the generic initialized/order facts; an exit is witnessed by
an actual transition and its prefix. Then keep receipt snapshots, newly excluded
request origins, and archived completion records as separate consequences of
their existing local step lemmas. `Interaction.ReactiveApplication.runRounds_environment_boundary`
is already a reusable first-loss theorem; use it for round-level losses rather
than proving another runner.

Estimate: gross 240–380, kernel 60–100, adapters 70–120, net 100–180.
Confidence: medium/high. Quantify over every supported stopped continuation and
arbitrary legal response policies, not just prescribed clients.

### 10. Move typed handler success/inversion certificates below value swaps

`EventApplication` exposes successful commitment/opening equations and graph-step
facts, while the useful inversions `handle_commitment_conditions` and
`handle_opening_conditions` currently live late in the 1,147-line `EventValueSwap`.
Consequently `Vegas.EventGraphRuntime.handle_playerView_congr_of_sender` does a
roughly 292-line synchronized decision tree, and ownership/invariant/frame proofs
repeat readiness, deadline, sender, candidate owner, node kind, association, raw
typing and resolution checks.

Extract a lower typed acceptance certificate with both directions:
`handle ... = some next ↔ commitment certificate ∨ opening certificate`, including
the exact resulting state. Prove rejection by failure of the certificate.
Use existing `State.complete_playerView_congr`,
`State.acceptHandle_playerView_congr`, and resolution-store congruence for the
positive branch; transport certificates between equal focal views and use the
inverse direction to handle the negative branch. This removes decision-tree
duplication while retaining arbitrary raw/malformed packets.

Estimate across observation, ownership and swap callers: gross 350–600,
certificates 100–160, adapters 100–180, net 100–260.
Confidence: medium/high. The remaining cast-dependent completion code is real;
expect adapters rather than one universal `simp` proof.

### 11. Two typed partial-environment readers can share a dependency traversal

`Vegas/EventGraph/Code.lean` contains `collectPublicReads` and
`GuardCheck.collectReads`, each recursing over a dependent context and proving
congruence, availability, and agreement with a known environment. Their output
value families differ (`L.Val` versus `PublicationResult (L.Val _)`), and guard
operands can read the current proposal without a stored field. Those are
parameters of a common typed partial reader, not reasons to duplicate the
context traversal.

Extract only the context/HasVar/dependency traversal to the foundation. Supply
operand-specific *get?* and footprint laws at the event-graph layer. Keep
expression evaluation and guard semantics where they are. Nearby useful
theorem: the collected environment equals a specified partial environment
exactly when every dependency lookup does; the reverse direction needs care
about unused variables, so quantify over `name ∈ deps` only.

Estimate: gross 160–230, kernel 70–110, adapters 30–60, net 50–100.
Confidence: medium. Do not require names to be unique unnecessarily: `HasVar`
witnesses distinguish positions even where names repeat.

### 12. Behavioral realization has a nearby stronger player-memory joint law

`ReactiveImplementation` and `ReactiveSchedulerImplementation` both use
`GameTheory.Protocol.PrivateStrategy`, but separately reconstruct prefix-aware
transcripts and disintegrate internal memory. The scheduler already proves
`SchedulerImplementation.realizeJoint`, retaining execution jointly with the
posterior final memory; the player's main `Implementation.realize` states a
marginal execution equality.

A useful new theorem is the player's analogous joint equality, with final memory
conditioned on that player's actual recall. The proof follows the existing
response disintegration and arbitrary-opponent/scheduler induction, keeping
memory outside application/network state. Abstract transcript reconstruction for
lists of entries with *beforeView* and chosen output. The remaining player
resume cases (inactive/other player/focal player) are legitimate extra work and
should not be forced into a vacuous interface. Inspect `PrivateStrategy.realize`
and posterior lemmas before introducing a new realization framework.

Estimated transcript/adapter cleanup: gross 70–120, kernel 40–70, adapters 20–40,
net 0–40. Main benefit is the stronger joint theorem, not promised large shrink.
Confidence: high mathematical feasibility; medium implementation effort.

### 13. A common service contract needs physical episode identity; timeliness does not imply blindness

`ReactiveAsyncContract` quantifies over every legal initialized raw history, with
event/entered-time episodes, signed owner activations, and sole-owner-identifier
protection. `ExclusionService` states it on actual wrapper histories using a
native projection; `PhaseServiceContract` uses `(attempt,event)` coordinates.
`PhaseRuntimeState.restore` restarts ready timers at the current physical clock,
so dropping attempt identity would conflate distinct episodes. `ReservedEpoch`
proves these guarantees from actual bounded-gap correlated tapes, cursor/clock
accounting, FIFO processing capacity, and a retry-aware finite work rank.

A credible common contract parameterizes a request coordinate and its physical
episode, owner, readiness stamp, retired/completed predicate, and packet address.
Prove old formulations equivalent to the specializations. Mere fields named
opportunity/inclusion/completion, each assuming the old theorem, would not reduce
the proof obligation. Keep signed-author uniqueness **per coordinate**, strict
clock inequalities, all legal histories, and separate finite-nature assumptions.

`ReactiveLateBlind.BlindToLatePackets` is stronger and different: it quantifies
over **all scheduler recall/view inputs**, including counterfactual erased views.
Neither an asynchronous contract nor bounded gaps proves it. `ReservedEpoch`
processing/activation masks may be arbitrarily jointly correlated; do not insert
independence to simplify posteriors. `pending_receipt_iff_timely_epoch` and
`unsent_request_before_next_offer` supply operational facts, not a blanket
all-view erasure law.

Potential theorem: a restricted blindness domain suffices if it contains every
legal history for every deviating/trembling policy **and is closed under all
erasures used by the proof**. Honest-profile support alone does not suffice.
This is a separate theorem/approval-sensitive semantic question, not a routine
refactor of the existing all-view contract.

Savings: unproven; expect 100–200 lines of shared definitions but comparable or
larger adapters initially. Confidence high in the semantic distinction, medium
in worthwhile contract engineering. This is a genuine consolidation boundary.

### 14. Strengthen completion bounds by dependency height; reuse the existing progress service

`CompletionService` is already the correct model-independent local-to-global
completion kernel: one epoch advances time, samples every ready chance event,
and expires due strategic events. `terminal` uses at most *eventCount* windows,
each of width `maxDeadline + 1`. Do not replace it with a second nearly identical
service abstraction.

A stronger nearby theorem needs no new scheduling assumption: each window
completes **every event ready at its start**, so dependency layers give a bound
of `DAG height * (maxDeadline + 1)` rather than event count times that width.
Define a predecessor-rank height using the existing `EventOrder` well-founded
rank, prove one layer clears per window by `window_completes_ready`, and induct
on layers. A refined weighted critical-path bound may follow, but prove the
uniform-window version first.

This cannot simply replace the `ReservedEpoch` proof: rollback may decrease the
semantic completed set. There the existing `workRemaining` deliberately counts
monotone namespace progress plus residual native work, bounded by excluded-owner
generation. A reusable lexicographic rank-to-Nat/window-progress theorem could
factor its arithmetic, with genuinely local decrease and nonincrease facts.
Keep actual command cursor, global clock, per-episode entered time, and semantic
work as separate quantities.

Savings for the new height theorem: none claimed, about 80–160 new lines.
Possible rank-arithmetic reuse: 30–80 net lines after adapters. Confidence:
high feasibility for uniform-height bound, medium for an economical shared rank API.

### 15. Generalize hidden-value symmetries only after exposing handler frames

`EventValueSwap`, `ReactiveValueSwap`, `PhaseValueSwap`, `PhaseSwapApplication`,
`PhaseProposalShadow*`, and `ValueSwapPairs` carry substantial hard mathematics:
private candidate meanings change while public observations and other players'
views are retained. *HiddenSwap.handle_swap* has explicit accepted-bind
compatibility and fixed-read resolution conditions; these must not disappear in
a shorter interface. Dynamic shadow masks additionally depend on completed
bindings and archived attempt state.

Nearby stronger theorem: compose checked local hidden-value symmetries (with
transported compatibility hypotheses) to obtain a finite-permutation simulation,
then preserve the complete external execution law against transformed focal
policies and arbitrary foreign policies. For finite domains, existing pair
swaps may already generate the needed permutations; prove the composition laws
before replacing involutions by a more general group-action hierarchy.
Application-level operation equivariance must be proved from field/lookup laws,
not supplied as the desired full-run equality. Initial laws must also be mapped;
the same initial law requires invariance under the symmetry.

Savings: none safely claimed before the handler work. Feasibility: medium/high
mathematically; medium engineering confidence. This offers actual privacy and
strategic-indistinguishability results beyond line-count cleanup.

## Quantifier audit

| Existing certificate | Current domain | What can safely be factored or generalized |
| --- | --- | --- |
| `ReactiveApplication.Invariant` / `StepRelation` | Every application state and primitive operation | Preserve this useful universal API; add a domain-restricted adapter only when a caller proves initial membership and local domain closure independently of the desired invariant. |
| `ServiceInvariant` | Every execution satisfying the predicate; every supported command of the fixed scheduler; unrestricted responses | Do not substitute one prescribed policy's support. The menu form additionally assumes **legal menu actions**, and policy invariants are a distinct, narrower notion. |
| `InformationDiscipline.ready_fields_exact` | Every admissible graph cut with a ready owned event | A reachable-cut version is conceivable, but scheduling/commutation proofs must close that domain under both event orders. Compiler structural certificates already prove the stronger all-cut form. |
| `Vegas.EventGraph.kernelStepThen_eq_independent` | Only actions in the actual first kernel's support and outputs in that graph step's support | This API is already appropriately weak; demanding equality of kernels on all configurations would strengthen assumptions unnecessarily. |
| `Interaction.ReactiveApplication.SubmissionNormalization.consistent_of_splitBayes_projection` | Every raw information site for every perturbation | The later Bayes theorem proves this premise. Limiting-profile support cannot replace it, because sequential consistency constrains off-path beliefs. |
| `BlindToLatePackets` | Every scheduler input holding a late pending packet | Any local-domain replacement must also cover counterfactual erased inputs and every legal deviating/trembling history, as explained above. |

The potential domain-restricted invariant generalization is a new checked
theorem, not permission to change any existing quantifier. Its hypotheses must
be primitive local closure facts, never “the desired invariant holds at all
reachable states”.

## Tests and counterexamples that should survive cleanup

All eight `InteractionTests` modules were included in the surface pass.
`ReactiveMenuRestriction.arbitrary_policy_continuation` and
`arbitrary_policy_state_law` are valuable arbitrary-policy regressions and should
remain quantified over all smaller-menu policies. `ReactivePublication` proves
that rejection spends an identifier and a **fresh** identifier can retry; it
must not become an assertion that the same rejected identifier can be accepted
later. `ReactiveProtocol` records submissions before inclusion, retains own
packets outside the leak mechanism, and distinguishes hidden partial
observations. These examples guard the exact network/recall distinctions that
the proposed projections and rollback factoring must preserve.

Useful additions alongside an actual refactor: a packet pending through phase
rollback remains in traffic/recall but its old attempt token cannot become a
fresh request; a foreign author's packet does not invalidate an honest owner's
sole-identifier guarantee; and correlated activation/processing tapes retain
their correlation after the scheduler-mixture realization. These should be small
checked counterexamples/regressions, not implementation-mirroring tests.

## Checked probe candidates and verification status

1. `ReducedEventOpponentFrame.lean`: delete duplicate ownership proof while
   retaining its downstream frame theorem unchanged. **Root checked** with the
   copied central Lean options. This verifies the local dependency/proof
   replacement, not a production descendant rebuild.
2. `RuntimeKernelProbes.lean`: zero-frontier exclusion-record equivalence and
   automatic-step trace invariant lift. **Both root checked** under the central
   options, with no additional assumptions.
3. The same probe file: generic earlier-input equivalence needed by all three
   count-forbidden persistence proofs. **Root checked** under the central options.

These are four checked scratch theorems, not production refactors. The estimated
savings above remain estimates until the complete production caller graph is
changed and rebuilt.

## Coverage ledger

The generated ledger below lists every scoped module. `D` means selected hard
signatures/proof bodies were read directly; `S` means the module was included in
the complete surface extraction and screened through its declaration-name index
and family searches. `S` is deliberately not a claim of proof-by-proof audit.

<!-- generated-runtime-ledger -->

| Family | Modules | Source lines | Lexical body lines | Selected deep reads |
| --- | ---: | ---: | ---: | ---: |
| Interaction application/network/strategy layers | 126 | 14,423 | 6,270 | 17 |
| Interaction tests | 8 | 818 | 170 | 2 |
| Event graph | 42 | 8,267 | 3,352 | 5 |
| Other pending foundations and adapters | 16 | 2,197 | 1,010 | 3 |
| Native event runtime | 22 | 5,721 | 3,123 | 4 |
| Recovery/permanent exclusion | 42 | 6,946 | 3,329 | 3 |
| Other phase runtime | 142 | 20,848 | 11,234 | 9 |
| Other phase proposal | 28 | 2,690 | 1,135 | 0 |
| Phase proposal shadow/repair | 28 | 4,037 | 2,376 | 2 |
| Phase seed calendar/contracts | 11 | 898 | 300 | 1 |
| Other reactive native runtime | 68 | 9,285 | 3,844 | 4 |
| Reactive private-binding frames | 32 | 4,419 | 2,294 | 4 |
| Reserved epoch scheduler/contracts | 51 | 5,752 | 2,900 | 5 |

All 616 modules follow. Every module has the complete extracted surface in the
surface artifact, including modules with no proof bodies.

| Module | Lines | Body declarations | Review |
| --- | ---: | ---: | :---: |
| `Interaction.ChallengeWindow` | 162 | 4 | S |
| `Interaction.CommitmentCandidates` | 248 | 15 | S |
| `Interaction.CompletePendingObservation` | 85 | 3 | S |
| `Interaction.IdealCommitments` | 106 | 2 | S |
| `Interaction.MessageInvariant` | 108 | 6 | S |
| `Interaction.MessageLedgerCount` | 53 | 2 | S |
| `Interaction.MessageMonitoring` | 59 | 2 | S |
| `Interaction.MessageNetwork` | 124 | 3 | S |
| `Interaction.MessageNetworkCounters` | 76 | 7 | S |
| `Interaction.MessageNetworkIdentity` | 128 | 10 | S |
| `Interaction.MessageNetworkInvariant` | 98 | 8 | S |
| `Interaction.MessageNetworkMap` | 38 | 1 | S |
| `Interaction.MessagePool` | 123 | 1 | S |
| `Interaction.MessagePublication` | 80 | 8 | S |
| `Interaction.MessageRetention` | 93 | 6 | S |
| `Interaction.PendingErasureSelection` | 218 | 8 | S |
| `Interaction.PendingOutsideSelection` | 135 | 7 | S |
| `Interaction.PendingSelection` | 54 | 2 | S |
| `Interaction.ReactiveAddressedScheduler` | 69 | 1 | S |
| `Interaction.ReactiveAliasAdmissibility` | 99 | 3 | S |
| `Interaction.ReactiveAliasBayes` | 170 | 2 | D |
| `Interaction.ReactiveAliasConsistency` | 109 | 3 | D |
| `Interaction.ReactiveAliasEquilibrium` | 204 | 5 | D |
| `Interaction.ReactiveAliasImplementation` | 261 | 11 | S |
| `Interaction.ReactiveAliasIncentives` | 147 | 5 | S |
| `Interaction.ReactiveAliasLaw` | 217 | 7 | D |
| `Interaction.ReactiveAliasSelector` | 259 | 9 | S |
| `Interaction.ReactiveAliasStrategy` | 140 | 7 | S |
| `Interaction.ReactiveAllocation` | 54 | 2 | D |
| `Interaction.ReactiveAnchoredMixture` | 124 | 3 | S |
| `Interaction.ReactiveAnchoredPolicy` | 95 | 4 | S |
| `Interaction.ReactiveAnchoredStopped` | 41 | 1 | S |
| `Interaction.ReactiveAnchoredSupport` | 104 | 2 | S |
| `Interaction.ReactiveAnchoredTrace` | 168 | 3 | S |
| `Interaction.ReactiveApplication` | 152 | 3 | S |
| `Interaction.ReactiveAuditCollection` | 106 | 3 | S |
| `Interaction.ReactiveCompleteInput` | 59 | 1 | S |
| `Interaction.ReactiveCompleteObservation` | 114 | 3 | S |
| `Interaction.ReactiveConsistentHistory` | 143 | 4 | S |
| `Interaction.ReactiveDecisionInformation` | 79 | 3 | S |
| `Interaction.ReactiveEmissionOrder` | 71 | 5 | S |
| `Interaction.ReactiveEnvironmentMass` | 55 | 2 | S |
| `Interaction.ReactiveErasure` | 120 | 1 | S |
| `Interaction.ReactiveEvaluation` | 108 | 4 | S |
| `Interaction.ReactiveEvidence` | 121 | 7 | D |
| `Interaction.ReactiveFiniteAssessment` | 81 | 4 | S |
| `Interaction.ReactiveHistory` | 96 | 6 | S |
| `Interaction.ReactiveImplementation` | 231 | 12 | D |
| `Interaction.ReactiveImplementationContinuation` | 49 | 1 | S |
| `Interaction.ReactiveInvariant` | 197 | 8 | D |
| `Interaction.ReactiveInvariantPrefix` | 61 | 2 | S |
| `Interaction.ReactiveLocalContinuation` | 194 | 5 | S |
| `Interaction.ReactiveLumping` | 51 | 1 | S |
| `Interaction.ReactiveMenuInvariant` | 77 | 1 | D |
| `Interaction.ReactiveMenuLikelihood` | 56 | 2 | S |
| `Interaction.ReactiveMenuPolicy` | 253 | 9 | S |
| `Interaction.ReactiveMenuRestriction` | 111 | 4 | S |
| `Interaction.ReactiveMessageIdentity` | 118 | 5 | S |
| `Interaction.ReactiveMessageReadout` | 62 | 2 | S |
| `Interaction.ReactiveMixtureLikelihood` | 40 | 1 | S |
| `Interaction.ReactiveMixtureRounds` | 292 | 7 | S |
| `Interaction.ReactiveMonitoring` | 149 | 4 | S |
| `Interaction.ReactiveNormalHistory` | 269 | 11 | S |
| `Interaction.ReactiveNormalRecall` | 140 | 10 | S |
| `Interaction.ReactiveObservation` | 42 | 2 | S |
| `Interaction.ReactiveOwnPlay` | 199 | 9 | S |
| `Interaction.ReactiveOwnerSelection` | 43 | 2 | S |
| `Interaction.ReactivePacketEvidence` | 118 | 7 | D |
| `Interaction.ReactivePolicy` | 73 | 2 | S |
| `Interaction.ReactivePolicyInvariant` | 99 | 5 | S |
| `Interaction.ReactivePolicyMixture` | 178 | 8 | S |
| `Interaction.ReactivePriorityErasure` | 131 | 5 | S |
| `Interaction.ReactiveProtocol` | 218 | 8 | S |
| `Interaction.ReactiveProvenance` | 123 | 4 | D |
| `Interaction.ReactivePublication` | 85 | 4 | S |
| `Interaction.ReactiveRawRoundTrace` | 171 | 6 | S |
| `Interaction.ReactiveRecall` | 169 | 8 | S |
| `Interaction.ReactiveRecallEntries` | 76 | 4 | S |
| `Interaction.ReactiveRecallInvariant` | 129 | 4 | S |
| `Interaction.ReactiveReceiptBoundary` | 98 | 3 | S |
| `Interaction.ReactiveReceiptIdentity` | 62 | 3 | S |
| `Interaction.ReactiveReceipts` | 181 | 10 | S |
| `Interaction.ReactiveRecordedMenuTrace` | 78 | 1 | S |
| `Interaction.ReactiveRecordedResponse` | 168 | 3 | S |
| `Interaction.ReactiveRecordedResponseAfter` | 72 | 1 | S |
| `Interaction.ReactiveRecordedRounds` | 31 | 1 | S |
| `Interaction.ReactiveRecovery` | 220 | 9 | S |
| `Interaction.ReactiveResponseAccounting` | 106 | 4 | D |
| `Interaction.ReactiveResponseBelief` | 106 | 4 | S |
| `Interaction.ReactiveResponseBudget` | 88 | 2 | S |
| `Interaction.ReactiveResponseEmbedding` | 74 | 2 | S |
| `Interaction.ReactiveResponseEvaluation` | 92 | 3 | S |
| `Interaction.ReactiveResponseKernel` | 119 | 1 | S |
| `Interaction.ReactiveResponseMenu` | 242 | 11 | S |
| `Interaction.ReactiveResponseNormalization` | 172 | 8 | D |
| `Interaction.ReactiveResponseStopped` | 63 | 1 | S |
| `Interaction.ReactiveRestrictedContinuation` | 34 | 1 | S |
| `Interaction.ReactiveRoundBoundary` | 73 | 2 | D |
| `Interaction.ReactiveRoundReachability` | 47 | 1 | S |
| `Interaction.ReactiveRoundTrace` | 166 | 9 | S |
| `Interaction.ReactiveRoundTracePrefix` | 93 | 1 | S |
| `Interaction.ReactiveRounds` | 204 | 8 | S |
| `Interaction.ReactiveRoundsFiniteness` | 26 | 0 | S |
| `Interaction.ReactiveSchedulerBeforeResponse` | 65 | 1 | S |
| `Interaction.ReactiveSchedulerFinishSeed` | 56 | 1 | S |
| `Interaction.ReactiveSchedulerImplementation` | 202 | 10 | D |
| `Interaction.ReactiveSchedulerObservation` | 24 | 0 | S |
| `Interaction.ReactiveSchedulerRelabel` | 63 | 2 | S |
| `Interaction.ReactiveSchedulerSeedSupport` | 91 | 2 | S |
| `Interaction.ReactiveSchedulerSeedTrace` | 80 | 1 | S |
| `Interaction.ReactiveSchedulerStoppedSeed` | 61 | 1 | S |
| `Interaction.ReactiveSchedulerTerminalMixture` | 39 | 1 | S |
| `Interaction.ReactiveSchedulerTranscript` | 49 | 2 | S |
| `Interaction.ReactiveServiceInvariant` | 71 | 1 | D |
| `Interaction.ReactiveServiceMixture` | 68 | 2 | S |
| `Interaction.ReactiveServiceRounds` | 63 | 4 | S |
| `Interaction.ReactiveStoppedState` | 119 | 2 | S |
| `Interaction.ReactiveStopping` | 225 | 11 | D |
| `Interaction.ReactiveSubmissionSerial` | 186 | 11 | S |
| `Interaction.ReactiveSupportedRounds` | 60 | 1 | S |
| `Interaction.ReactiveTerminalEvaluation` | 57 | 2 | S |
| `Interaction.ReactiveTrafficAudit` | 93 | 2 | S |
| `Interaction.ReactiveTrafficContinuation` | 29 | 1 | S |
| `Interaction.ReactiveTrafficIdentity` | 56 | 3 | S |
| `Interaction.ReactiveTrafficState` | 243 | 10 | S |
| `Interaction.ScheduledOpening` | 50 | 2 | S |
| `InteractionTests.Commitment` | 175 | 14 | S |
| `InteractionTests.CommitmentCandidates` | 34 | 1 | S |
| `InteractionTests.Pending` | 97 | 6 | S |
| `InteractionTests.ReactiveImplementation` | 90 | 4 | S |
| `InteractionTests.ReactiveMenuRestriction` | 111 | 6 | D |
| `InteractionTests.ReactiveMonitoring` | 70 | 3 | S |
| `InteractionTests.ReactiveProtocol` | 174 | 14 | S |
| `InteractionTests.ReactivePublication` | 67 | 5 | D |
| `Vegas.EventGraph.BarrierBlocks` | 161 | 7 | S |
| `Vegas.EventGraph.BarrierInformation` | 274 | 11 | S |
| `Vegas.EventGraph.Barriers` | 108 | 6 | S |
| `Vegas.EventGraph.Basic` | 93 | 1 | S |
| `Vegas.EventGraph.BindingRefinement` | 99 | 7 | S |
| `Vegas.EventGraph.Canonical` | 128 | 5 | S |
| `Vegas.EventGraph.CanonicalNormalization` | 99 | 4 | S |
| `Vegas.EventGraph.CanonicalStep` | 150 | 10 | S |
| `Vegas.EventGraph.Code` | 1039 | 28 | D |
| `Vegas.EventGraph.CommitmentEvidence` | 17 | 0 | S |
| `Vegas.EventGraph.Commutation` | 232 | 10 | S |
| `Vegas.EventGraph.CommutationRecall` | 119 | 5 | S |
| `Vegas.EventGraph.CompletedOutputAgreement` | 26 | 1 | S |
| `Vegas.EventGraph.ConfigRestriction` | 130 | 3 | S |
| `Vegas.EventGraph.Execution` | 462 | 22 | S |
| `Vegas.EventGraph.Information` | 444 | 23 | D |
| `Vegas.EventGraph.KernelCommutation` | 128 | 2 | D |
| `Vegas.EventGraph.NormalizedPolicy` | 178 | 9 | S |
| `Vegas.EventGraph.ObservationStep` | 99 | 5 | S |
| `Vegas.EventGraph.Order` | 171 | 10 | S |
| `Vegas.EventGraph.PolicyCommutation` | 128 | 3 | S |
| `Vegas.EventGraph.PolicyCongruence` | 84 | 1 | S |
| `Vegas.EventGraph.PrivateInputs` | 58 | 5 | S |
| `Vegas.EventGraph.Recall` | 109 | 2 | S |
| `Vegas.EventGraph.RelaxedRecall` | 72 | 1 | S |
| `Vegas.EventGraph.ResolutionFields` | 22 | 1 | S |
| `Vegas.EventGraph.ResolutionProvenance` | 278 | 8 | S |
| `Vegas.EventGraph.RevealRelaxation` | 305 | 16 | S |
| `Vegas.EventGraph.RevealRelaxedScheduling` | 74 | 1 | S |
| `Vegas.EventGraph.SchedulerDeviation` | 144 | 5 | S |
| `Vegas.EventGraph.SchedulerErasure` | 377 | 8 | S |
| `Vegas.EventGraph.SchedulerMixture` | 61 | 1 | S |
| `Vegas.EventGraph.SchedulerPredraw` | 90 | 2 | S |
| `Vegas.EventGraph.SchedulerProtocol` | 472 | 14 | S |
| `Vegas.EventGraph.SchedulerReplay` | 172 | 6 | S |
| `Vegas.EventGraph.SchedulerReplayLaw` | 209 | 4 | S |
| `Vegas.EventGraph.SchedulingLaw` | 60 | 1 | S |
| `Vegas.EventGraph.Semantics` | 243 | 10 | S |
| `Vegas.EventGraph.Sequential` | 292 | 26 | S |
| `Vegas.EventGraph.SequentialLaw` | 444 | 20 | D |
| `Vegas.EventGraph.StateCongruence` | 290 | 12 | D |
| `Vegas.EventGraph.Validation` | 126 | 7 | S |
| `Vegas.Pending.AcceptedEventOwnership` | 62 | 1 | D |
| `Vegas.Pending.ArchiveBindingRecord` | 142 | 3 | S |
| `Vegas.Pending.AttemptNamespace` | 54 | 1 | S |
| `Vegas.Pending.BindingReceiptOrder` | 112 | 5 | S |
| `Vegas.Pending.CompletedBindingReadback` | 32 | 1 | S |
| `Vegas.Pending.CompletionService` | 160 | 5 | D |
| `Vegas.Pending.EventActivationOrigin` | 158 | 9 | S |
| `Vegas.Pending.EventApplication` | 1419 | 48 | D |
| `Vegas.Pending.EventAssociationInvariant` | 221 | 8 | S |
| `Vegas.Pending.EventBindingInvariant` | 568 | 12 | S |
| `Vegas.Pending.EventBindingPublicObservation` | 131 | 2 | S |
| `Vegas.Pending.EventBindingReadback` | 55 | 1 | S |
| `Vegas.Pending.EventCommandFrame` | 72 | 2 | S |
| `Vegas.Pending.EventCommitmentBinding` | 46 | 2 | S |
| `Vegas.Pending.EventCompletionObservation` | 111 | 3 | S |
| `Vegas.Pending.EventExpiryObservation` | 110 | 1 | S |
| `Vegas.Pending.EventHandleObservation` | 474 | 3 | D |
| `Vegas.Pending.EventInitialObservation` | 64 | 2 | S |
| `Vegas.Pending.EventInvariant` | 396 | 18 | S |
| `Vegas.Pending.EventOpponentFrame` | 92 | 2 | D |
| `Vegas.Pending.EventPrivateObservation` | 72 | 2 | S |
| `Vegas.Pending.EventProgress` | 122 | 6 | S |
| `Vegas.Pending.EventPublicState` | 162 | 9 | S |
| `Vegas.Pending.EventSampleObservation` | 38 | 2 | S |
| `Vegas.Pending.EventSequentialTiming` | 38 | 1 | S |
| `Vegas.Pending.EventStore` | 98 | 3 | S |
| `Vegas.Pending.EventSubmission` | 127 | 4 | S |
| `Vegas.Pending.EventValueSwap` | 1147 | 58 | D |
| `Vegas.Pending.EvidenceNormalization` | 184 | 10 | S |
| `Vegas.Pending.ExclusionAcceptedOutput` | 78 | 3 | S |
| `Vegas.Pending.ExclusionApplication` | 215 | 11 | S |
| `Vegas.Pending.ExclusionBoundedBelief` | 166 | 2 | S |
| `Vegas.Pending.ExclusionBoundedHistory` | 142 | 2 | S |
| `Vegas.Pending.ExclusionBoundedInformationHistory` | 117 | 3 | S |
| `Vegas.Pending.ExclusionBoundedLift` | 133 | 6 | S |
| `Vegas.Pending.ExclusionBoundedProfile` | 122 | 3 | S |
| `Vegas.Pending.ExclusionBoundedRoundTrip` | 45 | 1 | S |
| `Vegas.Pending.ExclusionClearBelief` | 146 | 2 | S |
| `Vegas.Pending.ExclusionClearHistory` | 184 | 9 | S |
| `Vegas.Pending.ExclusionClearKernel` | 70 | 3 | S |
| `Vegas.Pending.ExclusionClearLift` | 239 | 15 | S |
| `Vegas.Pending.ExclusionClearReach` | 205 | 6 | S |
| `Vegas.Pending.ExclusionClearStepMass` | 114 | 3 | S |
| `Vegas.Pending.ExclusionCompletion` | 272 | 19 | D |
| `Vegas.Pending.ExclusionContinuationLaw` | 139 | 2 | S |
| `Vegas.Pending.ExclusionCountCollection` | 160 | 3 | S |
| `Vegas.Pending.ExclusionCountMenu` | 389 | 18 | S |
| `Vegas.Pending.ExclusionExitReflection` | 138 | 2 | S |
| `Vegas.Pending.ExclusionFailureOwners` | 57 | 3 | S |
| `Vegas.Pending.ExclusionFiniteNature` | 44 | 0 | S |
| `Vegas.Pending.ExclusionInformationHistory` | 187 | 8 | S |
| `Vegas.Pending.ExclusionInvariant` | 136 | 9 | S |
| `Vegas.Pending.ExclusionLiftTrace` | 200 | 5 | S |
| `Vegas.Pending.ExclusionLiftedSteps` | 198 | 3 | S |
| `Vegas.Pending.ExclusionMenuProjection` | 154 | 8 | S |
| `Vegas.Pending.ExclusionMenuStopped` | 76 | 1 | S |
| `Vegas.Pending.ExclusionNativeFailure` | 110 | 5 | S |
| `Vegas.Pending.ExclusionNativeProfile` | 92 | 3 | S |
| `Vegas.Pending.ExclusionPairedBehavior` | 205 | 2 | S |
| `Vegas.Pending.ExclusionPairedEnvironment` | 282 | 7 | S |
| `Vegas.Pending.ExclusionPairedTransition` | 157 | 1 | S |
| `Vegas.Pending.ExclusionPrefix` | 319 | 10 | S |
| `Vegas.Pending.ExclusionProjection` | 146 | 9 | S |
| `Vegas.Pending.ExclusionPublicRecord` | 509 | 22 | D |
| `Vegas.Pending.ExclusionResponseAliases` | 53 | 2 | S |
| `Vegas.Pending.ExclusionSameConfiguration` | 60 | 3 | S |
| `Vegas.Pending.ExclusionService` | 117 | 3 | D |
| `Vegas.Pending.ExclusionStoppedBoundary` | 158 | 3 | S |
| `Vegas.Pending.ExclusionStoppedLaw` | 232 | 8 | S |
| `Vegas.Pending.ExclusionTerminalClearance` | 202 | 3 | S |
| `Vegas.Pending.ExclusionTransitionMass` | 178 | 3 | S |
| `Vegas.Pending.OnePacketValueSwap` | 246 | 8 | S |
| `Vegas.Pending.OpeningEvidence` | 200 | 12 | S |
| `Vegas.Pending.PhaseAcceptedOrder` | 261 | 7 | S |
| `Vegas.Pending.PhaseAcceptedProgress` | 274 | 9 | S |
| `Vegas.Pending.PhaseActivationOrigin` | 180 | 6 | S |
| `Vegas.Pending.PhaseActivationResponse` | 98 | 1 | S |
| `Vegas.Pending.PhaseApplication` | 487 | 15 | D |
| `Vegas.Pending.PhaseArchiveGeneration` | 271 | 9 | S |
| `Vegas.Pending.PhaseArchiveOrder` | 132 | 4 | S |
| `Vegas.Pending.PhaseArchivedBindingInterval` | 131 | 4 | S |
| `Vegas.Pending.PhaseArchivedBindings` | 187 | 5 | S |
| `Vegas.Pending.PhaseArchivedExclusions` | 161 | 7 | S |
| `Vegas.Pending.PhaseArchivedObservation` | 130 | 4 | S |
| `Vegas.Pending.PhaseArchivedOwnPrefix` | 260 | 6 | S |
| `Vegas.Pending.PhaseArchivedRecall` | 260 | 10 | S |
| `Vegas.Pending.PhaseAttemptCheckpoint` | 143 | 3 | S |
| `Vegas.Pending.PhaseAttemptCompletion` | 324 | 4 | D |
| `Vegas.Pending.PhaseAttemptControls` | 52 | 1 | S |
| `Vegas.Pending.PhaseAttemptReceiptSnapshot` | 356 | 3 | D |
| `Vegas.Pending.PhaseBindingAcceptance` | 200 | 3 | S |
| `Vegas.Pending.PhaseBindingAcceptedReceipt` | 410 | 10 | S |
| `Vegas.Pending.PhaseBindingAdmittedInclude` | 57 | 2 | S |
| `Vegas.Pending.PhaseBindingCheckpointSubmission` | 41 | 1 | S |
| `Vegas.Pending.PhaseBindingCompletionMemory` | 73 | 1 | S |
| `Vegas.Pending.PhaseBindingCountTransport` | 52 | 1 | S |
| `Vegas.Pending.PhaseBindingForeignMemory` | 119 | 3 | S |
| `Vegas.Pending.PhaseBindingForeignSubmission` | 100 | 1 | S |
| `Vegas.Pending.PhaseBindingFreshness` | 159 | 3 | S |
| `Vegas.Pending.PhaseBindingIdleMenu` | 135 | 2 | S |
| `Vegas.Pending.PhaseBindingInertResponse` | 97 | 2 | S |
| `Vegas.Pending.PhaseBindingInvariant` | 217 | 9 | S |
| `Vegas.Pending.PhaseBindingMemoryCallback` | 53 | 1 | S |
| `Vegas.Pending.PhaseBindingMemoryFreshness` | 60 | 3 | S |
| `Vegas.Pending.PhaseBindingMenuShape` | 85 | 1 | S |
| `Vegas.Pending.PhaseBindingOpaqueStep` | 54 | 1 | S |
| `Vegas.Pending.PhaseBindingOpeningRead` | 152 | 2 | S |
| `Vegas.Pending.PhaseBindingPolicy` | 127 | 2 | S |
| `Vegas.Pending.PhaseBindingPreparationMemory` | 140 | 2 | S |
| `Vegas.Pending.PhaseBindingReadiness` | 75 | 1 | S |
| `Vegas.Pending.PhaseBindingReceiptResolution` | 578 | 15 | S |
| `Vegas.Pending.PhaseBindingRepairFrame` | 92 | 4 | D |
| `Vegas.Pending.PhaseBindingRepairInclusion` | 48 | 2 | S |
| `Vegas.Pending.PhaseBindingRepairObservation` | 96 | 6 | S |
| `Vegas.Pending.PhaseBindingRepairProjection` | 85 | 3 | S |
| `Vegas.Pending.PhaseBindingResponseDispatcher` | 40 | 0 | S |
| `Vegas.Pending.PhaseBindingResponseWitness` | 61 | 1 | S |
| `Vegas.Pending.PhaseBindingSampleReplay` | 79 | 1 | S |
| `Vegas.Pending.PhaseBindingService` | 60 | 1 | S |
| `Vegas.Pending.PhaseBindingServiceCompletion` | 52 | 1 | S |
| `Vegas.Pending.PhaseBindingShadow` | 115 | 9 | S |
| `Vegas.Pending.PhaseBindingShadowStep` | 95 | 3 | S |
| `Vegas.Pending.PhaseBindingSlotHistory` | 86 | 2 | S |
| `Vegas.Pending.PhaseBindingSlotPolicy` | 63 | 1 | S |
| `Vegas.Pending.PhaseBindingStamp` | 201 | 5 | S |
| `Vegas.Pending.PhaseBindingStampHistory` | 268 | 8 | S |
| `Vegas.Pending.PhaseBindingSubmittedPreservation` | 87 | 2 | S |
| `Vegas.Pending.PhaseBoundedHandles` | 106 | 2 | S |
| `Vegas.Pending.PhaseCandidateSupply` | 291 | 9 | D |
| `Vegas.Pending.PhaseClearNativeProgress` | 42 | 1 | S |
| `Vegas.Pending.PhaseClearSemanticProgress` | 178 | 4 | S |
| `Vegas.Pending.PhaseCompletedBindingMeaning` | 101 | 1 | S |
| `Vegas.Pending.PhaseCompletion` | 224 | 17 | D |
| `Vegas.Pending.PhaseCompletionStamp` | 233 | 9 | S |
| `Vegas.Pending.PhaseCompletionStampHistory` | 180 | 5 | S |
| `Vegas.Pending.PhaseConsistentContinuation` | 93 | 1 | S |
| `Vegas.Pending.PhaseCountCollection` | 173 | 3 | D |
| `Vegas.Pending.PhaseCountMenu` | 277 | 12 | S |
| `Vegas.Pending.PhaseCountProjection` | 141 | 5 | S |
| `Vegas.Pending.PhaseCountServiceReference` | 45 | 1 | S |
| `Vegas.Pending.PhaseCountUniqueness` | 31 | 1 | S |
| `Vegas.Pending.PhaseCountVerdict` | 204 | 8 | S |
| `Vegas.Pending.PhaseCountedOpeningSubmission` | 68 | 1 | S |
| `Vegas.Pending.PhaseCountedRequestResolution` | 111 | 1 | S |
| `Vegas.Pending.PhaseCurrentPackets` | 61 | 1 | S |
| `Vegas.Pending.PhaseCurrentTokens` | 199 | 8 | S |
| `Vegas.Pending.PhaseEntryExclusion` | 95 | 4 | S |
| `Vegas.Pending.PhaseEntryOwnRecall` | 218 | 4 | S |
| `Vegas.Pending.PhaseEnvironmentIsolation` | 94 | 2 | S |
| `Vegas.Pending.PhaseExclusionOrigin` | 337 | 5 | D |
| `Vegas.Pending.PhaseExclusionRecord` | 241 | 7 | S |
| `Vegas.Pending.PhaseFailureCoverage` | 179 | 13 | S |
| `Vegas.Pending.PhaseFailureOrder` | 228 | 8 | S |
| `Vegas.Pending.PhaseFailureOrderHistory` | 237 | 7 | S |
| `Vegas.Pending.PhaseFiniteNature` | 45 | 1 | S |
| `Vegas.Pending.PhaseFirstResponseRecall` | 246 | 5 | S |
| `Vegas.Pending.PhaseFrontier` | 343 | 15 | S |
| `Vegas.Pending.PhaseHistoryCheckpoint` | 119 | 6 | S |
| `Vegas.Pending.PhaseInputAddress` | 62 | 2 | S |
| `Vegas.Pending.PhaseInputBindings` | 111 | 3 | S |
| `Vegas.Pending.PhaseInputNamespace` | 124 | 4 | S |
| `Vegas.Pending.PhaseLatestBindingHistory` | 226 | 5 | S |
| `Vegas.Pending.PhaseLatestBindings` | 175 | 6 | S |
| `Vegas.Pending.PhaseLive` | 150 | 7 | S |
| `Vegas.Pending.PhaseNamespace` | 133 | 8 | S |
| `Vegas.Pending.PhaseNativeInvariant` | 45 | 1 | S |
| `Vegas.Pending.PhaseNativeProjection` | 77 | 4 | S |
| `Vegas.Pending.PhaseOncePolicy` | 54 | 2 | S |
| `Vegas.Pending.PhaseOpeningAcceptance` | 167 | 2 | S |
| `Vegas.Pending.PhaseOpeningCoverage` | 76 | 1 | S |
| `Vegas.Pending.PhaseOpeningMenuShape` | 160 | 2 | S |
| `Vegas.Pending.PhaseOpeningPolicy` | 109 | 2 | S |
| `Vegas.Pending.PhaseOpeningReceiptOrigins` | 210 | 7 | S |
| `Vegas.Pending.PhaseOpeningResponse` | 152 | 2 | S |
| `Vegas.Pending.PhaseOpeningService` | 131 | 1 | S |
| `Vegas.Pending.PhaseOwnCommitments` | 153 | 5 | S |
| `Vegas.Pending.PhaseOwnCount` | 83 | 3 | S |
| `Vegas.Pending.PhasePacketAddress` | 198 | 6 | S |
| `Vegas.Pending.PhasePacketEvidence` | 95 | 2 | S |
| `Vegas.Pending.PhasePlanSuffix` | 95 | 4 | S |
| `Vegas.Pending.PhasePreparedBinding` | 102 | 3 | S |
| `Vegas.Pending.PhasePreparedOnePacket` | 75 | 1 | S |
| `Vegas.Pending.PhasePrivateService` | 36 | 0 | S |
| `Vegas.Pending.PhaseProposalAccepted` | 271 | 13 | S |
| `Vegas.Pending.PhaseProposalAcceptedHistory` | 128 | 4 | S |
| `Vegas.Pending.PhaseProposalArchive` | 99 | 7 | S |
| `Vegas.Pending.PhaseProposalBindingSlots` | 69 | 1 | S |
| `Vegas.Pending.PhaseProposalCanonicalBinding` | 87 | 1 | S |
| `Vegas.Pending.PhaseProposalCanonicalOpening` | 83 | 1 | S |
| `Vegas.Pending.PhaseProposalEmissionOrder` | 170 | 3 | S |
| `Vegas.Pending.PhaseProposalFailure` | 106 | 2 | S |
| `Vegas.Pending.PhaseProposalFrameStep` | 58 | 2 | S |
| `Vegas.Pending.PhaseProposalFuture` | 78 | 2 | S |
| `Vegas.Pending.PhaseProposalInputSummary` | 97 | 4 | S |
| `Vegas.Pending.PhaseProposalLostBinding` | 44 | 1 | S |
| `Vegas.Pending.PhaseProposalLostBindingClosure` | 44 | 1 | S |
| `Vegas.Pending.PhaseProposalLostRecallReplay` | 40 | 1 | S |
| `Vegas.Pending.PhaseProposalMeaning` | 94 | 1 | S |
| `Vegas.Pending.PhaseProposalNamespace` | 177 | 4 | S |
| `Vegas.Pending.PhaseProposalNormalizationFrame` | 60 | 2 | S |
| `Vegas.Pending.PhaseProposalObservation` | 59 | 1 | S |
| `Vegas.Pending.PhaseProposalOrigin` | 136 | 2 | S |
| `Vegas.Pending.PhaseProposalPacketLaw` | 124 | 5 | S |
| `Vegas.Pending.PhaseProposalPreparationResult` | 68 | 1 | S |
| `Vegas.Pending.PhaseProposalPreparedBinding` | 67 | 1 | S |
| `Vegas.Pending.PhaseProposalPreparedResponse` | 51 | 1 | S |
| `Vegas.Pending.PhaseProposalPreparedUsability` | 77 | 1 | S |
| `Vegas.Pending.PhaseProposalResponseAliases` | 94 | 3 | S |
| `Vegas.Pending.PhaseProposalRetention` | 130 | 3 | S |
| `Vegas.Pending.PhaseProposalShadowAcceptance` | 167 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowAcceptedTrace` | 109 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowActivation` | 76 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowBindingResponse` | 129 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowDrain` | 150 | 8 | S |
| `Vegas.Pending.PhaseProposalShadowEnvironment` | 183 | 3 | S |
| `Vegas.Pending.PhaseProposalShadowEnvironmentRepair` | 163 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowExpiry` | 84 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowForeignBinding` | 208 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowForeignResponse` | 129 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowHandlerRepair` | 121 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowHistory` | 204 | 2 | D |
| `Vegas.Pending.PhaseProposalShadowIncludeRepair` | 178 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowInertResponse` | 90 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowMask` | 165 | 9 | S |
| `Vegas.Pending.PhaseProposalShadowMenu` | 106 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowNormalization` | 209 | 4 | D |
| `Vegas.Pending.PhaseProposalShadowOpening` | 188 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowOpeningAcceptance` | 198 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowOpeningResponse` | 162 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowProgress` | 57 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowRefinement` | 96 | 3 | S |
| `Vegas.Pending.PhaseProposalShadowRejectedTrace` | 109 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowRejection` | 89 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowResponse` | 210 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowResponseRepair` | 205 | 1 | S |
| `Vegas.Pending.PhaseProposalShadowSample` | 95 | 2 | S |
| `Vegas.Pending.PhaseProposalShadowSourceAcceptance` | 157 | 1 | S |
| `Vegas.Pending.PhaseProposalSubmittedBindings` | 105 | 4 | S |
| `Vegas.Pending.PhaseProposalTyping` | 74 | 2 | S |
| `Vegas.Pending.PhaseRawCheckpoint` | 127 | 6 | S |
| `Vegas.Pending.PhaseRawExclusion` | 44 | 2 | S |
| `Vegas.Pending.PhaseReactiveValueSwap` | 50 | 2 | S |
| `Vegas.Pending.PhaseReadiness` | 395 | 9 | S |
| `Vegas.Pending.PhaseReadyBindingDeclaration` | 71 | 1 | S |
| `Vegas.Pending.PhaseReadyPacketStatus` | 221 | 5 | S |
| `Vegas.Pending.PhaseReadyRequests` | 133 | 5 | S |
| `Vegas.Pending.PhaseReadyResolution` | 121 | 3 | S |
| `Vegas.Pending.PhaseReceiptOrder` | 44 | 1 | S |
| `Vegas.Pending.PhaseRecordedBindingMaterial` | 92 | 1 | S |
| `Vegas.Pending.PhaseRecordedCountedRequest` | 66 | 1 | S |
| `Vegas.Pending.PhaseRequestOrigin` | 129 | 4 | S |
| `Vegas.Pending.PhaseRequestProgress` | 59 | 1 | S |
| `Vegas.Pending.PhaseResolution` | 153 | 6 | S |
| `Vegas.Pending.PhaseResolutionPersistence` | 123 | 5 | S |
| `Vegas.Pending.PhaseResponseNormalization` | 89 | 2 | S |
| `Vegas.Pending.PhaseRetiredCompletion` | 181 | 6 | S |
| `Vegas.Pending.PhaseRetryClock` | 157 | 6 | S |
| `Vegas.Pending.PhaseSampleProgress` | 99 | 3 | S |
| `Vegas.Pending.PhaseSavedExclusionReadback` | 415 | 22 | S |
| `Vegas.Pending.PhaseSeedBudget` | 179 | 8 | S |
| `Vegas.Pending.PhaseSeedClockCharge` | 29 | 0 | S |
| `Vegas.Pending.PhaseSeedClockEffects` | 120 | 4 | S |
| `Vegas.Pending.PhaseSeedClosedBound` | 107 | 3 | D |
| `Vegas.Pending.PhaseSeedFreshness` | 58 | 1 | S |
| `Vegas.Pending.PhaseSeedOperationalInput` | 45 | 0 | S |
| `Vegas.Pending.PhaseSeedPhysicalIsolation` | 148 | 4 | S |
| `Vegas.Pending.PhaseSeedRecordedWait` | 47 | 1 | S |
| `Vegas.Pending.PhaseSeedScheduler` | 108 | 0 | S |
| `Vegas.Pending.PhaseSeedServiceBook` | 37 | 1 | S |
| `Vegas.Pending.PhaseSeedServiceMarks` | 20 | 0 | S |
| `Vegas.Pending.PhaseSemanticProgress` | 208 | 5 | S |
| `Vegas.Pending.PhaseSentMenu` | 164 | 2 | S |
| `Vegas.Pending.PhaseServiceContract` | 93 | 0 | D |
| `Vegas.Pending.PhaseServiceProgress` | 183 | 8 | S |
| `Vegas.Pending.PhaseSignedBindings` | 241 | 8 | S |
| `Vegas.Pending.PhaseStoredCheckpoint` | 121 | 6 | S |
| `Vegas.Pending.PhaseSurvivingHistory` | 122 | 6 | S |
| `Vegas.Pending.PhaseSwapApplication` | 130 | 9 | S |
| `Vegas.Pending.PhaseSwapInformation` | 59 | 1 | S |
| `Vegas.Pending.PhaseTerminalExclusion` | 95 | 3 | S |
| `Vegas.Pending.PhaseTimelyResolution` | 91 | 2 | S |
| `Vegas.Pending.PhaseValueSwap` | 214 | 20 | S |
| `Vegas.Pending.PrivateInputs` | 32 | 1 | S |
| `Vegas.Pending.ReactiveAcceptedOutput` | 186 | 8 | S |
| `Vegas.Pending.ReactiveAliasEquilibrium` | 80 | 1 | S |
| `Vegas.Pending.ReactiveAssociationEvidence` | 51 | 2 | S |
| `Vegas.Pending.ReactiveAssociationPersistence` | 42 | 1 | S |
| `Vegas.Pending.ReactiveAsyncContract` | 126 | 0 | D |
| `Vegas.Pending.ReactiveBinding` | 48 | 1 | S |
| `Vegas.Pending.ReactiveBindingAcceptedRecords` | 65 | 1 | S |
| `Vegas.Pending.ReactiveBindingAllocation` | 55 | 1 | S |
| `Vegas.Pending.ReactiveBindingCountedInclusion` | 109 | 1 | S |
| `Vegas.Pending.ReactiveBindingCoupling` | 124 | 3 | S |
| `Vegas.Pending.ReactiveBindingExpiry` | 159 | 3 | S |
| `Vegas.Pending.ReactiveBindingExpiryAccepted` | 97 | 1 | S |
| `Vegas.Pending.ReactiveBindingFrame` | 206 | 9 | D |
| `Vegas.Pending.ReactiveBindingFrameForeign` | 177 | 3 | S |
| `Vegas.Pending.ReactiveBindingFrameOpening` | 299 | 5 | D |
| `Vegas.Pending.ReactiveBindingFrameRounds` | 38 | 1 | S |
| `Vegas.Pending.ReactiveBindingFrameStep` | 344 | 11 | S |
| `Vegas.Pending.ReactiveBindingGuardedStep` | 106 | 2 | S |
| `Vegas.Pending.ReactiveBindingLikelihood` | 31 | 0 | S |
| `Vegas.Pending.ReactiveBindingOmission` | 96 | 5 | S |
| `Vegas.Pending.ReactiveBindingPreparationRecord` | 58 | 2 | S |
| `Vegas.Pending.ReactiveBindingReceipts` | 142 | 5 | S |
| `Vegas.Pending.ReactiveBindingRejectedInclusion` | 89 | 4 | S |
| `Vegas.Pending.ReactiveBindingRepair` | 173 | 4 | S |
| `Vegas.Pending.ReactiveBindingResources` | 60 | 1 | S |
| `Vegas.Pending.ReactiveBindingRestoration` | 191 | 2 | S |
| `Vegas.Pending.ReactiveBindingSchedule` | 96 | 2 | S |
| `Vegas.Pending.ReactiveBindingShadow` | 456 | 15 | D |
| `Vegas.Pending.ReactiveBindingShadowInvariant` | 162 | 7 | D |
| `Vegas.Pending.ReactiveBindingShadowStep` | 158 | 1 | S |
| `Vegas.Pending.ReactiveBindingSubmissionFrame` | 221 | 2 | S |
| `Vegas.Pending.ReactiveBindingSubmittedInclusion` | 91 | 3 | S |
| `Vegas.Pending.ReactiveBindingSubmittedRecords` | 119 | 4 | S |
| `Vegas.Pending.ReactiveBindingSubmittedRepair` | 164 | 2 | S |
| `Vegas.Pending.ReactiveBindingSubmittedResponse` | 64 | 2 | S |
| `Vegas.Pending.ReactiveBindingTranscript` | 117 | 6 | S |
| `Vegas.Pending.ReactiveBindingWindowLaw` | 104 | 1 | S |
| `Vegas.Pending.ReactiveBoundedHandles` | 157 | 5 | S |
| `Vegas.Pending.ReactiveBoundedValues` | 183 | 7 | S |
| `Vegas.Pending.ReactiveCandidateBudget` | 291 | 9 | D |
| `Vegas.Pending.ReactiveCandidateRealization` | 69 | 3 | S |
| `Vegas.Pending.ReactiveCanonicalDecision` | 200 | 8 | S |
| `Vegas.Pending.ReactiveCanonicalMenu` | 414 | 15 | S |
| `Vegas.Pending.ReactiveCanonicalResolution` | 90 | 3 | S |
| `Vegas.Pending.ReactiveCompiledMenu` | 191 | 7 | S |
| `Vegas.Pending.ReactiveCompiledResolution` | 103 | 1 | S |
| `Vegas.Pending.ReactiveContinuationObservation` | 118 | 5 | S |
| `Vegas.Pending.ReactiveCountAudit` | 302 | 8 | D |
| `Vegas.Pending.ReactiveCountVerdict` | 134 | 4 | S |
| `Vegas.Pending.ReactiveCountedResponseForms` | 80 | 2 | S |
| `Vegas.Pending.ReactiveCountedSurvivor` | 60 | 1 | S |
| `Vegas.Pending.ReactiveDisclosure` | 76 | 2 | S |
| `Vegas.Pending.ReactiveDisclosureStability` | 45 | 1 | S |
| `Vegas.Pending.ReactiveEntryStability` | 188 | 6 | S |
| `Vegas.Pending.ReactiveEventStability` | 601 | 14 | S |
| `Vegas.Pending.ReactiveFiniteCompiler` | 73 | 2 | S |
| `Vegas.Pending.ReactiveFiniteResponses` | 244 | 19 | S |
| `Vegas.Pending.ReactiveFreshCallAcceptance` | 77 | 2 | S |
| `Vegas.Pending.ReactiveGuardConformance` | 92 | 3 | S |
| `Vegas.Pending.ReactiveGuardedResponse` | 82 | 1 | S |
| `Vegas.Pending.ReactiveHiddenInclusion` | 158 | 4 | S |
| `Vegas.Pending.ReactiveHiddenResponse` | 149 | 5 | S |
| `Vegas.Pending.ReactiveInitialValues` | 37 | 0 | S |
| `Vegas.Pending.ReactiveLateBlind` | 70 | 0 | D |
| `Vegas.Pending.ReactiveMonitoring` | 38 | 1 | S |
| `Vegas.Pending.ReactiveNormalization` | 176 | 9 | S |
| `Vegas.Pending.ReactiveOnePacketFreshness` | 152 | 3 | S |
| `Vegas.Pending.ReactiveOnePacketMenu` | 321 | 14 | S |
| `Vegas.Pending.ReactiveOpeningConformance` | 49 | 1 | S |
| `Vegas.Pending.ReactiveOpeningLikelihood` | 118 | 2 | S |
| `Vegas.Pending.ReactiveOpeningSettlement` | 319 | 8 | S |
| `Vegas.Pending.ReactiveOpeningWindow` | 55 | 1 | S |
| `Vegas.Pending.ReactiveOwnerActivationRecall` | 87 | 2 | S |
| `Vegas.Pending.ReactiveOwnerOpportunity` | 140 | 2 | S |
| `Vegas.Pending.ReactiveOwnerWindow` | 69 | 1 | S |
| `Vegas.Pending.ReactivePacketEvidence` | 66 | 1 | S |
| `Vegas.Pending.ReactivePolicy` | 101 | 2 | S |
| `Vegas.Pending.ReactivePolicyFacts` | 30 | 1 | S |
| `Vegas.Pending.ReactiveRawBindingFrame` | 63 | 1 | S |
| `Vegas.Pending.ReactiveResolutionEvidence` | 63 | 2 | S |
| `Vegas.Pending.ReactiveResponseAliases` | 57 | 2 | S |
| `Vegas.Pending.ReactiveRevealBlock` | 31 | 0 | S |
| `Vegas.Pending.ReactiveRiskMenu` | 254 | 11 | S |
| `Vegas.Pending.ReactiveRuntime` | 181 | 10 | S |
| `Vegas.Pending.ReactiveSafety` | 43 | 1 | S |
| `Vegas.Pending.ReactiveSampleLikelihood` | 128 | 2 | S |
| `Vegas.Pending.ReactiveSelectionObservation` | 35 | 1 | S |
| `Vegas.Pending.ReactiveService` | 93 | 1 | S |
| `Vegas.Pending.ReactiveServiceAudit` | 103 | 3 | S |
| `Vegas.Pending.ReactiveServiceConditions` | 59 | 2 | S |
| `Vegas.Pending.ReactiveServiceConformance` | 231 | 7 | S |
| `Vegas.Pending.ReactiveServiceOpportunity` | 59 | 1 | S |
| `Vegas.Pending.ReactiveServiceProgress` | 176 | 5 | S |
| `Vegas.Pending.ReactiveSettledStability` | 142 | 6 | S |
| `Vegas.Pending.ReactiveSettledVerdict` | 163 | 7 | S |
| `Vegas.Pending.ReactiveSignedCommitments` | 366 | 12 | S |
| `Vegas.Pending.ReactiveStateInvariant` | 104 | 4 | S |
| `Vegas.Pending.ReactiveSubmissionRecall` | 115 | 6 | S |
| `Vegas.Pending.ReactiveUnusableBinding` | 46 | 1 | S |
| `Vegas.Pending.ReactiveValueSwap` | 283 | 14 | S |
| `Vegas.Pending.RecordedBindingReadback` | 78 | 3 | S |
| `Vegas.Pending.ReservedEpochAcceptingDelivery` | 251 | 2 | S |
| `Vegas.Pending.ReservedEpochAcceptingEpoch` | 151 | 1 | S |
| `Vegas.Pending.ReservedEpochActivationRecord` | 125 | 2 | S |
| `Vegas.Pending.ReservedEpochActivationWord` | 30 | 1 | S |
| `Vegas.Pending.ReservedEpochActiveSlot` | 89 | 4 | S |
| `Vegas.Pending.ReservedEpochAdmission` | 110 | 4 | S |
| `Vegas.Pending.ReservedEpochArrival` | 53 | 3 | S |
| `Vegas.Pending.ReservedEpochCapacity` | 93 | 5 | S |
| `Vegas.Pending.ReservedEpochClock` | 108 | 4 | S |
| `Vegas.Pending.ReservedEpochClockAccounting` | 86 | 3 | S |
| `Vegas.Pending.ReservedEpochCommandShape` | 64 | 3 | S |
| `Vegas.Pending.ReservedEpochCompletion` | 96 | 3 | S |
| `Vegas.Pending.ReservedEpochDelivery` | 79 | 1 | S |
| `Vegas.Pending.ReservedEpochEmissionTime` | 57 | 2 | S |
| `Vegas.Pending.ReservedEpochEmptyPrefix` | 88 | 6 | S |
| `Vegas.Pending.ReservedEpochEmptyProcessing` | 110 | 3 | S |
| `Vegas.Pending.ReservedEpochExhaustion` | 120 | 2 | S |
| `Vegas.Pending.ReservedEpochExpiredRequest` | 83 | 1 | S |
| `Vegas.Pending.ReservedEpochFinite` | 61 | 2 | S |
| `Vegas.Pending.ReservedEpochFirstAcceptance` | 101 | 1 | S |
| `Vegas.Pending.ReservedEpochFirstOffer` | 125 | 3 | S |
| `Vegas.Pending.ReservedEpochFlatWork` | 131 | 4 | S |
| `Vegas.Pending.ReservedEpochFreshResponse` | 148 | 1 | S |
| `Vegas.Pending.ReservedEpochGeometry` | 78 | 3 | S |
| `Vegas.Pending.ReservedEpochInterval` | 97 | 2 | S |
| `Vegas.Pending.ReservedEpochMixtureOpportunity` | 90 | 2 | S |
| `Vegas.Pending.ReservedEpochMixtureReceipts` | 105 | 3 | S |
| `Vegas.Pending.ReservedEpochOpportunity` | 159 | 6 | S |
| `Vegas.Pending.ReservedEpochPendingBound` | 84 | 4 | S |
| `Vegas.Pending.ReservedEpochProcessing` | 76 | 3 | S |
| `Vegas.Pending.ReservedEpochProgress` | 115 | 4 | D |
| `Vegas.Pending.ReservedEpochReceiptBatch` | 62 | 1 | S |
| `Vegas.Pending.ReservedEpochReceiptContract` | 87 | 3 | S |
| `Vegas.Pending.ReservedEpochReceiptDelay` | 139 | 1 | S |
| `Vegas.Pending.ReservedEpochReceiptTiming` | 387 | 6 | D |
| `Vegas.Pending.ReservedEpochRequestBound` | 102 | 1 | S |
| `Vegas.Pending.ReservedEpochRequestProgress` | 104 | 3 | S |
| `Vegas.Pending.ReservedEpochRequestTimer` | 82 | 2 | S |
| `Vegas.Pending.ReservedEpochResolution` | 85 | 2 | S |
| `Vegas.Pending.ReservedEpochResources` | 25 | 1 | S |
| `Vegas.Pending.ReservedEpochSampleProgress` | 97 | 3 | S |
| `Vegas.Pending.ReservedEpochScheduler` | 110 | 6 | D |
| `Vegas.Pending.ReservedEpochService` | 51 | 2 | S |
| `Vegas.Pending.ReservedEpochSlots` | 62 | 4 | S |
| `Vegas.Pending.ReservedEpochTape` | 51 | 1 | D |
| `Vegas.Pending.ReservedEpochTraceDelivery` | 29 | 0 | S |
| `Vegas.Pending.ReservedEpochTraffic` | 152 | 7 | S |
| `Vegas.Pending.ReservedEpochUnsentRequest` | 658 | 10 | D |
| `Vegas.Pending.ReservedEpochWaiting` | 119 | 1 | S |
| `Vegas.Pending.ReservedEpochWaitingPackets` | 73 | 1 | S |
| `Vegas.Pending.ReservedEpochWorkMonotone` | 114 | 6 | S |
| `Vegas.Pending.RevealTranscript` | 79 | 3 | S |
| `Vegas.Pending.RuntimePhase` | 86 | 2 | S |
| `Vegas.Pending.ServicePlan` | 63 | 3 | S |
| `Vegas.Pending.SuffixExclusionRecord` | 413 | 13 | D |
| `Vegas.Pending.ValueSwapPairs` | 254 | 10 | S |
