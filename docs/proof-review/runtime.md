# Runtime proof review and mathematical mining

Scope is the current tree at `ec4de15c`. This is a read-only review: no production
Lean, dependency, language semantics, scheduler contract, SE target, or checklist
has changed. GameTheory is unchanged. Probe files are isolated review evidence,
not migrated production APIs.

## Coverage and method

| Scope | Modules | Physical lines |
| --- | ---: | ---: |
| Interaction | 131 | 14,760 |
| InteractionTests | 8 | 818 |
| Vegas/EventGraph | 44 | 8,206 |
| Vegas/Pending | 442 | 62,122 |
| Total, excluding root aggregators | 625 | 85,906 |

All module sizes, declarations and twelve-line exact cross-file windows were
screened. Declaration surfaces are in `runtime-surfaces.txt`; the separate
lexical window scan produces 32 matches in `runtime-duplicates.json`. These
windows overlap and exclude many renamed variants. They are leads, not a count
of removable code. Source-body measurements below are manually delimited at
specific known declarations; they do not count a return-type `let` as a body.

Selected deep reads included the generic environment-step eliminator, input
recall and serial order, traffic collection, policy recovery, priority erasure,
scheduler observation/stopped seeds, message retention, graph scheduling and
kernel commutation, completion service, typed handler certificates, physical
failure coverage, live stamps and signed bindings, reserved empty processing,
and all three count-audit continuations. Further selected consumer reads cover
RecoveryCountIncentives and CommitTimingInformationAudit. This is not a claim
that every tactic in 85,906 lines was manually audited.

The earlier 64-item implementation ledger was checked before proposing work.
The current typed acceptance, exclusion-evidence, stopped-prefix and invariant
owners are retained. In particular, the findings below identify remaining
consumers or genuinely stronger scopes; they do not propose to re-create those
owners or reopen retained service-contract/permutation hierarchies.

## Ranked findings

### 1. Own count cleanliness is determined by the observed own past

**Checked missing adapter; high confidence; mathematical/API strengthening.**

`Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported`
(`Vegas/Game/RecoveryCountIncentives.lean:254`) currently assumes at lines269–272
that **every** history of the information fiber is OwnerCountClean. But that
particular property is local to the player's own remembered signed outputs.
The inputs of other authors are irrelevant to its verdict.

The owning facts already suffice:

- `Execution.InputRecall`, `Interaction/ReactiveRecall.lean:23`, identifies the
  sender-filtered input list with `outputs (recall who)`.
- `Execution.InputRecall.earlier_inputs_iff_outputs`,
  `Interaction/ReactiveInputOrder.lean:62`, identifies every lower-serial
  same-author test, requiring InputRecall only, without a next-serial or
  serial-order premise.
- `countPermits_congr`, `Vegas/Pending/ReactiveCountVerdict.lean:100`, and the
  analogous PhaseCount verdict congruence are the actual model adapters.
- The raw-history theorem `history_inputRecall`, transported by the actual
  `menu.toRawTrace`, supplies the invariant at **each** site history.

Thus a local premise

```
∀ message ∈ app.outputs past,
  countPermits (app.outputs past) message = true
```

at `site.1 = some (past, view)` supplies the entire current fiber premise.
Equivalently, one actual clean anchor can supply it **after** the proved
information-locality argument. Merely naming an anchor is not a valid shortcut.

The complete generic own-verdict equivalence and actual recovery information-
fiber adapter are in `OwnTrafficLocalityProbe.lean`. Root strict checking passes,
including the explicit obstruction when recall omits actual inputs. The probe
needs no Fintype Player premise. It uses actual histories and existing runtime
objects; no fake model or final-payoff equality is assumed.

The obstruction uses an empty recalled-output list and signed serial0/serial1
inputs. A checker permitting a packet only when there is no earlier own input
accepts the local empty history vacuously but forbids serial1 in the real inputs.
Hence no arbitrary-execution theorem is valid without InputRecall or an actual
history supplying it.

**Actual consumers.** Replace the whole-fiber clean premise in the generic
recovery support-exclusion theorem with the local past check. The phase timing
example already proves its special case in `ownPermitted_iff_past`
(`Vegas/Examples/CommitTimingInformationAudit.lean:135–168`) and reconstructs it
inside the uniform-gap proof at399–423. Instantiate the common locality kernel
there. Its original CountRecall conjunction must remain, or be reconstructed at
all actual histories by `PhaseCount.countRecall_history`; the new pointwise
kernel alone does not prove that conjunction on arbitrary executions.

The strict margin, actual evidence coverage, feasible silent comparator,
integrability, runner factorization and arbitrary-opponent quantifiers remain
unchanged. No statement after a sunk charge or full SE reflection follows.

**Cost.** A generic earlier-author verdict kernel plus actual site transport is
roughly40–65 lines, with about8–15 lines of concrete adapters and a reduced
~32-line phase locality proof. Expect modest feature growth, not a large net
compression. The useful result is an explicit local condition replacing an
opaque universal information-fiber hypothesis. The complete support theorem
has not been rewritten or production-checked by this review.

### 2. Derive remaining handler graph support from the exact certificates

**Checked projections; high confidence; estimated45–53 net lines removed.**

The exact acceptance iff theorems now precede the following proofs, but these
three consumers still repeat the old handle decision tree:

| Declaration | File:line | Current physical body lines |
| --- | --- | ---: |
| private handle_commitment_config_step | EventApplication:945 | 24 |
| handle_opening_config_step | EventApplication:979 | 38 |
| handle_commitment_vacant | ReactiveEventStability:88 | 10 |

The declaration headers and return witnesses can stay exact. Decompose
`handle_commitment_iff` or `handle_opening_iff`, substitute its **actual next
state**, and use the existing private `bind_complete_mem_step` or
`resolve_complete_mem_step` in the owner. Vacancy is a direct certificate field.
Clock and refreshActivated equalities are then reflexive.

`HandlerCertificateProjectionProbe.lean` passes strict checking with the
three complete old statements, retaining typed node identification, the action
`true` at resolution, and the actual deferred-check result (including failure).
The scratch proof derives graph support through public `Config.step_eq_map_of_code`;
production can use its already checked private owner helpers instead.

**Complete consumer route.** The shorter private commitment and public opening
facts continue to feed `handle_config_mem_step` (1070) and
`handle_clock_activated` (1091); those feed `completionStep_handle`
(ReactiveEventStability:102), completion classifiers, stability and all strategic
readers. No extra factual premises or changed callers are required. The
certificate family is already the owner; this is residual consumer migration,
not another acceptance interface.

Current body footprint is72 lines. Reusing in-owner support helpers should need
about19–27 lines, giving45–53 net before any trivial import movement. No new
public API, wrapper, certificate structure or compatibility names are needed.
The three projections are checked; the production family migration and final
physical measurement are not done by this review.

### 3. Make the exact empty-processing law own the weaker segment result

**Inspected complete route; high confidence; estimated35–50 net lines removed.**

`ReservedEpoch.empty_processing_segment`
(`Vegas/Pending/ReservedEpochEmptyProcessing.lean:38–71`) spends23 body lines on a
count induction. It records network, receipts, application and recall length.
But `empty_processing_prefix_law`
(`Vegas/Pending/ReservedEpochEmptyPrefix.lean:61–87`) already proves the exact
**entire execution** law for the same tape, cursor, capacity, epoch and empty-
pending hypotheses:

```
app.runRounds (family runtime leaks packetBudget tape) players count before
  = PMF.pure (emptyPrefix runtime leaks count before)
```

Move the existing prefix definition/frame lemmas and exact law below the
one-round empty-processing theorem in EmptyProcessing. The segment proof becomes
one rewrite, the pure-law support characterization, then its existing frame projections.
This removes the second induction. Delete the now-empty higher module rather
than preserving a forwarding module. Update its only imports: Pending umbrella
and `Vegas/Examples/ReservedEpochBudgetConcurrency.lean:4`.

**Complete consumer route.** `full_processing_epoch_clears` (EmptyProcessing:72)
uses the weaker segment result for post-clear padding. The budget-concurrency
example uses the stronger law directly at90 and the exact prefix frame facts
at42–44,94,100. Both use the same owner after reordering; there is no cyclic
import and no new proof framework.

The two existing modules have110+88 physical lines. Replacing the23-line body
by about5–7 lines plus eliminating the duplicate module header/section/import
scaffolding suggests35–50 net across both owners and both actual import sites.
The five tiny frame inductions need not be generalized further; they are not
the profitable part. The exact full environmentRecall wait records must remain,
not just its length. All policies and fixed correlated tapes remain quantified.
No symbolic clock, physical traffic or rollback semantics change is proposed.
No production pilot or new scratch theorem is claimed checked here.

### 4. One earlier-input audit transport can replace three continuation proofs

**Concrete duplicate consumers; medium confidence; estimated100–150 net lines
if redundant specialized APIs are removed and actual callers are ported.**

| Owning continuation theorem | Declaration/body/end | Body lines |
| --- | --- | ---: |
| ReactiveCountAudit.countForbidden_collection_continuation |140/158/202|44|
| ExclusionCountCollection.countForbidden_collection_continuation |76/94/139|45|
| PhaseCountCollection.countForbidden_collection_continuation |89/107/152|45|

The common134 body lines still construct the same protocol reach, retain a
traffic record for the starting input, eliminate a hypothetical `none` endpoint,
convert final traffic envelopes back to actual inputs, persist the checker
verdict, apply a per-record audit bound and integrate by expectation monotonicity.
The three additional countForbidden_reaches declarations have only one local
use each, inside those proofs.

The lower owners now available are sufficient for a **transport theorem** in
Interaction, without another invariant hierarchy:

1. From `stateTraffic_inputs` and `stateTraffic_reaches`, retain the actual
   starting input's authenticated TrafficRecord. The nonempty witness rules out
   an endpoint `none` because its stateTraffic is empty.
2. `earlier_inputs_reaches` provides exact preservation of earlier same-author
   inputs for the final actual control.
3. A checker congruence on those earlier-input predicates preserves its verdict.
4. Consume a **per-traffic-record** audit bound, already the exact statement of
   the three countAudit_collection / `audit_collection` lemmas. This is an
   existing service-level fact for arbitrary finite traffic, not an assumption
   of the desired policy-continuation collection law.
5. Apply expect_mono with the existing constant and charge integrability guards.

Keep all observation and conditional delivery coverage inside the three real
per-record audit adapters. In particular the evidence projection depends on
the complete final signed-input context; do not replace it by a static starting
verdict, a packet-only authenticity assertion, or independent sampling.

**Complete callers.** Only three Game consumers call the continuation APIs:
`OnePacketExtension.lean:121`, `RecoveryOnePacketExtension.lean:107`, and
`PhaseOnePacketExtension.lean:106`. Port those directly to the generic transport
and their existing per-record audit theorem. Then delete the three specialized
continuation and three single-use persistence declarations, rather than retaining
six compatibility wrappers. The three higher extension theorem headers and
all their full continuation/deviation scopes stay exact.

The estimated reduction subtracts a70–100-line generic statement/proof plus
20–40 total actual callback/adapter lines from the current three continuation
headers/bodies and single-use persistence owners. Keeping specialized wrappers
would erase much of the gain. This needs a full three-consumer pilot; no generic
kernel or numerical saving has been compiler-checked here. It is a remaining
specific consumer family beyond the earlier minimal serial-prefix extraction.

### 5. Admit independent chance nodes in scheduling confluence

**New scope extension; standard probability/confluence; medium proof-engineering
confidence; no compression claim or checked new global theorem.**

`ReadyIndependent` (`Vegas/EventGraph/PolicyCommutation.lean:46–63`) requires
both events in *every distinct ready pair* to have different actual players.
It therefore cannot describe two parallel chance nodes. This is stronger than
the lower commutation API needs:

- `kernelStepThen_map_storeRecall_comm` (KernelCommutation:99–135) explicitly
  permits ownerless events. Its actor condition is only that no player owns
  both events.
- `normalizedPolicyStep` (StateCongruence:58–66) already executes chance via its
  original evaluator and its unique unit action.
- The finite runner/confluence owners already reason about actual completion
  and enough remaining-event fuel.

Generalize the normalized two-event action kernel to compose the existing
normalizedPolicyStep for optional actors. Replace the actor-existence field by
no shared actual actor, and require the normalized action law to be stable under
completion of any other ready event. For a chance event the action kernel is
pure unit; for an owned event, the stability premise must also cover another
ready chance node. The existing public-barrier and reveal-relaxed producers
can discharge these stronger-domain obligations by their ready-pair facts.
All-chance DAGs satisfy the owned-policy condition vacuously and become a useful
new corollary: ancestral sampling order does not affect the terminal typed
store (or the current semanticKey's store/own-recall observation).

**Essential limitation.** A newly public random coin can change a later
strategic policy even when that event has no data-dependency edge. Removing
actor existence alone is unsound. Actual normalized-action/observation stability
is a substantive primitive guard, not an assumed pair-kernel or final-law equality.
No player may own both ready events if original-action recall is preserved.

The current confluence observation forgets the global completion order. Two
schedulers selecting independent events in opposite orders have different
public histories even if their terminal store laws agree. No full-history,
physical receipt, scheduler-path, arbitrary-builder Nash or SE invariance is
proposed. Adaptive-scheduler confluence must still use actual progress and
enough-fuel hypotheses, not a terminality assumption supplied by the caller.

A useful first regression is a graph with two independent sampled Boolean
nodes, checking equal joint terminal stores for both orders; a mixed public-coin
case should demonstrate failure when policy stability is absent. Rework the
existing kernel/confluence family rather than add a second executor or chance-
only proof hierarchy. Expect40–140 net feature lines until a concrete pilot
settles the ownerless branches and adapter costs.

## Smaller cleanup leads

- The existing `environmentStep_cases` is still not used by five directly
  inspected environment preservation proofs: liveBindingStamp_environment
  (PhaseBindingStampHistory:184), liveCompletionStamp_environment
  (PhaseCompletionStampHistory:73), signedBindings_environment
  (PhaseSignedBindings:177), bindingReceipts_environment
  (ReactiveBindingReceipts:84), and candidateValues_environment
  (ReactiveBoundedValues:121). Their model-specific accepted-packet and actual
  command branches must remain. Replacing only repeated support-map/pure
  decomposition suggests25–45 net lines including explicit imports. This is
  residual use of an existing owner, not a new elimination theorem.
- `candidateResult` (EventValueSwap:456) duplicates the match in
  `State.bindingResult` (EventApplication:367). Its pure decoder belongs below
  value symmetries; ArchiveBindingRecord imports EventValueSwap only to reach
  that decoder and its definitional bridge. Move the decoder into EventApplication,
  have the state reader use it once, and port three actual bridge-rewrite sites
  in EventValueSwap/ArchiveBindingRecord. Retire the now-definitional bridge
  instead of adding an alias. Numerous explicit State.bindingResult unfold sites
  also need auditing, so no reliable compression estimate is claimed. Dependency
  ownership is the main benefit; judge it separately from proof shortening.
  Preserve fresh/unopenable/wrong-type failure exactly; a generic opening?
  already exists and must not be replaced.

## Rejected or deliberately limited directions

- FailureCoverage is logically related to ExclusionEvidence at frontier0 with
  inheritance equal to the **current** excluded set. It is not the ordinary
  frontier0/empty exact detector. Dynamic inherited-set rebasing and the short
  one-way coverage API justify the current abstraction; expanding every caller
  to a self-indexed exact-evidence type would make the proof interfaces worse.
- CompletionService residual-height and weighted-path bounds are mathematically
  plausible, but no active service consumer currently uses even its stronger
  height theorem beyond Paper/tests. Do not present another rank framework as
  immediate compression or repeat the already declined rollback-rank proposal.
- EventGraph scheduler erasure already exposes a full semantic-key theorem
  before its store projection. Do not advertise that existing strengthening
  as a missing result. The genuinely missing scope is optional/chance actors.
- The repeated20–30-line runRounds inductions in mixture, recovery, realization
  and seed transport have different conditioning/memory obligations. Adapting
  all of them through a fresh artificial one-player protocol would add a new
  model just to reuse an iterator; no credible net win was established.
- No new common service-contract or arbitrary-permutation hierarchy is justified
  by this review. Physical episodes, guarded inverses, erasures and transformed
  initial laws retain the distinctions recorded in the implementation ledger.

## Checked experiment boundary

Root strict checking passed both isolated files using the central Lake options:
`OwnTrafficLocalityProbe.lean` and `HandlerCertificateProjectionProbe.lean`.
There are no local options, admissions, or copied shadow semantics. The former
checks local own-verdict equivalence, actual recovery fiber transport and the
missing-recall obstruction. The latter checks all three exact existing handler
projection statements. These results validate adapters, not the estimated
whole-family line savings or the optional-actor scheduling extension.
