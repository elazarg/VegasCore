# Runtime proof review and mathematical mining

The runtime findings have checked production implementations. All owners,
actual consumers and test aggregators pass the full warning-strict build.
The exact production-root audit and twenty guarded review experiments pass.
GameTheory, source/runtime execution rules and the fixed SE checklist are
unchanged.

## Coverage and measurement

| Current directory inventory | Modules | Physical lines |
| --- | ---: | ---: |
| Interaction | 132 | 14,874 |
| InteractionTests | 9 | 894 |
| Vegas/EventGraph | 44 | 8,202 |
| Vegas/Pending | 441 | 61,765 |
| Total, excluding root aggregators | 626 | 85,735 |

The review screened module sizes, declaration surfaces and exact cross-file
windows, then deep-read selected owners and their real consumers. These include
input recall and serial order, traffic collection, policy recovery, priority
erasure, scheduler observations and stopped seeds, message retention, graph
scheduling and kernel commutation, completion service, typed acceptance,
physical failure coverage, live stamps and signed bindings, reserved empty
processing and the three count-audit continuations. This is not a claim that
every tactic in the inventory received a manual audit.

The earlier 64 dispositions and [module architecture](../module-architecture.md)
were checked. Existing acceptance certificates, exclusion evidence and physical
invariants retain their ownership. Measurements below compare the reviewed
source with the implementation, count physical lines across complete changed
families, and include actual consumer adapters and regressions. Shared
aggregator imports are accounted for separately. Proof bodies are delimited
manually; return-type `let` bindings are not treated as proof bodies.

## Implemented findings

### 1. Own count cleanliness is local to the remembered own outputs

`Interaction.ReactiveApplication.own_verdict_iff_outputs` in
[ReactiveInputOrder.lean](../../Interaction/ReactiveInputOrder.lean#L143) proves
that an earlier-author checker permits every actual own input exactly when it
permits every output in that player's recall. Its premises are the checker's
congruence on lower-serial same-author inputs and the actual execution's
`Execution.InputRecall`. It needs neither serial ordering nor a Fintype player
premise. The adapter uses
`Execution.InputRecall.earlier_inputs_iff_outputs` from the same owner.

`Vegas.EventGraphRuntime.Recovery.ownerCountClean_of_past` in
[RecoveryCountIncentives.lean](../../Vegas/Game/RecoveryCountIncentives.lean#L31)
instantiates this kernel at every actual information history. It obtains recall
from `history_inputRecall` along the actual `menu.toRawTrace` and recovers the
observed past from `site.1 = some (past, view)`.

Consequently,
`Vegas.EventGraphRuntime.Recovery.forbidden_choice_not_supported` in
[RecoveryCountIncentives.lean](../../Vegas/Game/RecoveryCountIncentives.lean#L287)
now takes the explicit local condition

```lean
∀ message ∈ app.outputs past,
  countPermits (app.outputs past) message = true
```

instead of a universal cleanliness premise over the hidden information fiber.
The full support-exclusion theorem has been ported and its owning module has
passed. The strict collected-deposit margin, coverage, feasible silent
continuation, runner factorization, integrability and arbitrary later opponent
policies remain in force. No compliance after a sunk charge or full SE
reflection follows.

`Vegas.Examples.CommitTimingInformation.ownPermitted_iff_past` in
[CommitTimingInformationAudit.lean](../../Vegas/Examples/CommitTimingInformationAudit.lean#L137)
now uses the same kernel. Its `OwnPermitted` predicate retains the original
`PhaseCount.CountRecall` conjunction. The clean-fiber argument derives that
conjunction at each actual history using `PhaseCount.countRecall_history`;
local verdict equivalence alone does not supply it on arbitrary executions.

The strictly checked missing-recall probe remains an explicit boundary: empty
remembered outputs can omit actual serial-0/serial-1 traffic. A checker requiring
no earlier own input is then vacuously clean on recall but forbids the second
actual input. This refutes removing InputRecall, not an existing production
claim.

The same recovery theorem now requires its base-payoff interval only at actual
native protocol terminal states. `GameTheory.Enforcement.TerminalAudit.utility_abs_le`
in [TerminalAudit.lean](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean#L61)
bounds audited utility by the terminal base bound plus the absolute deposit.
The proof instantiates the existing
`GameTheory.Protocol.InformationModel.BehavioralAssessment.continuationContext_integrable_of_bounded_terminal`
from [BehavioralTerminal.lean](../../GameTheory/GameTheory/Protocol/BehavioralTerminal.lean#L237)
for every actual unilateral replacement; GameTheory itself is unchanged.

Terminal means the native protocol's terminal predicate, including horizon
exhaustion with unfinished application state. A source-completion-only bound
would be insufficient. [InteractionTests/TerminalAudit.lean](../../InteractionTests/TerminalAudit.lean)
exercises unbounded nonterminal base rewards, bounded actual terminals, a
positive charge at an exhausted terminal and the full alternative-policy
continuation-integrability adapter. The new test passes normal acceptance.

The combined locality/terminal family comprises ReactiveInputOrder,
TerminalAudit, RecoveryCountIncentives and the phase audit example: 1,452 to
1,536 lines, **+84 source lines**. The 76-line terminal regression and one test
aggregator import give **+161 lines across the complete family**. This is a
stronger, usable local hypothesis and terminal-only payoff interface, not a
proof-compression claim.

### 2. Handler graph support is projected from exact acceptance certificates

The remaining consumers now decompose the exact
`Vegas.EventGraphRuntime.handle_commitment_iff` and `handle_opening_iff` in
[EventApplication.lean](../../Vegas/Pending/EventApplication.lean#L811), substitute
the certified actual next state and reuse the existing private
`bind_complete_mem_step` or `resolve_complete_mem_step` support proof.

| Consumer | Current source | Proof body before → current |
| --- | --- | ---: |
| private `handle_commitment_config_step` | [EventApplication](../../Vegas/Pending/EventApplication.lean#L945) | 23 → 7 |
| `Vegas.EventGraphRuntime.handle_opening_config_step` | [EventApplication](../../Vegas/Pending/EventApplication.lean#L963) | 37 → 9 |
| `Vegas.EventGraphRuntime.handle_commitment_vacant` | [ReactiveEventStability](../../Vegas/Pending/ReactiveEventStability.lean#L88) | 9 → 4 |

All three statements retain their exact witnesses. Openings still execute the
original `true` resolution action and retain the actual deferred-check result,
including failure. Commitment failure meanings and authenticated handle
ownership are unchanged. Clock and refreshed-activation frames follow from the
same certified state.

The consumers continue through `handle_config_mem_step`,
`handle_clock_activated` and `completionStep_handle` to existing stability and
strategic readers. No new premise, public interface, structure or wrapper was
added. Both owning modules passed normal checks. The complete two-file family
is 2,124 to 2,075 lines: **49 lines removed**, matching the body reduction
69 to 20.

### 3. Exact empty processing owns the weaker segment result

`Vegas.EventGraphRuntime.ReservedEpoch.emptyPrefix`, its five frame lemmas,
`empty_processing_round`, `empty_processing_prefix_law`,
`empty_processing_segment` and `full_processing_epoch_clears` now live in
[ReservedEpochEmptyProcessing.lean](../../Vegas/Pending/ReservedEpochEmptyProcessing.lean).
The pure prefix/frame interface remains generic in players; Fintype is scoped
only to the actual round laws.

`empty_processing_prefix_law` proves the exact entire-execution law

```lean
app.runRounds (family runtime leaks packetBudget tape) players count before
  = PMF.pure (emptyPrefix runtime leaks count before)
```

under the existing cursor, reserved-capacity, processing-epoch and empty-pending
hypotheses. `empty_processing_segment` now rewrites by this law and projects
network, receipts, recall length and application from its unique supported
execution. Its duplicate count induction is gone.

`full_processing_epoch_clears` still uses the segment result for post-clear
padding. [ReservedEpochBudgetConcurrency.lean](../../Vegas/Examples/ReservedEpochBudgetConcurrency.lean#L4)
imports this same owner and uses the exact prefix law and frames directly.
The redundant split module and its umbrella import were removed; no forwarding
module remains.

The law retains every actual environment-recall wait record, arbitrary player
policies and the fixed potentially correlated scheduler tape. Physical traffic,
clocks, receipts and rollback meanings are unchanged. The owning module passed
its normal check. The two-owner footprint is **198 to 162 lines**; the real
example adapter has the same line count and the Pending umbrella loses one
import, giving **37 lines removed across the complete route**.

### 4. One earlier-input audit transport serves all three count models

`Interaction.ReactiveApplication.audit_collection_continuation` in
[ReactiveAuditContinuation.lean](../../Interaction/ReactiveAuditContinuation.lean#L18)
is now the owner of continuation collection. It takes an actual checker
congruence and a per-record audit collection bound, then transports that bound
through every actual response-menu continuation and arbitrary later profile.

The proof retains the starting input's authenticated traffic record using
`stateTraffic_inputs` and `stateTraffic_reaches`. That nonempty witness rules
out a `none` endpoint. `earlier_inputs_reaches` preserves the lower-serial
same-author context; checker congruence supplies the final verdict. The existing
charge integrability and expectation monotonicity complete the bound.

The actual model adapters remain
`Vegas.EventGraphRuntime.countAudit_collection` in
[ReactiveCountAudit.lean](../../Vegas/Pending/ReactiveCountAudit.lean#L78),
`Vegas.EventGraphRuntime.Recovery.countAudit_collection` in
[ExclusionCountCollection.lean](../../Vegas/Pending/ExclusionCountCollection.lean#L27),
and `Vegas.EventGraphRuntime.PhaseCount.audit_collection` in
[PhaseCountCollection.lean](../../Vegas/Pending/PhaseCountCollection.lean#L40).
Their observation and conditional delivery coverage still concern the complete
final signed-input context. Neither packet-only authenticity nor independent
sampling replaces those premises.

The three real consumers call the generic owner directly:
[OnePacketExtension](../../Vegas/Game/OnePacketExtension.lean#L122),
[RecoveryOnePacketExtension](../../Vegas/Game/RecoveryOnePacketExtension.lean#L108)
and [PhaseOnePacketExtension](../../Vegas/Game/PhaseOnePacketExtension.lean#L107).
The three specialized continuation proofs and their three single-use verdict
persistence declarations were removed without compatibility wrappers. The higher
extension statements keep their full continuation and deviation scope.

The generic owner passed its module check. Across that new owner, the three
model owners and all three Game adapters, the family is 1,595 to 1,417 lines:
**178 removed**. Its Interaction umbrella import gives **177 lines removed
across the complete route**. All three downstream consumers pass normal checking.

### 5. Scheduling confluence admits independent chance events

[PolicyCommutation.lean](../../Vegas/EventGraph/PolicyCommutation.lean#L26)
now owns `Vegas.EventGraph.normalizedAction`, `normalizedPolicyStep` and
`policyStepThen`. The action kernel uses the actual normalized behavioral law
for an owned event and the fixed unique action for an ownerless event. Chance
outputs still come from the original node evaluator and ordinary `Config.step`;
there is no second executor.

`Vegas.EventGraph.ReadyIndependent` now requires:

- `ready_pair_not_actor`: no player owns both distinct simultaneously ready events;
- `normalizedAction_complete`: the actual normalized action law stays unchanged
  under completion of every other ready event, for each supplied action/output.

The second guard includes completion of a chance event. It is a primitive
kernel/observation condition, not an assumed two-step diamond or final law.
`Vegas.EventGraph.readyIndependent_of_ownerless` supplies the all-chance case.
The existing `BarrierOrdered.readyIndependent` and
`RevealRelaxedOrdered.readyIndependent` producers discharge their obligations
from their real ready-pair information properties.

`ReadyIndependent.policyStepThen_map_storeRecall_comm` retains the store and
each player's original-action recall. Its semantic-key extension in
[StateCongruence.lean](../../Vegas/EventGraph/StateCongruence.lean#L230) also retains
the cut. The global
`Vegas.EventGraph.ReadyIndependent.runPlan_normalized_semantic_eq_canonical` in
[SchedulerErasure.lean](../../Vegas/EventGraph/SchedulerErasure.lean#L270)
continues to use the actual runner and the guard `config.remaining ≤ fuel`.
Its public scheduler selects an enabled event, and actual step progress drives
the remaining-event induction. The terminal-store corollary is
`ReadyIndependent.runPolicies_store_eq_canonical` in the same owner.

The observation deliberately forgets global chronological completion metadata.
No full-history, public-receipt, scheduler-path, physical-clock, arbitrary-builder
Nash or SE law invariance is claimed. No common actual actor may be introduced
while retaining original own-action recall.

[ChanceScheduling.lean](../../VegasTests/ChanceScheduling.lean) contains two
actual nondegenerate fair-Boolean chance nodes. It checks the local semantic-key
diamond and terminal store equality under every adaptive public scheduler. Its
mixed graph has an independent public coin and a strategic binding policy that
reads the sampled value. An actual supported `true` sample changes the
normalized binding action from `false` to `true`; the profile fails
ReadyIndependent. This proves the supported-kernel obstruction to dropping
policy stability. It does not assert a separate complete scheduler-law
inequality. The existing
[ConcurrentRevealOrderLaw.lean](../../Vegas/Examples/ConcurrentRevealOrderLaw.lean)
is ported to the same API.

The five production/existing-example files measure 1,062 to 1,059 lines:
**3 source lines removed** (PolicyCommutation +41, StateCongruence −17,
SchedulerErasure −31, RevealRelaxedScheduling +3, existing example +1).
The new 166-line regression and its test umbrella import give **+164 lines for
the complete feature**. Kernel and semantic-state module checks have passed;
the complete confluence/producers/regression source passed isolated strict
checking. Full normal downstream acceptance passes.

## Unimplemented smaller cleanup leads

- Five environment-preservation proofs still expand support-map/pure cases
  instead of using the existing `environmentStep_cases`: the live-binding stamp,
  live-completion stamp, signed-bindings, binding-receipts and bounded-candidate
  owners. Their accepted-packet and actual command branches are model-specific
  and must remain. No new eliminator is justified by these short repetitions.
- The pure `candidateResult` decoder still lives in
  [EventValueSwap.lean](../../Vegas/Pending/EventValueSwap.lean#L456), with a
  definitional bridge from `State.bindingResult`. Moving that ownership lower
  could remove ArchiveBindingRecord's value-symmetry dependency. It requires
  auditing the real unfold/bridge consumers, preserving fresh/unopenable/wrong-
  type failure and reusing the existing generic opening decoder. No measured
  compression or completed migration is claimed.

## Rejected or deliberately limited directions

- FailureCoverage relates to ExclusionEvidence at frontier zero with inheritance
  equal to the current excluded set. It is not the frontier-zero/empty detector.
  Dynamic inherited-set rebasing and the short one-way API justify retaining
  this abstraction instead of expanding callers to a self-indexed exact type.
- CompletionService residual-height and weighted-path bounds remain plausible,
  but no active service consumer uses even its stronger height result beyond
  Paper/tests. Another rank framework has no established immediate consumer;
  the declined rollback-rank proposal is not reopened.
- Scheduler erasure already had a semantic-key theorem before store projection.
  The implemented extension concerns optional/chance actors, not discovery of
  that existing observation strengthening.
- Short runRounds inductions for mixture, recovery, realization and seed
  transport retain different conditioning and memory obligations. No credible
  net gain justifies an artificial one-player protocol solely to reuse an
  iterator.
- No new common service-contract or arbitrary-permutation hierarchy is justified.
  Physical episodes, guarded inverses, erasures and transformed initial laws
  retain their distinct contracts.

No local Lean options, admissions or copied shadow executor were introduced.
The full normal build, exact standard-axiom audit and actual regression modules
pass with the boundaries stated above.
