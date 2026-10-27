# Mechanizing the finite broadcast construction

The [broadcast theorem](se-asynchronous-preservation-theorem.md) and its
[fresh-service alternative](se-asynchronous-support-weakening.md) are hand
constructions. The table below distinguishes existing Lean results from the
new adapters needed to implement them. It is not a completion checklist and
does not change the fixed SE target or its checked boxes.

The primary [assembled derivation](se-broadcast-preservation-derivation.md)
uses the [explicit runtime](se-broadcast-runtime-mathematics.md) and deterministic
ledger audit. All bounded authenticated session bodies are recordable. There is
no honest monitor, strategic reporting stage or receipt-dependent audit stop.
The [strategic reporting game](se-strategic-reporting-mathematics.md) and
[evidence-summary lemma](se-evidence-summary-mathematics.md) are separate extension
tools. They do not establish the retained timing/information argument for a
separate announcement-only operation.

The admitted existential statement in [Paper](../Paper.lean) has the order
"there exists one implementation; for every source equilibrium there exists
an implementing equilibrium." The [result carrier](../Vegas/Game/BroadcastImplementation.lean)
defines its payoff and joint-law conclusion without a compiler stub or an
admitted helper definition. It is still a generic finite-game carrier: no formal
operational predicate connects it to the proposed parameters or broadcast
transition system. Adding that constraint is necessary before the statement
expresses blockchain implementation correctness; otherwise the source game
itself could witness existence. The draft is preparation, not a checked theorem
or a complete formal statement of the mathematical construction.

The program scope is finite initial support, finite binding domains and finite
support for every reachable sample of the linear source syntax, so the intended
game has finitely many histories. Unbounded bidding is outside this statement. Integer
payoff expressions need not have a finite ambient type; their reachable
values are finite in the stated game.

## Compiler and runtime objects

| Component | Existing foundation | Required implementation or proof |
| --- | --- | --- |
| Source block batching | Source observations and successor kernels already express a fixed commitment block with only own-value feedback. `Vegas.SourceProgram.CommitPrefix.prefixLaw_view_eq` proves the relevant foreign-view independence. | Define a physical packet containing the owner's separate component handles; prove the vector law, source SE transport and initialized typed-state law. The source syntax and intended game need no change. |
| Selective component opening | Existing source reveals and `Vegas.SourceProgram.Obligation.accepts_eq_predicts` retain guards until all required inputs are published. | Bind each component certificate to its accepted physical block/owner/component. Publish only components in the current original reveal block. Prove that batching does not disclose later components or reorder samples. |
| Fixed windows and recording interval | Supplied runtime parameters and event deadlines exist. The current phase application advances when a phase finishes. | Add readiness gates for the public times A, D and the recording interval. First sends remain possible after A. Record stale bodies independently of executing their inner calls. Prove publication from the actual service bound. |
| Failure and rollback | `Vegas.EventGraphRuntime.PhaseRuntimeState.settle` already rolls back a failed commitment phase when fresh misses occur and preserves earlier checkpoints. | Relate the fixed-window batch controller to these source transitions. The support-free argument requires rollback of the entire current commitment block on any commitment failure. No global abort is needed. |
| Saved obligations and exclusion payoff | Source recovery debt and native phase exclusion lemmas exist; see below. | Prove termination and resolve/check-or-exclude for the new service/controller. A guard can fail at its last input publication, not necessarily at its subject opening. |
| Broadcast occurrences and entries | `Interaction.MessageNetwork` and the reactive recall/receipt modules provide authenticated messages and actual histories. | Distinguish a canonical body from its repeated broadcast occurrences and from the rebroadcaster. Add finite batch/replay actions, immutable body-level jobs, and the appropriate reference-profile projection. Do not erase visible duplicate receipts. |
| Physical authorization | `Vegas.EventGraphRuntime.CommitAttemptId` and `Vegas.EventGraphRuntime.CommitAttemptPacket.tokenValid_retired` already distinguish current and retired attempts. | Add actual installed-phase and accepted-component authorization records; establish persistent positive validity/invalidity checks. A namespace inequality lemma is not the entire authorization/evidence adapter. |
| Service | The existing concurrent implementation uses one correlated reserved tape for the whole run. | Construct the chosen body-level service. Either prove the same-information delayed-delivery repair, or the fresh-body completion and regenerated-continuation conditions. The existing tape mixture is not automatically an instance of the latter. |
| Timing policy | The existing concurrent local-gain theorem is specialized to its implementation and information construction. | For the support-based route, build the joint completion-agent game. For the fresh-service route, use the clock optimizer over success probabilities p_e(a). These are proof-selected strategies; the implementation does not forbid alternative timing. |
| Failure continuation | Generic constrained information-agent completion and perfect-recall one-step bounds exist. | Supply the actual continuation information model. The support-based proof completes full raw handlers. The support-free proof first uses a structurally clean handler, fresh namespaces, old-namespace observation filtering and fixed replay coordinates, then restores raw actions by extension. Players retain their actual memory. |
| Audit and collateral | Existing evidence services and terminal audit accounting support conditional collection and payoff-spread inequalities. | For the primary runtime, implement total outer recording and the positive ledger verifier. Derive inevitable charge at the first forbidden submission; no peer-receipt premise is needed. Fund per-author per-run publication allowances and audit work separately from deterrence collateral. Monitor capture and strategic reporting are separate alternatives. |
| End-to-end law | Current capstones retain initialized readouts and realized payoff laws. Generic continuation extension and SE limit theorems are available. | Instantiate them for the new models and prove the complete initialized source/public/payoff readout correspondence. Existing current-runtime conclusions cannot simply be relabeled. |

The relevant source owners are [CommitBlockInformation](../Vegas/Source/CommitBlockInformation.lean),
[CommitPrefixLaw](../Vegas/Source/CommitPrefixLaw.lean),
[CommitPrefixInformationLaw](../Vegas/Source/CommitPrefixInformationLaw.lean),
[GuardPrediction](../Vegas/Source/GuardPrediction.lean) and
[IntendedGame](../Vegas/Source/IntendedGame.lean).
The current physical controller and namespace are
[PhaseApplication](../Vegas/Pending/PhaseApplication.lean) and
[AttemptNamespace](../Vegas/Pending/AttemptNamespace.lean).

## Results reusable without changing their mathematical statements

The generic finishing results do not mention the reserved scheduler:

- `GameTheory.Protocol.InformationModel.exists_consistent_free_agent_completion`
  in [AgentCompletion](../GameTheory/GameTheory/Analysis/Protocol/AgentCompletion.lean)
  constructs a common fully mixed family and jointly completes free agents.
- `GameTheory.Protocol.InformationModel.BehavioralAssessment.continuationGain_le_of_localGain_le`
  in [SequentialOneShot](../GameTheory/GameTheory/Analysis/Protocol/SequentialOneShot.lean)
  supplies the finite continuation comparison from local bounds.
- `GameTheory.Protocol.InformationModel.BehavioralAssessment.isSequentiallyRational_of_converging_deviations`
  in [SequentialLimits](../GameTheory/GameTheory/Analysis/Protocol/SequentialLimits.lean)
  and the adapters in [LocalSimulationLimit](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
  supply the limiting rationality step once its actual comparisons are proved.
- `GameTheory.Protocol.InformationModel.ActionRestriction.sequentialEquilibrium_extends_of_continuation_unclocked`
  in [PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
  supplies the raw-action extension from one legal retained comparator at each
  retained information set. Its beliefs, arbitrary extending-profile and
  actual-net-payoff requirements must all be instantiated.

The source-level result
`Vegas.SourceProgram.Setup.commitRecovery_terminal_payoff_of_checkpointed_debt`
in [CommitRecoveryDebtPayoff](../Vegas/Game/CommitRecoveryDebtPayoff.lean)
already expresses the inevitable payoff of saved source debt. Its statement
and the source guard identities can be reused. The physical adapter remains
new: `Vegas.reserved_checkpointDebt_behavioral_terminal_payoff` in
[PhaseProposalReservedDebt](../Vegas/Game/PhaseProposalReservedDebt.lean)
uses reserved-service terminal completion explicitly.

`Vegas.phase_excluded_terminal_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean) has arbitrary
menus and scheduler parameters for its existing phase application. It carries
over directly if that application is retained under the new driver. If a new
application/state type is introduced for batches or recording, first prove the
projection and transfer this invariant; its arbitrary-scheduler quantifier is
not an arbitrary-application quantifier.

## Results whose current scope must not be overstated

`Vegas.concurrentRaw_local_gain_le` in
[ConcurrentRawEquilibrium](../Vegas/Game/ConcurrentRawEquilibrium.lean) is a
useful comparison specification, but its current producers use the reserved
implementation and reference-information machinery. It does not already prove
the fresh clock optimizer, partial-view repair or reset quotient.

`Vegas.EventGraphRuntime.ReservedEpoch.full_processing_epoch_clears` in
[ReservedEpochEmptyProcessing](../Vegas/Pending/ReservedEpochEmptyProcessing.lean)
proves a full-processing property for that epoch service. The new theorem
uses individual body publication; it must prove its
own publication invariant instead of importing a full-pool-flush premise.

`Vegas.EventGraphRuntime.PhaseCount.onePacket_raw_sequentialEquilibrium` in
[PhaseOnePacketExtension](../Vegas/Game/PhaseOnePacketExtension.lean) already
accepts an arbitrary leak rule, but applies to its existing one-packet menu,
raw menu, count verdict and evidence service. New replay/batch menus and
singleton/pair witnesses need new restriction and collection adapters.

The current evidence type is `Vegas.EventGraphRuntime.PhaseCount.Evidence`
in [PhaseCountMenu](../Vegas/Pending/PhaseCountMenu.lean). Its coverage premise
`Vegas.EventGraphRuntime.PhaseCount.EvidenceCoverage` in
[PhaseCountCollection](../Vegas/Pending/PhaseCountCollection.lean) concerns
the whole evidence object. The [compact audit service](se-asynchronous-lanes-and-audit-service.md)
uses different evidence: individual authenticated bodies, positive pairs and
public certificate references. That is new verifier/capture work, even though
the generic audit accounting remains useful.

The current configuration
`Vegas.ReservedConcurrentImplementation.Operational` in
[ConcurrentRawSequentialPreservation](../Vegas/Game/ConcurrentRawSequentialPreservation.lean)
still contains complete pending observation. Neither a hand theorem nor an
unrelated generic extension theorem removes that field. The new implementation
needs its own service and information producers before a paper-facing theorem
can claim the new scope.

## A useful implementation boundary

The source language, intended utilities and generic equilibrium foundations
can remain. The substantial new work is the physical packet/service model,
the actual-information adapter, and the deterministic ledger audit. The fresh-service
route simplifies the timing proof but adds an explicit reset/observation quotient;
the delayed-support route retains more operational history but needs its
likelihood repair. The monitored-lane audit is available with either route
when that route's clean-body service conditions hold.

The primary ledger audit needs neither an evidence-capture service nor a
report-all game. Its availability follows from total recording and the assumed
nonrevocable inclusion service for submitted bodies. A monitored backend instead
assumes capture and forwarding. A strategic reporting backend needs the report
game and its incentive proof. Objective verification alone supplies none of
those availability properties. The admitted Lean draft does not discharge the
operational adapters or change the checked paper results.
