# SE compilation stack and implementation plan

## Objective and status

Fix the source program, service, observation rule, utilities and deposits before
choosing an equilibrium. Every source sequential equilibrium should have a
native sequential equilibrium preserving the joint initial parameter, public
result and realized settlement law. The final native game retains all bounded
raw responses. Utilities may depend on initial private parameters and public
results; the claim does not cover repaired future private values.

The [full-language calendar capstone](../Vegas/Game/SourceServiceCompilation.lean)
composes the source-to-permitted and permitted-to-raw proof chains for one fixed
finite roster service. The [proof checklist](se-proof-checklist.md) records the
evidence used by that capstone. The [asynchronous plan](se-schedule-generalization.md)
tracks preservation for any builder satisfying the service contract. That
end-to-end theorem remains open. The explicit decision-packet port is being
checked through the calendar proof chain; the whole semantic change is not yet
globally verified.

## Runtime and service boundary

[SourceServiceRuntime](../Vegas/Game/SourceServiceRuntime.lean) supplies the
compiled graph, pending application and initialization. Readiness starts the
event timer. The handler checks readiness, timeliness, ownership and handle
material. There is no grant cursor. Only `.advanceClock` moves time; expiry is
an explicit command. A scheduler's decision to visit an owner does not by
itself enforce the response that owner sends.

[ServiceRoster](../Vegas/Game/ServiceRoster.lean) supplies the fixed-calendar
instance: a finite player roster, protected inclusion or public sampling,
clock ticks and expiry for each sequential event. Every actor must occur in
its own roster. Bindings and resolutions both need this opportunity; a binding
coverage premise alone cannot rule out a silent resolution miss.

The general service contract separates three obligations: give a ready owner
a timely opportunity, include a protected packet before its deadline, and
complete play. The builder reads public data. Its timing and delivery may be
adaptive; its choices are not strategic player actions in this model. A
strategic builder would need its own incentives.

## Stack: one runtime, several strategic games

```text
Original source assessment
  -> retained native responses and source correspondence
  -> effective native responses with audit and continuation repair
  -> bounded raw native responses through the proved alias lift
```

These are policy families and restrictions of one runtime. No edge adds source
syntax, an emitted interpreter or a private memory facility. Each edge must
preserve the relevant execution and observations and compare whole continuation
policies shared across the hidden histories of an information set.

The retained resolution choices are explicit FALSE withholding and effective
TRUE opening packets. Silence is a deferral. At the last timely opportunity,
the fixed-calendar menu requires an actual decision packet. Expiry without a
decision records a public miss. Equal application results do not make silence
and a FALSE packet interchangeable: the pending traffic, receipts and own
recall distinguish them.

## Source correspondence and beliefs

The calendar chain connects [timed policies](../Vegas/Game/SourceServiceTimedPolicy.lean),
[whole-prefix factorization](../Vegas/Game/SourceServicePrefixFactorization.lean),
[owner Bayes posteriors](../Vegas/Game/SourceServiceBayes.lean),
[original source assessments](../Vegas/Game/SourceServiceAssessment.lean) and
[local comparisons](../Vegas/Game/SourceServiceLocalComparison.lean).
Bindings, guarded resolutions and public sampling have separate operational
laws. Their composition must retain the joint source state and actual native
traffic, rather than only the terminal outcome marginal.

The general-builder kernels already cover actual resolution response and
inclusion in [ResolutionDecisionFactorization](../Vegas/Game/SourceServiceResolutionDecisionFactorization.lean)
and [ResolutionInclusionFactorization](../Vegas/Game/SourceServiceResolutionInclusionFactorization.lean),
and actual chance in [SampleEnvironmentFactorization](../Vegas/Game/SourceServiceSampleEnvironmentFactorization.lean).
They retain the actual scheduler history, network, receipts and player recall.
These local laws do not prove delayed completion, a stopped continuation law,
belief preservation or sequential rationality.

Retained earlier deferrals require a stopped law at the actual later decision
site. Own waiting probabilities cancel by decision recall, but the remaining
source and traffic reach weights still need a joint factorization. Escape error
must vanish relative to the probability of reaching that site; an unconditional
vanishing error is insufficient for a rare off-path information set. Passage
and proportional-reach belief transport permit this proof without a common
calendar depth.

## Audit at settlement

[SourceServiceAudit](../Vegas/Game/SourceServiceAudit.lean) defines the actual
terminal audit for any scheduler. It samples signed packets and judges them
against immutable readiness tokens and the final contract record. It separately
reads public missed-decision markers. A report need not contain a transmission
time, prior ledger or physical broadcaster identity.

[ServiceSettledEvidence](../Vegas/Game/ServiceSettledEvidence.lean) classifies
actual content breaches. An evidence-free authenticated FALSE withholding
packet is lawful. The generic retained-packet soundness kernels are in
[SourceServiceSettledSound](../Vegas/Game/SourceServiceSettledSound.lean);
calendar execution and zero-charge composition belong in
[CalendarSettledSound](../Vegas/Game/SourceServiceCalendarSettledSound.lean) and
[CalendarAudit](../Vegas/Game/SourceServiceCalendarAudit.lean).

The audit contract requires authentic partial records, a positive conditional
probability of actual collection when used to deter a first departure, and
collectible collateral. Missing packet reports do not certify silence. Public
miss markers are contract evidence of expiry; protected timely opportunities
are needed to ensure prescribed players are not falsely charged.

The watcher obtains only its actual network observations and included records.
[ChallengeWindow](../Interaction/ChallengeWindow.lean) separates evidence
observation from report delivery through pending messages. Their conditional
bounds may be correlated; no independence or certain observation is assumed.
A watcher may continue observing after a player deadline. Settlement must leave
enough time for the stated report-delivery bound and must not add unmodeled
information before the last strategic choice.

## Deviations and incremental incentives

The calendar proof uses actual stopped couplings for
[binding windows](../Vegas/Game/SourceServiceStoppedBindingWindow.lean),
[foreign turns](../Vegas/Game/SourceServiceOffTurnWindow.lean),
[sampling](../Vegas/Game/SourceServiceSampleRepair.lean) and
[resolution blocks](../Vegas/Game/SourceServiceResolutionBlock.lean).
[RemainingRepair](../Vegas/Game/SourceServiceRemainingRepair.lean) and
[ActiveRepair](../Vegas/Game/SourceServiceActiveRepair.lean) compose them into
whole continuations. [EvaluatorRepair](../Vegas/Game/SourceServiceEvaluatorRepair.lean)
identifies both actual behavioral marginals using one repaired policy at the
information set. Public auditing does not make a privately unusable commitment
openable; repair must preserve the observations relevant to later players.

[RepairSettlement](../Vegas/Game/SourceServiceRepairSettlement.lean) and
[ContinuationComparison](../Vegas/Game/SourceServiceContinuationComparison.lean)
connect those couplings to conditional settlement dominance.
[RestrictionExtension](../Vegas/Game/SourceServiceRestrictionExtension.lean)
and [RawExtension](../Vegas/Game/SourceServiceRawExtension.lean) assemble the
native equilibrium edge.

A one-time deposit pays for a first departure and its whole continuation gain.
After that charge becomes unavoidable it supplies no additional deterrent.
Later native information sites need a consistent rational continuation using
the information actually available. Packet coverage alone cannot prove those
later incentives. The general risk-menu extension isolates exclusion
comparisons but still takes an equilibrium of its retained risk menu as an
input; it is not the original-source capstone.

## Assumptions and acceptance

| Assumption | Required use |
| --- | --- |
| Finite payload coverage and sufficient candidate capacity | Represent every admitted source binding and all bounded raw responses. |
| Timely owner opportunities, protected inclusion and complete play | Implement decisions and distinguish actual misses from scheduler failure. |
| Authentic partial evidence and positive conditional collection coverage | Charge actual attributable departures without charging retained play. |
| Collectible deposits and quasi-linear money utility | Turn settlement deductions into the claimed incentive bounds. |
| Public chance with the specified conditional kernel | Preserve source sampling and its information. |
| Final inclusion and ideal commitments | Give stable contract records and the modeled binding/opening semantics. |
| Initial-parameter/public-result payoff domain | Preserve utilities through private response normalization and repair. |

No theorem here asserts cryptographic or EVM refinement, reflection of all native
equilibria, or executable synthesis of rational off-path strategies. A fixed
playerwise policy compiler and an existential assessment extension are distinct
claims.

The general capstone must derive retained native beliefs and incentives from
an arbitrary original source SE, prove all native comparisons and a common
rational completion, then preserve the actual joint settlement law. Local
acceptance, zero-charge and traffic lemmas are ingredients, not substitutes for
those obligations. Strict whole-project compilation, declaration-reference
checks and the load-bearing SE evidence check are required at a stable checkpoint.
