# Absorbing failure as the source language semantics

Absorbing failure changes the source games. A player cannot withhold once and
later resume successful play. The replacement belongs to the ordinary intended
game -> source -> dependency graph -> ledger tower: the intended game restricts
source menus, and each remaining level has one authoritative executor.

This research branch implements absorbing source and graph execution and checks
source-to-graph compilation for every source profile and public scheduler.
The unified ledger application also has checked operational graph refinement.
Exact graph-deviation backtranslation and source-to-graph approximate Nash
correspondence are checked, including parameter-dependent expression payments.
Whole native source-continuation laws and common consistent equilibrium
completion are checked. Their remaining client and strategic consumers still
require ports. The full branch is not a verified replacement for the maintained
tower; the complete build and paper acceptance gates remain open.

## Authoritative source execution

[Semantics](../Vegas/Source/Semantics.lean) has one recursive evaluator,
`SourceProgram.runFrom`, over `Config`. The protocol uses the same sample,
binding and revelation successors. Execution returns the complete terminal
configuration; public projection retains public typed cells and default history.

A binding decision is `Option (PublicationResult payload)`:

* `none` omits the binding and publicly defaults the owner immediately;
* `some (.success value)` accepts an ordinary opaque binding;
* `some .failure` accepts an opaque but unopenable binding. Its owner remains
  active until a public failed opening, unless another public default occurs.

The binding cell stores a `PublicationResult`. Equal hidden cell contents do
not imply equal public default events. In particular, the source cannot infer
public default from hidden failed binding values. The native runtime records this distinction through the same graph completion:
[EventApplication](../Vegas/Pending/EventApplication.lean) admits a handle with
`some result`, and records a missing binding with `none` at its due expiry.
Receipt-provenance consumers remain part of the ledger port.

An active owner's attempted reveal runs the retained guard checks. Withholding,
an unopenable binding or a rejected publication produces public failure and
defaults that owner. Every later owned instruction completes automatically with
failure. It queries no policy callback and appends no invented own action.
Automatic openings still resolve their binding and retain guard bookkeeping.
Public samples follow their declared laws and execution continues.

[DisclosureBehavioral](../Vegas/Source/DisclosureBehavioral.lean) normalizes
only unopenable disclosure attempts. Authentic attempts remain unchanged even
when deferred guards reject publication. Its uniform profile transformation
preserves the joint law of every typed cell and the full default history for
arbitrary profiles, prior configurations and initial laws, without a
finite-player or posterior-reconstruction premise. Defaulted owners' private
intention lists can differ; full configuration equality is not asserted.
[DisclosureOpening](../Vegas/Source/DisclosureOpening.lean) and
[DisclosureSupport](../Vegas/Source/DisclosureSupport.lean) use the same
authentic-binding criterion.

[ValueBinding](../Vegas/Source/ValueBinding.lean) excludes accepted unusable
bindings while retaining public omission. [Honest](../Vegas/Source/Honest.lean)
requires successful admission at every active binding and disclosure at every
active reveal; omission is not honest play. Its initialized execution law
proves successful typed cells and an empty default set.
[IntendedPlay](../Vegas/Source/IntendedPlay.lean) checks that intended play keeps
this clear-default invariant. The intended-opening adapter uses the same
[authentic opening](../Vegas/Source/AuthenticOpening.lean) transformation.

[BindingNormalization](../Vegas/Source/BindingNormalization.lean) supplies a
uniform pure-policy compiler that replaces accepted unusable bindings with
values and withholds precisely those replacements. It retains public omission
and preserves the complete public-outcome/default-history law from every
initial state. Its private reconstruction retains the actual public record;
inactive owners have no callback to reconstruct.
[Exclusion](../Vegas/Source/Exclusion.lean) reads public defaults alone. Its
trace invariant proves that an owed failure on an actual initialized history
implies terminal public default, without an initial-success or finite-player
premise. Hidden unusable bindings alone do not establish exclusion.

Policy callbacks accept proof that their owner is active. This removes unused
inactive responses from the strategy type and permits exact strategy
equivalence with legal protocol policies. It imposes no restriction on an
active player's action law. The source kernel proves persistence of default,
automatic failure and absence of automatic own-action recall.

[AbsorbingFailure](../VegasTests/AbsorbingFailure.lean) checks complete runs with
withholding, binding omission and accepted unopenable bindings. The last case
permits an intervening successful binding before the bad opening becomes public.

## Public information and recall

[DefaultHistory](../Vegas/Foundation/DefaultHistory.lean) is the single
authoritative public default record. Each completed source instruction adds one
entry, newest first: a newly defaulted player, or no new default.
`Vegas.SourceProgram.Config.defaulted`
is derived from this record. The initial record is empty, regardless of hidden
input binding values.

Every player's view retains this public record and its actual own actions.
Retaining only the current default set would lose information. Suppose Alice
omits a binding before Bob acts in one history, but accepts an unopenable binding
and fails its opening after Bob acts in another. Alice's final failed cells and
default set can agree, while Bob previously observed different public status.
The public record keeps these histories distinguishable. It adds no observation
that a player did not already receive.

Earlier views are reconstructed by dropping the newest typed cell and public
record entry, and dropping the newest own action only when the player was active
at that instruction. No private configuration or remembered policy is needed.
The protocol recall proofs must use these projections, including automatic steps.

[ProtocolBehavioralPolicy](../Vegas/Source/ProtocolBehavioralPolicy.lean) and
[SetupProtocolBehavioral](../Vegas/Source/SetupProtocolBehavioral.lean) check exact
policy equivalence and behavioral continuation laws at every legal history.
[ObservationRecall](../Vegas/Source/ObservationRecall.lean) reconstructs earlier
views; [SetupProtocolRecall](../Vegas/Source/SetupProtocolRecall.lean) proves
perfect recall and decision recall under every commitment interface.
[InitialState](../Vegas/Source/InitialState.lean) retains the initial environment
and its joint parameter/public-result law through the full configuration readout.
[Metadata](../Vegas/Source/Metadata.lean) checks that every supported terminal
configuration has exactly the syntax-determined guard registry and revelations.
These fields can be reconstructed by compiler readout without another evaluator.

## Utility and transfers

[Utility](../Vegas/Source/Utility.lean) defines the canonical `exclusionUtility`
from public default membership, including binding omission. Its public-outcome
rule agrees definitionally with `Config.utility`. For an active player, the
ordinary valuation can read all typed cells
and the complete public default history. A defaulted player receives its
declared exit utility under every continuation. The source proof gives fixed
expected utility and integrability for an already defaulted player without a
finiteness or bounded-valuation hypothesis.

Failed-reveal counts remain a diagnostic of publication cells. They are not the
control state for source utility. Count-only utility laws for arbitrary public
outcomes do not apply to the canonical rule; consumers must use public membership
or prove a reachable-outcome correspondence.

Exit utility and exit transfer remain distinct. The monetary readout must return
the declared exit transfer after default; external valuation must be included
when defining the fixed total exit utility. The ledger's count audit can still
deduct for forbidden traffic after default.
[NativePaymentReadout](../Vegas/Game/NativePaymentReadout.lean) checks the joint
cash and utility readout, with valuation factorization required only on actual
clear support. Its final strategic preservation consumers remain open.

No independence, service, coverage, finiteness or funding premise is added.
Restricting surviving players' valuations to ignore public default history
would be an additional assumption and is not part of this design.

The ambient public-record type admits impossible histories. Utility-range ports
must use their actual execution domain or a bounded extension outside it;
boundedness on extra impossible records must not become a hidden new premise.

The native count-audit extension bounds utilities on legal bounded-menu
histories. Its source-payoff specialization bounds ordinary utility only at
successful source readouts of those histories. Missing readouts and declared
exit values have their own explicit branches. Arbitrary fabricated protocol
states and impossible public records require no ordinary-utility bound.

[IntendedPreservation](../Vegas/Game/IntendedPreservation.lean) and
[IntendedNash](../Vegas/Game/IntendedNash.lean) check canonical fixed-exit
sequential and approximate Nash equilibrium preservation under every sitewise
binding admission. They use the declared exit-floor comparison on actual
intended terminal readouts, with no payoff-spread premise. The sequential
assessment extends the intended strategy; every extending source profile
preserves the intended Nash guarantee with the same approximation error.
Both results preserve the joint full-readout/payoff law and have no public
default or failed reveal on equilibrium paths. Their deviation proof uses actual
trace provenance to turn owed failure into terminal public default.
It does not assert that every source equilibrium is clean when exit payoffs tie
with ordinary payoffs.

The optional count-penalty preservation results in those modules bound the
payoff spread only over terminal legal source histories; impossible public records and unsupported
parameters need no bound. They do not infer a bound on a freely declared exit
value. Native strategic preservation and settlement remain separate checks.

## Graph and ledger port

Binding decisions in [Code](../Vegas/EventGraph/Code.lean) use the same
accepted/omitted distinction; stored binding values remain publication results.
The single [executor](../Vegas/EventGraph/Execution.lean), `Config.step`, normalizes
actions of defaulted owners and updates public failure control. Its public
default history is derived from completion history, with no independently stored
control set. Every event completion remains in that history; its optional
decision distinguishes actual player choices from automatic or chance steps.

The executor checks persistent defaults, unchanged step laws under every
suppressed requested action, field persistence, chronological predecessors,
cut progress and termination. [EventGraphDefault](../VegasTests/EventGraphDefault.lean)
checks actual two-binding execution: omission suppresses a later requested
successful binding, while an accepted unopenable binding permits it.

The [graph observations](../Vegas/EventGraph/Information.lean) retain this public
history, and actual recall filters out automatic completions. Logical policy
observations keep the same public log. [Policies](../Vegas/EventGraph/Semantics.lean)
have active-only callbacks and supply automatic failure after default; their
executor still checks finite branching and termination under public scheduling.

[Observation congruence](../Vegas/EventGraph/ObservationStep.lean) compares every
public effect, including the newly public default entry. Equal hidden stored
failure values alone do not give equal public observations: foreign omission
and accepted unusability can differ publicly. This is a calculated effect in
the observation lemma, not an added compiler or environmental assumption.
The source policy compiler preserves this complete decision view at each aligned
prefix. [Policy backtranslation](../Vegas/Compile/EventGraphPolicyBacktranslation.lean)
reconstructs the complete active-player view and invokes the original graph
callback. Automatic completions create no callback to reconstruct.

Public omissions introduce information dependencies. If Alice's source binding
precedes Bob's, Bob may condition on Alice's default. Scheduling Bob first can
change their joint outcome law. The
[compiler constructor](../Vegas/Compile/EventGraphAssembly.lean) generates
every earlier source instruction as a dependency, using the sequential order
and cut lemmas in [Order](../Vegas/EventGraph/Order.lean). This supplies the
required order without a scheduler assumption. Typed node lowering, local
evaluation, state/reference agreement and input encoding are checked with this
constructor.

[Law](../Vegas/Compile/EventGraphLaw.lean) proves the full configuration law at
every aligned suffix using the single source and graph executors.
[Canonical](../Vegas/Compile/EventGraphCanonical.lean) instantiates it with actual
initial configurations and an arbitrary private/public setup law.
[Scheduling](../Vegas/Compile/EventGraphScheduling.lean) proves that every public
scheduler has the same complete graph law, even for arbitrary graph profiles:
the compiler-generated order makes the enabled-event type a singleton.
Consequently `scheduled_terminalConfig_law` and `scheduled_setup_law` preserve
all five source configuration fields for every source profile. No finite
payload, finite-history, independence or service premise enters these laws.
Typed-store and raw expression-payout laws are projections; the latter do not
replace the outstanding exit-transfer settlement port.

[Deviation](../Vegas/Compile/EventGraphDeviation.lean) backtranslates every
graph deviation to one source policy, chosen before the initial state is drawn.
Under every public scheduler the replacement preserves the entire terminal
source configuration law, including arbitrary correlated setup laws. No
mixture over source policies or finite-alphabet premise is needed for this law.
[EventCompilation](../Vegas/Game/EventCompilation.lean) uses this exact
deviation correspondence for source-to-graph approximate Nash equivalence.
[ProgramPaymentNash](../Vegas/Game/ProgramPaymentNash.lean) retains the initial
parameter, typed public values and public default history in its observation;
the payment and Nash statements retain their stated integrability premises.

The regressions include withholding, omission and accepted unusability under
arbitrary schedulers, plus a two-player response to public omission under the
greatest-enabled scheduler. The response cannot be moved before its public cause.
More concurrency requires a separate information-preservation proof.
Unconditional commutation of same-owner events and unconditional independence
of different owners' binding decisions are false for this semantics.

## Authoritative ledger execution

[EventApplication](../Vegas/Pending/EventApplication.lean) retains one native
`State`, containing the graph configuration, accepted handles, immutable
candidate meanings and relative-clock metadata. Public default is derived
from its graph configuration; there is no separate exclusion set or wrapper
application. Accepted unusable bindings remain opaque. Physical silence
stutters until an owned deadline is due. Calls authored after public default
are rejected even when their addressed event is ready and timely.

[ExclusionCompletion](../Vegas/Pending/ExclusionCompletion.lean) performs bounded
automatic service directly on that state. Each automatic completion is a
supported step of the graph executor, records no new decision or default,
and preserves default membership, handles, candidates and the clock. The drain
terminates with no ready event owned by a defaulted player.
[ExclusionInvariant](../Vegas/Pending/ExclusionInvariant.lean) proves that it
preserves native reachability, stored cells and existing activation timestamps
for unfinished events.

[ReactiveRuntime](../Vegas/Pending/ReactiveRuntime.lean) is the sole compiled
application. Successful inclusion and environment service atomically drain
automatic completions. Its observations contain the graph's public default
history, without copying that history into another state field.
[ReactiveGraphSteps](../Vegas/Pending/ReactiveGraphSteps.lean) and
[GraphRefinement](../Vegas/Pending/GraphRefinement.lean) prove that arbitrary raw
responses and public schedulers follow finite supported graph paths. No
finiteness, visibility, service or monotone-withholding assumption is added.
Completion remains conditional on the same `CompletesPlay` service predicate;
that predicate is not an existence theorem for a completing scheduler.

[ReactiveStateInvariant](../Vegas/Pending/ReactiveStateInvariant.lean) proves
reachability, clock coherence, permanent stored values and automatic-service
quiescence on initialized physical histories.
[RuntimeDefault](../VegasTests/RuntimeDefault.lean) distinguishes early silence,
accepted unusability, due omission, atomic application draining and rejection
at an otherwise ready, timely event after default.
[EventBindingInvariant](../Vegas/Pending/EventBindingInvariant.lean) retains
exact immutable binding/handle provenance through native and automatic steps.
[ReactiveAssociationEvidence](../Vegas/Pending/ReactiveAssociationEvidence.lean)
extends it to every initialized physical history.
[ReactiveSignedCommitments](../Vegas/Pending/ReactiveSignedCommitments.lean)
connects accepted event handles to their owner's actual signed emission recall,
while [ReactivePacketEvidence](../Vegas/Pending/ReactivePacketEvidence.lean)
preserves the truth of carried opening certificates through arbitrary raw
responses, forwarding, rejected calls and automatic completion. These facts
retain their original hypotheses; they impose no honesty or service premise.

[EventCompletionObservation](../Vegas/Pending/EventCompletionObservation.lean)
compares the exact new public default entry and proves that automatic service
preserves equal focal views. Its focal-authored call, arbitrary commitment and
expiry corollaries in [EventHandleObservation](../Vegas/Pending/EventHandleObservation.lean)
and [EventExpiryObservation](../Vegas/Pending/EventExpiryObservation.lean)
derive that entry from retained observations. Their hypotheses are unchanged;
foreign hidden candidate meanings need not agree. The graph-observation
projection of a native player view is owned by the application layer and
shared by [continuation observation](../Vegas/Pending/ReactiveContinuationObservation.lean).

[PublicFailureEvidence](../Vegas/Pending/PublicFailureEvidence.lean) lifts
native receipt footprints and failure persistence along finite completion
paths, and [ExclusionNativeFailure](../Vegas/Pending/ExclusionNativeFailure.lean)
reads default monotonicity directly from graph configurations.
[ReactiveSampleLikelihood](../Vegas/Pending/ReactiveSampleLikelihood.lean)
retains the actual physical chance law through atomic draining, while
[ReactiveServiceProgress](../Vegas/Pending/ReactiveServiceProgress.lean)
preserves clocks, completed events and unfinished-event deadlines through
arbitrary responses and environment operations.

[ExclusionEvidence](../Vegas/Pending/ExclusionEvidence.lean) proves the native
failure/default correspondence through admission, opening, chance, expiry,
clock changes, private submission and automatic completion. Initialized
histories identify the publicly failed event owners with graph default
membership, without a finite-player premise.
[Activation origins](../Vegas/Pending/ReactiveServiceOpportunity.lean) hold
through arbitrary raw operations: live activation times are retained or
created no earlier than the operation's entry clock.

The [runtime decision translator](../Vegas/Pending/ReactivePolicy.lean) sends
an authentic requested opening even when its public guard fails. Native
acceptability permits this call, and the handler records its actual failure
result. The count verdict checks authentication, typing, signed binding
association and first use; it does not require guard success. The separate
successful-content predicate for settled auditing retains its stricter guard
condition. An all-profile client theorem cannot infer that stricter predicate
merely from emission.

[Source checkpoints](../Vegas/Game/SourceServiceCheckpoint.lean) now retain
typed cells, actual own choices and the complete public default history.
The [prefix decoder](../Vegas/Game/SourceServicePrefix.lean) copies that history
from the native graph configuration. [Information reconstruction](../Vegas/Game/ServiceInformation.lean)
and [active-view reconstruction](../Vegas/Game/ServiceObservation.lean) use
the same log and the actual callback domain. These are checked information
adapters, rather than an end-to-end probabilistic client law.

[ExclusionPolicyLaw](../Vegas/Pending/ExclusionPolicyLaw.lean) proves that one
automatic completion and the entire native drain preserve the full remaining
graph policy-run law, for every profile and raw sequential native state.
Its accepted-call corollary retains the actual chosen action and guarded result,
including failure, before composing this continuation law. Physical draining
can complete several source instructions; exact one-instruction endpoint laws
must therefore be replaced by the checked continuation composition.
[ReactiveDefaultCompletion](../Vegas/Pending/ReactiveDefaultCompletion.lean)
proves visibility and persistence of native public default and obtains whole
continuation optimality from consistency and local optimality in that region,
on the supplied native response menu. It introduces no wrapper application.

[SourceServiceContinuation](../Vegas/Game/SourceServiceContinuation.lean)
identifies the full remaining graph-run law with the ordinary source
continuation at its decoded position. It uses the same configuration reader,
source residual and source executor, including actual own decisions and the
complete public default history.
[SourceDebtContinuation](../Vegas/Game/SourceDebtContinuation.lean) uses native
transition closure and actual publication provenance to prove fixed exit
utility, integrability and whole-policy indifference for latent source debt
under complete play. Already public default has the stronger continuation
guarantee in [NativeExitContinuation](../Vegas/Game/NativeExitContinuation.lean),
which needs no completion or ordinary utility-range premise.
[SourceDebtObservation](../Vegas/Game/SourceDebtObservation.lean) proves that
own source debt agrees throughout a native information fiber for arbitrary
response menus and initial laws, without a finite-player premise.
[OnePacketOwingOptimality](../Vegas/Game/OnePacketOwingOptimality.lean) combines
that fact with completed-continuation utility to give zero whole-policy and
local-law gain at indebted sites, under any assessment belief.

These laws and the common consistency construction are checked adapters for
the final compiler and equilibrium-preservation theorems. They do not by
themselves close those end-to-end obligations.

## Roster timing through automatic completion

Unconditional ticks in obsolete roster blocks can violate rank-based service
bounds. Consider bindings owned by A, A, A and B, followed by their reveals,
with only each event's owner on its roster and every response silent.

| Point in an unconditionally ticking plan | Clock | Native progress |
| --- | --- | --- |
| First binding expires | 1 | A defaults; A's next two bindings complete automatically. |
| Second binding's obsolete block ends | 3 | B's binding has remained ready since clock 1. |
| Third binding's obsolete block ends | 6 | B has still received no activation. |

B's event has rank 3, reaction bound 3 and deadline duration 4. A native
command fragment in [RosterAutomaticCompletion](../VegasTests/RosterAutomaticCompletion.lean)
checks readiness at clock 1 and overdue readiness at clock 5. This is a checked
operational fragment, rather than a full protocol trace of an alternative scheduler.

The [roster scheduler](../Vegas/Game/ServiceRoster.lean) tags each instruction
with its block's event. It suppresses clock ticks exactly when that event was
already completed at block entry, as recorded in the public environment recall.
It retains every activation, inclusion check, sample and expiry. A block live
at entry keeps its entire tick tail, even if inclusion completes its event.
The fixed command horizon and player response counts therefore stay intact.

[The calendar invariant](../Vegas/Game/ServiceRosterInvariant.lean) bounds the
age of surviving events and records responses made during obsolete blocks.
[The initialized-history theorem](../Vegas/Game/ServiceRosterHistory.lean)
derives that invariant for arbitrary raw player strategies, pending observation
rules and network policies. Its internal state and recall facts come from the
actual initialization and transitions; they are not service assumptions.

[The service capstones](../Vegas/Game/ServiceRosterAsync.lean) give reaction
bound `event.val`, protected inclusion bound zero and terminal completion at
the fixed plan horizon. Each event's actor must occur in its roster, as in
`ActorOpportunities`; deadlines remain `event.val + 1`. The concrete
`SourceServiceSpec.toAsync` builder supplies the generic asynchronous service
contract from these theorems. The compiler, strategic and paper acceptance
gates below remain separate obligations.

## Remaining acceptance obligations

Only checked theorems close these obligations:

1. The source protocol, whole-continuation and perfect-recall correspondence is
   checked under every commitment interface, including automatic instructions.
2. Source-to-graph full-configuration correspondence is checked for arbitrary
   source profiles, initial states and public schedulers, including distributed
   correlated private/public setup laws.
3. Ledger inclusion, expiry and automatic draining have checked finite-path
   graph refinement, initialized-history invariants, immutable candidate/handle
   provenance and signed-emission/certificate soundness. Native focal-call,
   commitment, expiry and automatic-service observation congruence is checked.
   Receipt-failure provenance, activation origins and the native information
   adapters are checked. Port the remaining physical service/client consumers
   to these finite paths and complete default-aware readouts.
4. Reprove the bounded-client law with complete readout using the checked roster
   service contract.
5. Source-to-graph Nash deviation translation is checked. Port the ledger
   client deviation correspondence and sequential consistency/rationality;
   equilibrium-path outcome agreement alone is insufficient.
6. Canonical fixed-exit intended-to-source SE and approximate Nash preservation
   are checked with the declared exit floor on actual intended terminal
   readouts. Finish the intended-to-ledger composition and monetary
   specialization using the same source and target utilities. This does not
   assert preservation of every full-source sequential equilibrium.

The ordinary full build, examples and paper guards remain acceptance gates for
replacing the maintained tower. Targeted source/compiler checks do not close them.

## Scheduler and deviation interface

Two simultaneously ready actions need not commute under absorbing default.
For two bindings owned by one player, omitting the first and then requesting a
successful second binding produces two failures. Executing the successful
binding first retains that success. The actual graph steps and unequal stored
results are checked in [EventGraphDefault](../VegasTests/EventGraphDefault.lean).
[Commutation](../Vegas/EventGraph/Commutation.lean) proves the independent
typed-write and evaluator-footprint facts; these do not assert that arbitrary
requested actions commute through default control. Foreign default
announcements also prevent erasing observations while retaining only hidden
field values.

The compiler-generated order is sequential. Its exact scheduling simulation
uses unchanged strategies and supports every reader of the full terminal
outcome. The checked deviation interface uses that generated order directly,
without generic commutation or foreign-observation erasure. This does not add a
scheduler or runtime assumption. The remaining ledger and sequential strategic
consumers and the acceptance obligations above must still check before the
complete tower is replaced.

## Native completion boundaries

One ledger command can complete its addressed event and automatically complete
several later events. The native relation is a finite supported graph path,
as exposed by `reactiveApplication_graphSteps` in
[ReactiveGraphSteps](../Vegas/Pending/ReactiveGraphSteps.lean). The checked
`round_prefix` result in
[SourceServiceCompletion](../Vegas/Game/SourceServiceCompletion.lean) preserves
the round's starting bound on recorded ready-event views and certifies a
completed prefix at an actual rank greater than or equal to its starting rank.
Activation and response preserve the graph, while a completing environment
command adds no player response. `roundsFrom_ranked` propagates these facts
from initialization through any supported number of complete rounds.

`runUntil_completion_prefix` retains the original prefix when its target is
unfinished, or certifies an actual prefix rank strictly greater than the target
rank once it completes. These are facts about supported executions. A stop at
completion of event `e` need not end at `e.val + 1`.
`CompletionBoundary.stopped` must identify that actual later boundary, with
its future events untouched, rather than a fixed successor rank. Likewise,
`LateStopped` defined by an exact successor prefix is not a monotone
completion test, and `completionValue` cannot read that fixed rank as the
current endpoint after an automatic jump. These consumers require the event's
completion predicate and the actual decoded endpoint. Prefix geometry and
terminal stability can use finite-path induction and
`Config.Step.path_eq_of_terminal`; no new scheduler condition follows from
this change.

Exact probability laws require more than supported-path existence.
`State.drain_bind_runPlan_canonical` and `AcceptanceWitness.reactive_runPlan` in
[ExclusionPolicyLaw](../Vegas/Pending/ExclusionPolicyLaw.lean),
`SourceResidual.runPlan_readout_law` in
[SourceServiceContinuation](../Vegas/Game/SourceServiceContinuation.lean), and
`counted_canonical_source_continuation` in
[OnePacketPrescribedSourceKernel](../Vegas/Game/OnePacketPrescribedSourceKernel.lean)
preserve the full terminal continuation through automatic completion. They
provide the continuation interface for completing the honest-client law;
they do not identify a multi-event endpoint with one source step.

The stopped comparisons count actual player responses, so automatic graph
completions add no response charge.
[SourceTerminalReadout](../Vegas/Game/SourceTerminalReadout.lean) proves
`sourceTerminal_config_stable`: every supported continuation from a completed
source cut retains the complete native configuration. Its readout freeze law
uses that same configuration certificate.
[OnePacketExclusionPayoff](../Vegas/Game/OnePacketExclusionPayoff.lean) derives
`sourceTerminal_exclusionBase_stable` for the actual native fixed-exit payoff
vector, under arbitrary continuation profiles. Traffic and audit deductions are
separate from that observable.

[SourceTerminalComparison](../Vegas/Game/SourceTerminalComparison.lean) uses
those native freeze laws to compare the joint readout and fixed-exit payoff at
source completion with exactly the conditional expected-response budget.
A public default fixes the native payoff even when the terminal reader returns
`none`, so the proof retains the actual joint observable throughout.
[OnePacketHonestTerminalApproximation](../Vegas/Game/OnePacketHonestTerminalApproximation.lean)
preserves the horizon coefficient `min (Fintype.card Player) 1 * horizon` by
mapping the complete-history comparison and using the checked honest joint law.
The intended side uses the full source horizon, `instructionCount + 1`;
complete readouts follow internally. No condition on incomplete source runs or
new service assumption is used. The remaining fixed-successor consumers above
and the final compiler and strategic acceptance gates still require checking.
