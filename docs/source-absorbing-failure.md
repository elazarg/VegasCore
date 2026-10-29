# Absorbing failure as the source language semantics

Absorbing failure changes the source games. A player cannot withhold once and
later resume successful play. The replacement belongs to the ordinary intended
game -> source -> dependency graph -> ledger tower: the intended game restricts
source menus, and each remaining level has one authoritative executor.

This research branch implements absorbing source and graph execution and checks
source-to-graph compilation for every source profile and public scheduler.
The unified ledger application also has checked operational graph refinement.
Probabilistic client correspondence, deviation backtranslation, monetary
interpretation and equilibrium preservation still require ports. The full branch is not a
verified replacement for the maintained tower. The paper and its pins are unchanged.

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
authentic-binding criterion. Intended-strategy consumers remain acceptance
obligations.

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
deduct for forbidden traffic after default. These definitions and their
settlement projection require an explicit port in the strategic consumers.

No independence, service, coverage, finiteness or funding premise is added.
The preservation theorem's premises, including the exit floor, remain proof
obligations for its port. Restricting surviving players' valuations to ignore
public default history would be an additional assumption and is not part of
this design.

The ambient public-record type admits impossible histories. Utility-range ports
must use their actual execution domain or a bounded extension outside it;
boundedness on extra impossible records must not become a hidden new premise.

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
prefix. Arbitrary graph-deviation backtranslation remains a separate port.

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
reads default monotonicity directly from graph configurations. Exact
first-default/receipt provenance remains a separate constructor proof.
[ReactiveSampleLikelihood](../Vegas/Pending/ReactiveSampleLikelihood.lean)
retains the actual physical chance law through atomic draining, while
[ReactiveServiceProgress](../Vegas/Pending/ReactiveServiceProgress.lean)
preserves clocks, completed events and unfinished-event deadlines through
arbitrary responses and environment operations.

These are operational support/refinement laws; they do not establish the
probabilistic client/compiler law or equilibrium preservation.

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
   Port receipt-failure provenance and the remaining physical chance/service
   observation adapters to the single application.
4. Reprove the bounded-client law with complete readout and the service contract.
5. Port Nash deviation translation and sequential consistency/rationality;
   equilibrium-path outcome agreement alone is insufficient.
6. Recheck intended-SE preservation only after the source and target utilities
   and transfers agree. This does not assert preservation of every full-source
   sequential equilibrium.

The ordinary full build, examples and paper guards remain acceptance gates for
replacing the maintained tower. Targeted source/compiler checks do not close them.

## Scheduler and deviation proof boundary

Two simultaneously ready actions need not commute under absorbing default.
For two bindings owned by one player, omitting the first and then requesting a
successful second binding produces two failures. Executing the successful
binding first retains that success. The actual graph steps and unequal stored
results are checked in [EventGraphDefault](../VegasTests/EventGraphDefault.lean).
Thus the unrestricted local-commutation statement in
[Commutation](../Vegas/EventGraph/Commutation.lean) is false for this semantics.
Foreign default announcements also invalidate observation-erasure arguments
that retain only hidden field values.

The compiler-generated order is sequential and already has an exact
scheduler-independence theorem. The remaining deviation/scheduler interface
must use that generated order instead of the generic commutation and foreign
normalization argument. The full replacement is unproved until that interface,
its strategic consumers and the other acceptance obligations above check.
No additional scheduler or runtime assumption is authorized by this boundary.
