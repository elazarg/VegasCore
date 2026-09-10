# Timeout resolution as a compilation mechanism

Timeout resolution belongs to the runtime implementation of a program's
specified nonresponse consequences. A deadline makes a resolution action
eligible; executing that action must implement those consequences. Passage of
time alone does not execute a program.

This document fixes the component boundaries and the next compiler obligations.
The checked scope includes a dependency gate, atomic message inclusion,
a timed final-disclosure instance of the native sealed application, and
source-legal public-choice and binding timeout code in generated application images. It is
not a source-to-timed-runtime strategic compiler theorem. Ethereum grounds the
design through the adjacent Kotlin compiler's generated contracts. Other
runtimes can supply the same components where their semantics fit.

## Operational components

### Public fallback certificates

`SourceDecisionSite.PublicFallback` supplies a typed expression over the public
source context and proves that its value satisfies the original decision guard
at every source environment. The compiler retains that expression and its
field reads as `EventExpr` code. For an adjacent public choice,
`PublicChoiceSite.install` attaches the expression and deadline to the existing
generated instruction. It changes neither the source language nor the source
accounting plan.

The annotation designates a **source-legal backend resolution**. Nonemptiness
of a guard alone does not select a default, and the certificate does not assert
that the owner's original policy chooses this value. Connecting a surface
language's declared nonresponse handler to this annotation remains a frontend
obligation. A constant quit value is a special case; a resolution can also
depend on public source data.

The raw application alphabet includes `expireChoice address`. Any principal
can submit this message. Inclusion requires the endpoint to remain unresolved,
its prerequisites to be complete, and its strict public deadline to have
passed. The handler reads and evaluates the emitted expression, defensively
checks the ordinary source guard, and writes the same two allocated fields and
completion flags as a successful ordinary public choice. It does not forge an
owner-authored message, add a command to the owner's history, or modify private
commitment preparation. An already completed endpoint rejects expiry; a late
ordinary choice remains admissible until a competing expiry is actually
included.

Read availability and legality at a represented source checkpoint follow from
the public-expression compiler and the source certificate. Acceptance therefore
has the original adjacent commit/reveal source continuation with the annotated
value. This is a source-support claim, not equality with the original behavioral
profile. It also does not produce an expiry transaction or guarantee inclusion.
Binding defaults use the same source-decision certificate and a distinct public
disposition, described below; the public-choice mechanism does not create a
commitment handle or an accepted opening witness.

Optional timeout code retains the generated image's completed-run source
support theorem under arbitrary native actions and randomized policies. It
also retains the exact reference-profile outcome law: the lifted source
policies never submit the new expiry request. The latter follows from a
runtime-general handler-extension theorem comparing complete executions with
the same state, observation, action, and history types. Neither result provides
a source policy simulating an arbitrary runtime deviation.

### Binding expiry and public dispositions

`SourceDecisionSite.PublicFallback` retains a public source expression and a
proof that it is legal at the original commitment in every source environment.
Its compiled expression reads only public fields. At an exact source-prefix
checkpoint, `PublicFallback.expiry_include_source_coupling` proves that actual
inclusion of a pending `expireBinding` packet performs the original source
commit with the evaluated value. It derives unfinishedness, prerequisite
completion, absence of an accepted disposition, and executable read availability
from the checkpoint and native refinement. Its explicit service premises are a
pending packet and a passed strict deadline. It retains that packet in the ledger
with its receipt and does not change local sent or inbox histories. It assumes
neither the owner's private preparation nor its chosen policy.

`PublicFallback.installBindingTimeout` attaches this code at the existing
generated binding address. The complete-image regression privately prepares
true and proves that a non-owner's actual expiry packet instead advances the
original source commitment to its designated false fallback. Additional tests
cover the strict deadline boundary, missing prerequisites, both orders of the
binding/expiry race, replay, and absence of timeout code. A deadline does not
disable ordinary binding: the first successful inclusion wins.

The binding and public-choice decoration passes commute. Each retains graph
refinement under arbitrary native actions and randomized policies. The combined
artifact retains the source reference-profile outcome law because lifted
source policies submit neither kind of expiry packet. This no-expiry reference
law does not establish a resolving service or arbitrary-deviation simulation.

`BindingDisposition` is runtime-general: it records either an opaque handle or
a public default value. The application stores this sum in its public memory.
The private preparation table and acceptance-time snapshots remain separate.
Refinement relates a public default directly to the typed graph field; opaque
bindings retain their existing snapshot condition, including absent or
ill-typed snapshots. Local readout takes a public default from the disposition,
not from the owner's registration cache. A different cached value does not
change that readout. The fallback value is stored once, in the disposition;
the public source-field store remains unchanged by this update.

`ConditionalPublication.resolveDisposition?` supplies the runtime-general
publication classifier for these alternatives. An opaque binding uses the
commitment verifier. A public default admits an owner-authored cleartext
request exactly when its value matches the recorded default and satisfies the
continuation guard. It rejects commitment-opening requests and does not
consult the private verifier. Owner decline and permissionless overdue expiry
remain available. Shared-runtime tests include actual submission, delivery,
inclusion, retained rejected traffic, and rejection after completion.
Generated conditional instructions use this classifier after checking the
accepted disposition's dynamic type. Their lifted source policy selects a
strict opening or cleartext codec from that same public disposition. The two
codecs have distinct accepted packet forms; future-cache freshness quantifies
over both alternatives. A public default overrides a conflicting private
registration when reconstructing the source decision's observations.

`ConditionalPublicationSite.include_source_coupling` proves that actual
inclusion of either disposition's legal voluntary request continues the exact
source commit/reveal pair. Default/source equality is derived from state
refinement, not supplied as a separate value assumption. The corresponding
expiry theorem implements the source decline for either disposition.
`imagePolicy_first_submission_source_law` identifies the unchanged source
decision's law under the selected codec. Generated three-node regressions
exercise a private preparation of `true`, a public fallback of `false`, and
the resulting policy submission of cleartext `false` through the shared runner.

These local laws do not establish a whole-program law after expiry. The
conditional phase used in the serial-reference induction still assumes an
opaque binding. Extending phase composition to public defaults, preserving
cache freshness across a resolving service, and comparing arbitrary deviations
remain separate obligations. A public-computable fallback value does not make
the occurrence or timing of fallback independent of private player behavior.

The public-expression certificate has a genuine eligibility condition. If two
source environments have identical public information but disjoint legal
choice sets, no deterministic public-expression default can be legal in both.
`PublicFallback.not_nonempty_of_disjoint_legal` checks this statement, with a
private-Boolean equality regression. This concerns the universal certificate,
not an impossibility for every runtime or every reachable-state restriction.
It changes neither source syntax nor well-formedness.

### Runtime services

| Component | Meaning and present scope |
| --- | --- |
| Clock | A reading supplied by the enclosing runtime. The gate uses natural-number units; it neither advances time nor publishes ticks. |
| Deadline policy | A predicate deciding whether a missing obligation is overdue. The two implemented instances use a mutable activity origin or immutable deadlines. |
| Dependency gate | Ordered checks stage completion and principal-exclusion effects. Exclusion discharges every dependency of that principal, not just the overdue obligation. |
| Application transaction | A handler returns an accepted next state or rejection. Rejection retains the initial application state. |
| Message inclusion | Publish a preexisting pending message and then run the application transaction. Rejection does not remove that publication or earlier observations. |
| Resolution behavior | The program-specific continuation, entitlement, or settlement effected by a successful resolution. No general compiler correspondence for it is established here. |

These are small functions and parameters, not a universal runtime configuration
language. Atomic application execution is a particular supported boundary;
a non-atomic runtime needs a different execution model and comparison. Clock
units, clock visibility, permitted advances, and inclusion guarantees belong
to the enclosing runtime, not to the gate's arithmetic.

`Interaction/DependencyGate.lean` stores completed action identities,
excluded principals, and the last activity reading. A call checks actor
eligibility and action freshness, stages action completion, checks its ordered
dependencies, and evaluates a body-acceptance predicate. Success records the
current activity reading. Failure returns no staged state to commit.

The compiled entry point must supply the authenticated actor, recorded action
identity, and dependency list. These are fixed entry-point metadata, not
caller-chosen labels. The raw gate API does not enforce this restriction or
authenticate its arguments. Actor and action owner are
separate because registration can execute under one role while completing an
action for another. An instance must establish their actual relationship.
The body predicate captures rejection after staged checks; it does not model
other application writes, reentrancy, transfers, or resource exhaustion.

`Interaction/TransactionalInclusion.lean` supplies the separate atomic
boundary over `MessagePool.includePending`. A handler returns `some next` or
`none`; the result records acceptance, rejection, or a missing message id.
An included rejected message remains on the public ledger. Sent histories and
recipient inboxes are unchanged by inclusion, so previously delivered content
remains available. This component does not yet specify a policy observation
interface for receipts, fees, account nonces, or finality.

## Concrete grounding: the call-entry activity snapshot

The adjacent compiler's
[Solidity emitter](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/main/kotlin/vegas/backend/evm/Solidity.kt)
and
[Vyper emitter](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/main/kotlin/vegas/backend/evm/Vyper.kt)
use a shared `lastTs` and a timeout window. The concrete clock is
`block.timestamp`, not block height. A missing dependency is overdue when
`origin + TIMEOUT < block.timestamp`, where `origin` is one snapshot of
`lastTs` taken before the call's dependency checks. Each overdue check marks
the dependency owner as bailed and resets `lastTs` immediately, but every
check in that call uses the same snapshot. Each successful action also resets
`lastTs`. These writes remain visible to the action body. Per-action
timestamps are recorded but do not determine expiry.

Dependency checks precede the game-action body. In Solidity they follow the
authorization and action-completion modifier preludes. Failure reverts staged
application-state writes as well as the body's writes. See the
[modifier semantics](https://docs.solidity.org/en/latest/contracts.html#function-modifiers)
and [state-reverting exceptions](https://docs.soliditylang.org/en/latest/control-structures.html#error-handling-assert-require-revert-and-exceptions).
Such a revert does not erase the included transaction. Fees and other
transaction-level effects need their own model; [EIP-140](https://eips.ethereum.org/EIPS/eip-140)
does not make rejected execution free.

There is also a staging difference between emitters. The Solidity `action`
modifier marks the current action completed before dependency checks; the
Vyper emitter marks it after the body. The gate's `call` follows the Solidity
order. Both use a call-entry snapshot for expiry while retaining activity
writes during dependency checks. Equating their
complete gate behavior would additionally require that the current action
is absent from its dependencies and that the body does not observe or exploit
the staging difference. No such emitter-equivalence theorem is supplied.

The [deployed Solidity regression](https://github.com/elazarg/vegas/blob/47734f73e3ad22a550bec299b0bfce1c95105316/src/test/kotlin/vegas/eth/tests/EthDependencySnapshotTest.kt)
checks that one overdue call persists both missing owners' exclusions, action
completion, and its activity timestamp. A call exactly at the deadline
rejects and retains neither staged completion nor exclusion. Vyper has
generated-code/golden coverage, not a deployment test. These tests are
implementation evidence, not a checked compiler-to-VM simulation.

## Re-reading a mutable activity origin

`slidingExpiry` instead reads the updated activity origin on every dependency
check. This policy has a within-call interference problem. Suppose a call
checks two missing dependencies of distinct, initially active owners:

1. If the shared deadline has not passed, the first check rejects.
2. If it has passed, the first check stages exclusion and sets `lastTs` to
   the current reading.
3. The second check now compares the current reading with itself plus the
   timeout window, so it cannot expire the second owner. It rejects.
4. The application transaction discards the first exclusion as well.

Waiting longer cannot make this same batch succeed from unchanged state.
Other calls may change that state; this is not a theorem that every such
contract is permanently stuck. Successful unrelated actions can also extend
the shared deadline, a distinct policy choice exercised by the tests.

`Interaction/DependencyGateLaws.lean` proves this obstruction for the abstract
gate. It distinguishes re-reading staged state from the emitters' call-entry
snapshot. The abstraction uses unbounded naturals and omits address checks,
other contract storage, finite-word overflow, gas, and external execution.
Connecting a generated handler to the gate remains a separate refinement
obligation.

## Immutable deadlines

`fixedExpiry` reads an immutable deadline for each dependency. A constant
deadline represents the call-entry snapshot used by the emitters. This
relationship is by inspection; there is no checked emitter correspondence.
An independently fixed deadline for each obligation is a separate policy.

The gate laws prove that checking succeeds when each dependency is already
completed, belongs to an initially excluded principal, or has passed its
immutable deadline. This is a check-level progress result, conditional on
that readiness premise. The enclosing call can still fail its admission or
body checks. It also still needs someone to submit it and a runtime that
includes it.

When every initially missing requested dependency is overdue, the exact result
also retains the completed set, excludes precisely the initial exclusions
plus the owners of those missing dependencies, and records the current clock
reading if any such dependency exists (otherwise retaining the initial reading).

Snapshotting the shared origin removes within-call timer interference;
it does not establish per-obligation deadlines or prevent other successful
calls from postponing resolution. A per-obligation deadline map supports the
latter policy. Both retain the gate's principal-wide exclusion rule. Changing
that rule is a separate operational choice with different strategic effects.

`InteractionTests/TimeoutGate.lean` checks the strict deadline boundary,
shared-timer failure, immutable-deadline success, body rejection, activity
reset, and principal-wide exclusion. Its actual submit/deliver/include
executions distinguish rolled-back application state from retained public
messages and recipient observations. These are runtime-component tests, not
compiled source fixtures or a source-equilibrium result.

## Connecting resolution to source meaning

### The integrated final-expiration instance

`Interaction/SealedTimeout.lean` attaches one named opening checkpoint and an
immutable absolute deadline to an existing `SealedProgram`. Ordinary traffic
uses `SealedProgram.validateMessage?`, the same pool-independent validator
used by the untimed application. All messages, including failed expiration
and opening calls, pass through atomic pool inclusion and produce public
success/rejection receipts. The caller cannot choose the checkpoint metadata.
Expiration is permissionless but must pass the checkpoint's original public
opening-readiness checks and the strict deadline test.

The chosen policy accepts a late valid opening until expiration has actually
been included. Expiration first stops subsequent protocol-event acceptance;
opening first disables expiration while allowing the program to continue.
Expiration preserves the service table and original public events. Further
network activity and registration of new service bindings remain possible;
occupied bindings remain unchanged. This policy
does not synthesize an opened value, pay a refund, discharge other graph
dependencies, or implement role-specific abandonment while other players
continue. Those are application/compiler responsibilities, not consequences
of the word timeout. This instance is a final-failure policy, distinct from
the adjacent emitter's principal-exclusion dependency gate.

The environment advances an explicitly public monotone natural-number clock.
Neither advancement nor exhausting a finite analysis horizon resolves the
checkpoint. The native policy game in `Interaction/SealedTimeoutPolicies.lean`
allows local-history-dependent register, submit, replay, and wait choices;
the environment adaptively advances the clock, delivers, includes, or waits.
It sees wire state and public application data, but not the hidden commitment
table. Polling uses a fixed finite invocation list and does not imply timely
inclusion. The policy-law module proves every supported result has its actual
native execution witness and preserves already occupied service bindings.

`VegasTests/PendingTimeout.lean` instantiates this extension with the program
emitted from `PendingSource`. Its race executions start with actual native
registration, commitment submission, and inclusion. They compare opening and
expiration orders after delivery, retaining the earlier inbox content even
when the opening is rejected. This connects the runtime experiment to the
actual compiled prefix; it does not identify expiration with that source's
terminal nullable value.

`WFProgram.sealed_timeout_run_source` proves that every finite raw timed run
decodes to a reachable compiled graph prefix. `sealed_timeout_policy_source`
lifts this result to every supported outcome of the native policy game.
When the decoded graph prefix is terminal, both reconstruct a written-order
source execution with matching terminal bindings and payout evaluation.
The decoder omits traffic, receipts, clock, and resolution: these are
support-level execution theorems, not observation or strategy equivalences.
Expiration may leave an incomplete graph prefix. A completed disclosure
checkpoint likewise need not complete the rest of the program.
`VegasTests/PendingTimeoutSource.lean` instantiates terminal reconstruction for
all nullable input pairs and both commitment inclusion orders after a real
clock advance past the deadline. With no expiration included, both openings
remain valid and the complete decoded graph reaches its source outcome.

`VegasTests/PendingTimeoutPolicies.lean` holds the players and invocation
schedule fixed while two environment policies choose opposite inclusion
orders. Both deliver the valid opening; their exact resolution laws are
respectively completion and expiration. This demonstrates an inclusion-order
effect even when the owner has submitted its bound value.

`Interaction/SealedTimeoutHiding.lean` relates paired raw executions whose
service contents differ only in a protected principal's occupied values. It
preserves equality of the declared views, including clock, resolution, and
success/rejection receipts, before that principal sends an opening. The
retained carrier must already exclude its opening messages and the common
trace must contain no further commands from that principal. This is a raw
noninterference theorem; lifting it to adaptive policy laws and proving an
reference strategy's disclosure discipline are additional obligations.

### Source correspondence still required

The current minimal source makes `reveal` publish the already sealed value.
A nullable choice of `none` is chosen at its source decision; it does not
authorize replacing a previously chosen `some value` after withholding a
later opening. The source and its well-formedness discipline remain unchanged.

The adjacent backend implements absence through completion flags and
principal exclusion. Bailing an owner neither fills the missing field nor
marks that field completed. Relating this to source nonresponse handlers
requires the handler elaboration and downstream field accesses to respect
the intended optionality. The gate alone has no field-value or payoff semantics.

The existing selective-publication witness also retains its force: a deadline
can settle withheld disclosure, but does not make an informed decision after
seeing an opponent's opening identical to an earlier nullable choice. A
source/backend pair needs either an actual corresponding source decision or
a proved weaker comparison, for example an incentive condition bounding
informed quitting. Hiding and binding do not supply that comparison by
themselves. See [runtime models](runtime-models.md) and the
[quitting compilation contract](quitting-compilation-contract.md).

## Next integration gate

### Initial defaults and privately prepared commitments

Private commitment preparation, public submission, and ledger acceptance are
separate operations. An owner can prepare a value and withhold its submission.
A source-designated initial default therefore cannot be implemented by
overwriting that private commitment, treating it as submitted, or making a
private preparation step publish an application decision.

The disclosure application records the accepted source binding as either an
owner-submitted opaque commitment or an explicit public default. An included
permissionless initial expiration chooses the latter without modifying private
storage or forging an owner-authored message. Subsequent validation uses the
accepted alternative, not an unsubmitted commitment the owner prepared earlier.
The generic publication kernel takes its opening validator independently of
the source guard: verification of a captured commitment and comparison with a
public default are separate implementations of that interface.

The initial deadline is the configured window from clock-zero initialization.
Early calls and calls after a binding is accepted reject; a late ordinary
binding may win until expiration is included. The source default is `false`,
the existing initial action used by the finite sealed-offer interface. It is
not a new initial quit branch or the richer frontend's persistent abandonment.
The checked full native execution contains no owner action: the responder's
calls expire initial selection, expire disclosure after source chance, and
respond. Its source execution uses that exact initial default. Separate checks
retain private preparation and reject attempts to bind or disclose a different
prepared value after the default. The pure owner controller reconstructs its
continuation choice from the accepted disposition rather than its unsubmitted
private intention; a local recovery theorem checks that behavior even with an
empty local history, once the declared public reads are available. The native
handler accepts that public value without private preparation. The responder
controller submits initial expiration when its public deadline is overdue.
The initialized slotted-service results below establish opportunity and
settlement; the separate honest inclusion script does not take the default branch.

The response default has an actual permissionless entry point. Successful
publication arms a response window, and an included overdue call selects the
source's rejection action `false`. A repeated publication cannot reset that
window; early calls and calls after response completion reject. Clock advance
does not execute the call. The native owner-disclosure/response-expiration
execution has the expected chance law and public receipts without any responder
action, and the handler has a written-source support theorem for arbitrary
public payouts. The pure owner controller submits response expiration after
observing its deadline. The initialized owner-side service bound below covers
arbitrary responder policies.
Deadlines enable the fallback; a normal response may win until expiration is included.

There is a separate commitment-validity boundary. The disclosure application
accepts an opaque handle without testing whether it has an opening, and
captures an immutable private verifier at inclusion. Acceptance and subsequent
marker/chance readiness reveal no validity result. Later preparation cannot
repair an accepted unopenable binding: every native continuation that resolves
its publication selects decline. The checked hostile execution delivers and
rejects a late opening before an included expiration continues to the responder;
the failed message and its rejection receipt remain observable.

The snapshot point is inclusion, not creation of a cryptographic packet. This
ideal instance still permits preparation while a handle is pending. Its
realization must relate that freedom, actual packet binding, and native
observations; immutable accepted state alone does not prove the relation.
An unopenable snapshot's source-support witness is `false`, with decline at
publication. It is a legal source reconstruction, not an operational initial
default, a settlement guarantee, or a strategic backtranslation.

Public fallback and failure calls add observations. Their source-value
legality does not prove strategic preservation, but their visibility alone
does not refute unilateral Nash preservation either. Compiled opponents may
ignore auxiliary traffic, and a deviator may already know its own fallback.
The comparison must establish the actual observation and deviation law. A
claim of impossibility needs a witness for that claim and policy class.

### Whole-program comparison

The conditional-publication component supplies a local source-resolution
bridge without adopting the final-expiration instance's global stop policy.
`ConditionalPublicationSite` combines the paired choice/reveal occurrence
with a guard certificate identifying decline or opening of a retained binding.
Source accounting can supply that certificate; later copies can supply it
independently of the original binding's discharge. `ConditionalResolution` proves accepted
results perform legal source steps and every legal source choice has a
canonical accepted request, under the appropriate soundness/completeness
directions of the application validator. `ConditionalExecution` proves the
accepted effect follows the two actual compiled graph kernels. The compiler
must also maintain source/store and original-handle correspondence.

This component distinguishes commitment verification from program legality.
An opening can verify correctly but be forbidden by a continuation guard after
earlier quitting. The application supplies that check; source well-formedness
does not force all bound openings to remain legal. Publication also retains
previously delivered payloads, including an opening overtaken by expiration.
These facts do not yet supply a whole-program timeout implementation or a
strategic comparison.

The shared `DisclosureApplication` instance includes binding, forced marker,
public chance, publication, and the responder's continuation. Decline and
included expiration resolve publication without terminating that continuation.
Its publication deadline is armed by the public sample. Arbitrary supported
policy runs have checked source-prefix support; specified pure controllers and
an inclusion script have the actual AST's complete outcome law from empty.
Every nontrivial source decision in this finite instance has an explicit
nonresponse handler. The forced marker and chance are environment-triggered
fixed application work. Pure timeout-driving controllers and an instantiated
slotted inclusion service are available. Players can react to pending delivery,
and reserved capacity drains the queue even under arbitrary player policies.
The service clock advances once per complete cycle. Stable pending resolvers
also have application-progress proofs for initial binding, ordinary response,
and all three expiration calls. These phase results start with an already
pending, ready request. Initialized settlement with either player unchanged is
also checked below. With a positive window, the unchanged owner's source
choices and the unchanged responder's selected reply are preserved.
The instance does not yet provide the whole-program timeout contract below.

#### Service settlement guarantees and remaining targets

For the slotted service, number cycles from one. From clock-zero initialization,
`DisclosureServiceClock.service_schedule_clock` gives clock `c` after `c`
complete cycles, independently of player policies and admitted inclusion choices.
The service capacity theorem gives an empty queue at each cycle boundary.
The initial milestone is also checked: with the unchanged responder, every
owner policy and admitted selector reaches initial binding, marker, and public
signal by cycle `w + 2` (`DisclosureInitialService.responder_initial_by_cycle`).
This result starts at game initialization and covers earlier one-shot timeout
submissions. It holds even at `w = 0`; preserving an unchanged player's chosen
value requires the stronger timely-opportunity argument below.
`DisclosureServiceTimeOrigins.responder_signal_overdue_by_cycle` proves the
signal deadline is overdue by `2*w + 2`: the sampling origin precedes the clock
at its cycle boundary and survives all continuations. The exact publication
request history and the next responder opportunity then give publication by
`2*w + 3`. `DisclosureServiceSettlement.responder_settles_by_cycle` supplies the
last response cycle and proves that a native outcome exists by `2*w + 4`, from
initialization and against arbitrary owner policies and admitted selectors.
No positive-window assumption is required for this termination result.

The complete-cycle bounds and their status are:

| Policies | Settlement bound | Status |
| --- | --- | --- |
| Both compiled pure controllers | 3 | Proof target |
| Arbitrary owner, unchanged responder | `2*w + 4` | Checked for all `w` |
| Unchanged owner, arbitrary responder | `w + 3` | Checked for `w >= 1` |

`DisclosureOwnerSettlement.owner_settles_by_cycle` proves the owner-side bound.
Its first two cycles also preserve the owner's secret and selected optional
publication (`owner_choice_by_two_cycles`); `owner_choices_preserved` carries
those exact values through all subsequent supported service cycles. Registration
precedes the actual binding submission, the initial deadline is not overdue
during first-cycle inclusion, and the publication deadline is not overdue during
second-cycle inclusion when `w >= 1`. Pool-wide provenance proves that any
owner-authored publication packet is the one selected by the unchanged policy.
It covers pending, ledger, delivered, and sent copies, so the argument includes
replay rather than excluding it by a scheduler restriction.

`DisclosureResponderSettlement.responder_choice_preserved` proves exact reply
preservation at every complete-cycle boundary for `w >= 1`. The invariant says
that a resolved response is the controller's selected reply, and an unresolved
published response has a fresh window: `clock <= responseAt + 1`. Before
publication, full-pool provenance excludes any responder-authored response
packet. If publication first occurs during inclusion, its window is armed at
that phase's clock, so expiration cannot resolve the response in that phase.
The next service cycle submits and includes the selected reply before its
deadline is overdue. Arbitrary owner traffic, stale expiration requests, and
replay are included in the argument. `responder_settles_to_choice` combines
this preservation with the `2*w + 4` completion bound.

These guarantees are for the concrete deterministic source controllers against
arbitrary opposing policies under the specified service. They complete the
example's operational integration gate. Generation of the application and
controllers, randomized profile laws, and deviation simulation remain the
general compiler obligations; the support-level results do not establish them.

The one-cycle lag between observing resolution and acting explains the window
condition. With `w = 0`, an expiration can be eligible in the same inclusion
phase as an unchanged player's first normal publication or response. Ordering
expiration first can select the default. `DisclosureServiceRace` checks the
local ordering effect: an actual native run reaches a state with a valid opening
and an overdue expiration pending. Opening-first accepts the chosen value;
an admitted payload-sensitive selector instead includes expiration first in
the actual eight-slot inclusion phase and fixes publication to decline. This
is a reachable native prelude followed by a serviced phase, not a whole-run
compiled-profile counterexample. The positive proof must exclude such a race
at an unchanged player's first opportunity without restricting the deviator's
raw commands.

Delivery and inclusion guarantees are environment assumptions. Eventual
inclusion alone does not put a player's response ahead of an effective timeout.
Preservation of that player's source choice needs a deadline-relative
observation and inclusion opportunity; termination also needs clock progress
and submission of a resolver. These are separate premises. The concrete slotted
service supplies bounded opportunities, while the controller proofs establish
that unchanged players use them. Its service guarantee applies under player
deviations and does not assume that a deviating player submits a request.

`Interaction/MessageApplicationProgress.lean` proves the inclusion-phase
invariant: the concrete resolver envelope remains pending, or its application
milestone already holds. Its local premises require milestone persistence,
readiness preserved up to resolution, and resolution when that envelope is
selected. Sufficient reserved inclusion capacity then implies the milestone,
including for randomized selectors that inspect payloads. The result uses the
existing native policy runner and permits arbitrary competing pending messages.
It does not permit new arrivals during the reserved inclusion phase.

`DisclosureServiceResolution` and `DisclosureResponseResolution` discharge
those local premises for canonical initial binding, ordinary response, and
overdue initial, publication, and response expiration. These application
instances start from a pending request with the required phase invariant and
deadline. A competing call may establish the milestone first; the conclusion
therefore asserts resolution, not preservation of the request's chosen value.
Ledger membership alone would not suffice: it neither implies acceptance nor
distinguishes earlier publication from a pending replay.
`Interaction/MessageApplicationSubmission.lean` connects an exact submission
history entry to a pending-or-resolved state under local preservation and
acceptance premises. Its emission condition is required on invariant application
states. The initial-expiration, publication-expiration, and ordinary-response
instances discharge these premises from initialization. The shared
`MessageApplicationPolicyHistory` theorem proves that recorded commands satisfy
the controller's view/command law. Its responder instance connects the broader
one-shot flags to exact publication-expiration and response requests. These
facts discharge the history obligations of the initialized settlement theorem;
they do not imply that the responder's chosen value wins a timeout race.
The corresponding owner-response-expiration instance discharges the owner-side
history obligation. Exact choice preservation additionally uses the timely
inclusion and full-pool provenance proofs described above.

#### Deviation-law proof targets

The intended comparison fixes the adaptive inclusion selector, assumes the
slotted service and `w >= 1`, and uses a sufficiently long schedule (the proposed
uniform bound is `2*w + 4` cycles). Neither an arbitrary environment nor the
inclusion predicate alone supplies the required opportunity guarantees.
The first source endpoint may use pure compiled policies with behavioral source
replacements, but draft-level coverage requires randomized source profiles too.
The generic `ApplicationImage` has conditional-publication expiration and
optional source-certified binding and public-choice expiry. Its serial reference
service does not produce expiry traffic, so these endpoints alone do not
totalize refusal. Generated conditional instructions and their local policy laws
support public defaults; whole-plan continuation under a resolving service is
still required. The concrete `DisclosureState` fixture has
separate initial-binding and response fallbacks; its resolution-service results
must not be generalized to every emitted image without the corresponding
continuation and service proofs.

After settlement and exact unchanged-player choices, reconstruct laws rather
than choosing an independent source witness for each supported outcome:

- For an owner replacement, factor the decoded law into an initial binding
  distribution, independent source chance, an opening kernel conditional on
  binding and signal, and the unchanged source response kernel. Legal openings
  are decline or the retained binding. Unopenable accepted commitments use the
  existing decoder's `false` witness and permit only decline.
- For a responder replacement, retain the unchanged owner's initial and
  disclosure laws and reconstruct a response kernel depending on signal and
  actual publication. Correlation with a randomized hidden binding is not by
  itself a counterexample to equality of the public terminal decoder: if the
  binding remains sealed, that correlation can disappear under public
  projection. Conditional independence from the binding is required for a
  richer latent or full-environment law, or when a later public result exposes
  the same binding. A fixed-secret example cannot establish that obligation.

A candidate public-law witness would use two conditional publications of one
randomized binding. The first opening packet is delivered to the responder, but
expiration wins and records decline; the responder conditions its reply on the
packet's value; a later source-certified copy publishes that same binding. This
requires the later copy's guard to permit opening after the earlier decline.
The generic `conditionalCopy` plan constructor can carry such an independently
certified guard and account for the new copy, but no checked source instance or
whole-run law currently realizes this witness. In particular, the existing
persistent-quitting fixture forces every later copy to decline after the first
decline, so it is not this example.

A service that lets expiration defeat an unchanged owner's selected opening
already fails full compiled-profile source preservation at the first
publication. The responder's source-unavailable observation is a further
public-law issue only if it affects a later compared result, such as the
separately certified publication above. It is not by itself a responder-only
counterexample under a premise that already preserves the unchanged owner's
source choice. A positive comparison must exclude or explicitly compare an
opening-visible-before-expiry race when that observation survives into its
claimed outcome or payoff. It need not forbid every such delivery when the
chosen public projection erases the observation and all of its downstream
effects.

Finite-law disintegration can construct these kernels once their factorization
properties are proved. Zero-mass observations need legal fallback policies.
The candidate translation is profile-local and environment-dependent, not a
uniform translator for all opponent profiles. Runtime traffic and receipts
remain observations of the actual policies but are not equated with source
terminal environments. Randomized controllers must retain their own sampled
initial choice and sample each later source decision once; extra polling must
not create resampling opportunities for compiled play. These obligations are
not discharged by the scripted honest law or by source-support correspondence.

1. Relate the emitted resolution entry point and call-entry deadline policy
   to the gate and complete handler semantics. Treat source handler
   elaboration as an explicit compiler obligation.
2. Integrate conditional publication into the chosen source's complete public
   application and controller, including its actual continuation and
   observations. Do not reinterpret the final-expiration instance's global
   failure as that continuation. Preserve the original bound value and both
   calls' observable success or rejection throughout.
3. Prove that a supported source program's resolution executes its prescribed
   continuation or settlement while retaining bound values and observations.
   Eligibility for this backend is distinct from source well-formedness.
4. Establish the relevant strategic comparison against the same opponent
   and environment policies. State service assumptions under deviations,
   distinguish voluntary withholding from censorship, and retain unresolved
   outcomes when progress is not guaranteed.

The next gate is met by an actual compiler instance and a checked comparison
or precise obstruction in that integrated game, not by these component laws
alone. Later clock, cryptographic, transaction, and VM realizations refine
this path under named assumptions. Runtime-general interfaces remain outside
Vegas lowering and outside the Ethereum-specific implementation.
