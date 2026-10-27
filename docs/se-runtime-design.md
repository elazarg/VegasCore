# Runtime definitions for sequential-equilibrium preservation

## Objective and scope

Use the existing source compiler, message execution engine and game-theory
foundation to describe two concrete implementations: the existing sequential
phase runtime and the proposed concurrent runtime with fixed windows and direct
ledger audit. Share their actual common operations. Keep differences explicit
where they affect execution, information or legal deviations.

The design should allow stronger preservation results for the sequential
implementation without importing assumptions needed only by the concurrent
proof. It should also localize changes to deadlines, publication service and
audit policy. It cannot promise that a change in information or available
actions leaves an SE proof intact.

This is an implementation design, not a checked theorem or a replacement for
the [fixed preservation target](se-async-checklist.md). The
[broadcast derivation](se-broadcast-preservation-derivation.md) specifies the
particular concurrent construction to formalize. Its additional service and
observation assumptions are not universal blockchain semantics.

## Existing foundation

| Owner | Reuse | Specific work still required |
| --- | --- | --- |
| [Event graph compiler](../Vegas/Compile/EventGraphCompiler.lean) and [execution modes](../Vegas/EventGraph/Sequential.lean) | Typed source nodes, dependencies, inputs, samples and payoffs; sequential and concurrent orders on the same nodes. | Relate any physical batching to the same source transitions, preserving component publication and sample order. Do not define another source language. |
| [Message network](../Interaction/MessageNetwork.lean) | Envelope identities, submission, pending pool, ledger and partial reception of whole packets. | Distinguish canonical authenticated bodies from envelope occurrences where the new service needs that distinction. |
| [Reactive application](../Interaction/ReactiveApplication.lean), [protocol](../Interaction/ReactiveProtocol.lean) and [response menus](../Interaction/ReactiveResponseMenu.lean) | Actual execution, player recall, scheduler commands, legal actions, induced information model and bounded histories. | Supply concrete application, raw menu and scheduler instances; justify any batch or microstep adaptation. |
| [Scheduler implementation](../Interaction/ReactiveSchedulerImplementation.lean) | Private scheduler memory and its behavioral realization. | Construct independent body jobs with the required publication law. Do not infer independence from the existence of this interface. |
| [Runtime phases](../Vegas/Pending/RuntimePhase.lean) and [phase application](../Vegas/Pending/PhaseApplication.lean) | Source phase partition, current and saved state, attempt identity, exclusion and rollback operations. | Separate atomic packet/environment effects from immediate phase advancement where the fixed-window controller requires it. |
| [Source readout and exclusion payoff](../Vegas/Game/PhaseExclusionPayoff.lean), [joint observation](../Vegas/Game/TerminalObservation.lean) and [terminal audit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean) | Typed decoding, realized settlement and the source-defined joint observation. | Derive the new verifier's charge from actual final ledger evidence and connect the concrete controller to these readers. |
| [Sequential raw preservation](../Vegas/Game/SequentialPhaseRawPreservation.lean) and generic [action extension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean) | Existing sequential consumer, common consistency construction and comparison/extension machinery. | Prove the new runtime's information and continuation comparisons. A specialized old theorem is not already such an instance. |

Outer recording is already separate from application acceptance:
`Interaction.ReactiveApplication.Execution.includePending` updates the network
ledger even when the application handler returns no result. The
[publication module](../Interaction/ReactivePublication.lean) already proves
network publication invariants. The new task is to guarantee the required
bodies reach that ledger under the specified service, not to invent another
rejected-call archive.

## Definition boundaries

### Source compilation and phase control

Keep dependency order, phase grouping and physical timing distinct. Existing
`Vegas.EventGraph.ExecutionMode` changes dependency order. A phase plan groups
source events. A controller decides when an installed phase closes and when
the next phase becomes ready. Choosing a sequential order does not by itself
specify the network scheduler or require fixed publication windows.

Start with two concrete controllers: the existing immediate phase controller
and the fixed-window controller required by the concurrent construction. Share
the atomic semantic operations they actually use. If an existing operation
combines a packet effect with normalization, extract the effect and retain
normalization in the immediate controller. Prove that recombining them gives
the existing transition before relying on old proofs.

Prefer a small state extension holding the window times to a new copy of the
source store, rollback state and interpreter. First verify which existing
invariants survive between an atomic effect and delayed normalization; some
current lemmas assume a normalized phase frontier. Do not claim they transfer
merely because the state records have similar fields.

In particular, completing a native event refreshes readiness timestamps in
[EventApplication](../Vegas/Pending/EventApplication.lean), including events
outside the installed phase. Simply postponing normalization can start the
next phase's deadlines before that phase becomes available. The fixed-window
controller must define phase-gated activation or installation-time deadline
rebasing, with the corresponding observation and invariant proofs. The
immediate controller must retain its existing timestamp behavior.

Do not introduce an arbitrary failure-handler algebra or a product of Boolean
configuration switches. Both concrete implementations use the source's
specified settlement meaning. Global abort, different quit semantics and
different intended games are separate changes requiring their own arguments.

### Physical communication and service

Retain the existing engine's separation of player response, network observation,
inclusion and application commands. A global mathematical pending pool is not
a player observation. Scheduler access to network data is distinct from player
knowledge; neither justifies inventing a public order of senders.

For the new service, distinguish signed body, broadcast occurrence and
broadcaster. A forwarded body does not change its signed author. A replay does
not create a new body job or reset its inclusion deadline. Reuse the existing
authentication/known-packet machinery where its definitions have this meaning;
add the missing body identity and authorization data at the packet layer.

The current reactive response emits at most one envelope. The concurrent
mathematics permits bounded fresh bodies together with replay coordinates.
Encoding this as a list payload would couple their inclusion; serializing it
into several responses can add observations or decisions. Neither is a free
representation change. Resolve this finite batch interface with an explicit
transition and information comparison before extracting more generic APIs.
A wider engine primitive is justified only by that concrete mismatch.

Keep engine fuel, player sending opportunities and blockchain time distinct.
Several engine commands may implement one logical block; their count must not
silently become a new player-visible clock or a public sender order. A concrete
service must relate these units and provide enough commands/capacity for its
claimed opportunity and publication bounds.

Keep service properties separate. The existing phase service protects a sole
packet for a current attempt/event. The concurrent route additionally needs
publication of every submitted in-scope body, including rejected/stale bodies,
and independent fresh service. State those properties over actual executions;
construct a scheduler satisfying them. Do not strengthen the shared service
record so every sequential instance must satisfy the concurrent assumptions.

Submission commits all new body jobs before exposing any component effect.
Exclusion, retirement, rejection and base-payoff freeze cannot cancel them.
Final audit occurs after the last permitted raw submission plus the publication
bound. These are essential to stopping the raw comparison at submission;
finite capacity alone does not establish them.

Capacity is finite data plus a coverage proof for the actual raw menu. It
includes post-exclusion traffic, fresh bodies and replay occurrences. Use
per-author, per-run publication bounds and separate audit collateral. A later
capacity reduction should replace this resource argument while retaining the
same service laws; if it introduces congestion dependence, the timing proof
must also change.

### Information and legal actions

Derive the target information model from actual engine observations and recall,
using the existing response-menu construction. Do not accept an unrelated
information model as a field. Derive the raw menu from the declared bounded
message syntax and the player's actual knowledge; prescribed honest behavior
is a strategy, not the raw menu.

The existing observation interface selects pending identifiers and retains
the corresponding whole envelopes. Use it for partial reception of whole
packets. Partial-body and standalone count/metadata signals are additional
expressiveness questions, not a reason to replace partial reception and recall.
Introduce such an extension only with a concrete instance and a reduction of
the existing packet-only interface.

Opacity, own-service freshness and the reset comparison belong in the relevant
proof hypotheses or in lemmas derived from a concrete observation law. They
must not become hidden restrictions in the common information definition.
Ignoring old traffic is a property of a chosen continuation strategy and its
proof. It does not erase the player's actual memories or remove old-message
deviations. A stronger sequential theorem may use a different information
argument without changing the execution engine.

Likewise, the existing sequential theorem's conditional independence hypothesis
on private initial inputs is a proof premise, not part of the common runtime
definition. A future stronger theorem should be able to replace that argument
while keeping the same initialization and execution. No weakening of the
current theorem's hypothesis is claimed by this design.

### Settlement and the paper statement

Reuse the actual source decoder and terminal settlement machinery. Exclusion
must come from the controller state; charges must come from the chosen audit
on actual evidence. The intended joint law retains initial data, typed result,
public result and realized net payoff together. An arbitrary output function
or a free charge flag is not an implementation specification.

The implementation object should package concrete configuration: the compiled
graph/phase plan, controller, packet/menu bounds, service and audit data. Its
execution protocol, information model and readers are derived definitions.
Configuration selects a concrete controller construction; it does not supply
arbitrary transition, observation or readout functions in their place.
Operational hypotheses concern these concrete objects. They must not contain
SE preservation or its deviation comparison as an assumed field.

The existential in [Paper](../Paper.lean) ranges over such concrete
configurations before the source equilibrium is selected. The supplied service
law and its assumptions are fixed outside that existential, so it cannot choose
a more favorable network. The theorem may select the contract configuration
and an implementing equilibrium. No new contract programming language is
required merely to express this result.

The generic [broadcast carrier](../Vegas/Game/BroadcastImplementation.lean) is
not the basis for this implementation: its freely supplied protocol, model and
readers fail to enforce these connections. Replace that draft when the concrete
definitions are available; do not fill its gap with an unspecified predicate
or an admitted constructor. `Paper.lean` remains one file of statements.

## Known semantic risks and required checks

| Risk | Required evidence |
| --- | --- |
| Microstep serialization exposes an order of sends or introduces intermediate choices. | Show the actual views and legal deviations of the batch representation; a terminal-state equality alone is insufficient. No invented public sender calendar. |
| Delaying closure changes accepted calls, source information or future deadlines. | Give exact boundary order, including inclusion at the deadline, failure settlement and readiness. Prove both the immediate-controller identity and the new window rules. |
| Private preparation consumes later legal choices. | Establish that future admitted source choices and fresh submission allowance remain available at every relevant raw prefix. Reuse candidate machinery only with this property. |
| Retry forgets information or lets old authenticated bodies become current again. | Preserve recall and actual archives; distinguish attempt authorization from a sender-supplied tag; prove fresh-action and old-replay comparisons. |
| Guards or samples are evaluated at a different source position. | Keep component opening order, intervening public samples and saved obligations; check a guard when its last required input is available. |
| Audit relies on private traffic rather than public evidence. | Identify each positive witness in the final ledger under every raw continuation, including late sends and post-exclusion traffic. Inclusion liveness is an explicit service assumption. |
| Recording or reporting costs alter the promised payoff law. | Specify the funding and payoff accounting. The primary construction funds publication separately and has no strategic reports; do not silently subtract variable fees from a supposedly unchanged source payoff. |
| A small observation change invalidates conditional incentives. | Check the likelihood/conditioning comparison at actual information sets along one common fully mixed sequence. Matching terminal distributions or limiting strategies is insufficient. |
| A new common interface silently narrows the sequential theorem. | Instantiate the existing sequential runtime with its original service and observation hypotheses; preserve its stated conclusion exactly. |

## Implementation order and limits on abstraction

1. Record the concrete transition differences using the owners above, including
   the batch interface and delayed-normalization invariants. Resolve those
   representation issues before committing to a common state structure.
2. Extract only atomic operations needed by both controllers. Re-establish the
   existing sequential runtime and its raw-preservation consumer through these
   definitions. Do not add the new concurrent service assumptions to that proof.
3. Build the fixed-window controller and body service on the existing engine,
   adding only the justified packet/menu changes. Prove the operational facts
   needed to identify its actual game, observations and settlement.
4. Replace the arbitrary-game existential draft with the fully defined concrete
   statement. Its SE proof may remain the explicitly requested admission; its
   target semantics may not.
5. Instantiate the retained-game comparison and raw extension. Keep the
   timing/information arguments specific to the service they actually prove.
   Extract a common theorem only when both preservation routes use its contract.

The existing sequential raw theorem and its
[funded executable example](../Vegas/Examples/SequentialPhaseServiceEquilibrium.lean)
are the first reuse checks. The new concurrent instance is the second consumer.
No compatibility aliases are needed: update callers of a justified extraction.

Do not add a universal compiler framework, a generic effect system, a hierarchy
of arbitrary schedulers or a capability for every possible audit. Parameterize
existing data where it already varies. Extract a new interface when two concrete
consumers need the same operation and its precise laws. Keep genuinely different
proofs separate even when they share execution definitions.

The intended payoff is controlled change impact, not proof immunity: changing
a numerical deadline can be local, while adding a signaling channel may require
a new preservation argument. Both should be expressible without replacing the
source compiler or the execution/game foundation.
