# The message runtime, its service schedule, and compilation

## 1. The three components

The runtime has three distinct components:

1. **A message machine** stores pending packets, delivers them to players, and
   publishes them in a ledger.
2. **An application** checks included packets and updates the game's shared
   state. It also provides explicitly triggered chance and timeout operations.
3. **A service driver** decides when players can act, when the network can act,
   and when application operations run.

The message machine has no built-in turns or clock. The selected service driver
supplies the finite schedule used in the theorems. In particular, the number
three comes from this driver and its command-based strategy compiler.

The response protocol uses the same message operations and service schedule,
but makes an uninterrupted player response one strategic decision. The
command-based compiler and the response protocol have different proof status;
Section 8 identifies the boundary.

## 2. The message machine, independently of Vegas

An envelope contains a sender identity, a sender-local serial number, and a
payload. The state contains:

- a list of pending envelopes;
- a shared ledger of included envelopes;
- a separate inbox for each player;
- each player's sent-envelope list;
- the next serial number for each sender.

These operations have the following effects:

| Operation | Who chooses it in the policy model? | Effect |
|---|---|---|
| Submit a payload | A player | Create an envelope under that player's identity and append it to pending and that player's sent list. |
| Replay a known envelope | A player | Append another unchanged copy to pending and the broadcaster's sent list. The original author and identifier remain unchanged. |
| Deliver an envelope to a player | The wire policy | Copy one pending envelope into that player's inbox. The envelope remains pending. |
| Include an envelope | The wire policy, or reserved service | Remove one pending copy, append it to the shared ledger, and invoke the application's handler. |
| Wait | A player or the wire policy | Make no transmission or network change. |

Delivery and inclusion select an existing envelope by its identifier. Selecting
a missing identifier has no effect. Replay is possible only for an envelope
the broadcaster knows from its sent list, inbox, or the shared ledger.

The policy interface authenticates newly authored submissions: a policy
invoked as Alice submits as Alice. The bare envelope datatype itself contains
ordinary identity labels. The operational/authorship invariants establish the
authentication property; a signature algorithm is outside this model.

Inclusion always publishes an existing selected envelope, even if the
application rejects its contents. Acceptance changes application state;
rejection leaves application state unchanged. Both produce a public receipt.
A rejected opening can therefore already have disclosed its raw value.

This machine permits reordering, selective delivery, repeated delivery, and
replay. It has no automatic delivery guarantee. An envelope can remain pending
throughout the finite run. The operations contain no fees, block construction,
reorganizations, or real-time delays.

See [MessagePool.lean](../Interaction/MessagePool.lean),
[TransactionalInclusion.lean](../Interaction/TransactionalInclusion.lean), and
[MessageApplicationPolicies.lean](../Interaction/MessageApplicationPolicies.lean).

## 3. What a player and the network can observe

A player sees its own inbox and sent list, the shared ledger and receipts, the
public application projection, its authorized private application information,
and its own action recall. Recall records the view before each own action and
the action selected. The response model also permits private memory in actions.

The wire policy sees the complete message pool, public application projection,
receipts, and environment history. It can inspect pending packet contents and
choose recipients and inclusion order. It cannot inspect private commitment
meanings, private inputs, or the players' private action recall.

Thus pending packets are available to the network, while player access depends
on delivery or publication. A player does not receive an automatic view of
the complete pending pool.

A wire invocation chooses exactly one of:

```text
deliver one pending envelope to one player
include one pending envelope
wait
```

The wire policy can adapt and randomize using its observation and history. The
service-order policy can likewise adapt when it selects each epoch's order.
Both policies are fixed parameters of a player game: replacing Alice's policy
leaves their functions fixed, although their choices can change in response to
Alice's traffic. They are not additional utility-maximizing players in that game.

See [MessageApplicationWirePolicy.lean](../Interaction/MessageApplicationWirePolicy.lean)
and [EventPlayerAction.lean](../Vegas/Pending/EventPlayerAction.lean).

## 4. The event application

The application can be specified directly by a finite event graph, without a
source program. Each event has a stable address, a kind, prerequisites, and
an output field. Strategic events also have an owner and a deadline.

| Event kind | Application operation |
|---|---|
| Binding | Accept an owner-authored commitment handle and record its immutable meaning privately. |
| Resolution | Resolve an earlier binding by a verified opening or withholding, producing a public success or failure. |
| Sample | Draw from a specified probability kernel and record its public result. |

An event can complete only after its prerequisites have completed, and can
complete at most once. The state records completed events, their results,
accepted handles, the logical clock, activation times, and the current service
grant. Private projections expose a player's own values and candidates.

Packets have four forms: commitment, opening, withholding, and arbitrary
malformed data. Inclusion checks the event address, readiness, deadline,
authorization, and the relevant commitment conditions. An invalid packet can
be rejected without completing an event. A verified opening that fails an
application guard completes the resolution with failure. Expiry can also
complete an unresolved strategic event with failure.

Commitment meanings are ideal semantic state. In the response/action model,
an authored commitment submission can carry private opening material alongside
its public envelope. For a fresh owned handle, this fixes the meaning before
the envelope enters pending; only the envelope goes onto the network. A fresh
handle submitted without opening material becomes unopenable. Subsequent
actions cannot change a fixed meaning. A player can create multiple handles
and submit competing commitments; fixing each candidate's meaning does not
decide which candidate the application will accept.

This gives exact binding and controlled observation in the mathematical model.
A cryptographic implementation would need its own realization proof.

See [EventApplication.lean](../Vegas/Pending/EventApplication.lean) and
[EventBindingAction.lean](../Vegas/Pending/EventBindingAction.lean).

## 5. A slot is a scheduled policy invocation

Calling something a *slot* means that the service driver gives a particular
policy one opportunity to act. The schedule determines whose opportunity it
is. Taking a slot does not advance the logical clock.

There are two player interfaces in the repository:

| Interface | What one player invocation returns |
|---|---|
| Command-based service used by the end-to-end compiler theorem | One private command, submission, replay, or wait. |
| Native action protocol used for the SPE investigation | Private memory together with an optional submission or replay. Commitment opening material can be supplied privately in the submission itself. |

In the second interface, local computation and sampling happen inside the
policy. One invocation can produce one envelope, or none. It has no modeled
computation charge. The coalesced response interface groups adjacent invocations
of the same player into one decision producing an ordered list of these actions.
The list retains the existing number of transmission opportunities.

### Where Alice gets three opportunities

For each event owned by Alice, the driver reserves three consecutive Alice
invocations. The command-based strategy compiler uses them as follows:

1. Sample the graph action once and remember it privately.
2. Stage its private commitment material, or perform a private memory operation.
3. Submit the event-addressed packet.

This same shape covers successful and failed prescribed choices, keeping their
submission position independent of that private distinction. The service grants
all three opportunities even if the event is unavailable; a prescribed player
then waits.

Each invocation admits arbitrary player behavior. Alice can use all three to
submit packets instead of following the prescribed staging sequence. Consequently
the schedule also permits three competing envelopes. That capability matters
when reasoning about deviations.

The response model can sample, retain memory, and supply commitment material
within one action. It nevertheless uses the same three-call service plan.
Coalescing makes that prefix a single response with three optional transmissions;
it does not reduce its packet budget. The number three is therefore a constant
built into this service implementation, justified by the command
compiler's staging protocol. A final runtime interface needs an independent
justification for its chosen transmission budget.

See [EventPolicies.lean](../Vegas/Pending/EventPolicies.lean),
[EventService.lean](../Vegas/Pending/EventService.lean), and
[ResponseProtocol.lean](../Vegas/Pending/ResponseProtocol.lean).

## 6. Exactly how the driver runs

At the beginning of an epoch, the order policy selects a permutation of all
events. The driver visits each event once in that order. The order need not
respect prerequisites; the application checks readiness.

For a player-owned event `e`, its visit is:

```text
publish grant naming e
invoke its owner three times, without network activity between calls
repeat reactionRounds times:
    invoke the wire once
    invoke each player in the reaction roster, in list order
try reserved inclusion for e
try the sample operation for e
```

A *reaction roster* is a fixed list supplied to the service. It may omit
players or repeat them. Every event owner receives its initial three calls
regardless of roster membership. Reaction calls can be used for any legal
traffic; packets need not address the currently granted event.

Reserved inclusion selects the rightmost still-pending envelope authored by
the event's owner and addressed to that event. It attempts inclusion of that
envelope, or waits if none exists. Replay can affect the pending-list order.
The selection uses public envelope metadata; application acceptance is a
separate check. Ordinary wire calls may include any pending envelope, including
one for another event.

For a sample event, the visit consists of its grant and sample operation; it
has no owner calls or reaction rounds. The sample attempt attached to a
strategic event has no effect. A ready sample executes its fixed kernel once;
the environment does not choose the sampled value.

After all event visits, the driver advances the clock once and checks every
event for expiry. An event's deadline is measured from its activation time.
The finite run has `n * (D + 1)` epochs, where `n` is the event count and `D`
the maximum deadline. The prescribed-play protection theorem assumes each
deadline is at least two ticks, allowing an event enabled after its visit to
receive another full service opportunity before expiry.

Reserved inclusion, regular visits, and clock control are substantive service
assumptions. They supply the progress and deadline protection used by the
compiler proof. Implementing them on a concrete ledger is an additional task.

### A message can be read and answered before inclusion

Suppose `e` is Alice's ready resolution event, the roster is `[Bob]`, and
there is one reaction round. One permitted execution is:

```mermaid
sequenceDiagram
    participant A as Alice
    participant P as Pending pool
    participant N as Network / driver
    participant B as Bob
    participant C as Application
    Note over A,C: Grant e; Alice's uninterrupted response
    A->>P: Submit opening m containing value v
    N->>B: Deliver m from pending
    Note over B: Read v; choose a response
    B->>P: Submit another packet n
    N->>C: Reserved inclusion of m
    Note over C: Verify m and complete e
```

The opening stays pending when delivered. Bob reads the actual packet and
acts before Alice's event completes. Bob's packet remains subject to its own
event's readiness and authorization checks. Coalescing Alice's initial calls
leaves the delivery and Bob's reaction in place.

In general a network call performs only one operation, so delivery followed
by wire-selected inclusion requires two network calls. In this example the
later reserved-inclusion instruction supplies the second operation.

## 7. How Vegas compiles into this runtime

Compilation supplies an application description and player-policy embeddings.
The service configuration and its wire/order policies are runtime parameters.

### Program to application graph

| Source construct | Graph/application representation |
|---|---|
| Initial private input | An owner-visible input field; no commitment, event, or packet. |
| Commit a value | A binding event with an owner and an opaque accepted handle. |
| Reveal or withhold | A resolution event referring to the earlier binding. |
| Deferred guard | A check attached to the resolution where the required values become available. |
| Public sample | A sample event using the compiled probability expression. |
| Return | Terminal readout metadata. |

Dependencies enforce data availability and the public and own-action ordering
required by the source observations. Sequential execution adds all earlier
events as prerequisites. The driver can offer service out of order, but a
packet cannot make an unavailable event complete.

See [EventGraphCompiler.lean](../Vegas/Compile/EventGraphCompiler.lean) and
[EventGraphLayout.lean](../Vegas/Compile/EventGraphLayout.lean).

### Source strategy to player policy

For a ready granted event owned by the player, the prescribed policy samples
the corresponding source/graph action once and remembers it. Its packet has
one of these forms:

- **Binding:** a commitment packet naming a stable event-addressed handle,
  whose material is staged privately.
- **Successful disclosure:** an opening containing the accepted handle and
  correctly typed value.
- **Failed publication:** a withholding packet. This includes an attempted
  disclosure whose guard would fail. The original intention remains private
  policy memory.

The withholding form is necessary for the source observation contract: sending
a guard-invalid secret and relying on rejection would expose that secret in
transit or in the ledger. The prescribed policy computes the public result
before constructing its packet.

Players remain free to deviate from this policy, send malformed or premature
packets, compete with their own earlier submissions, replay known envelopes,
wait, and react to their inboxes. The runtime enforces application validity;
the compiler's prescribed strategy is not an enforcement mechanism.

See [EventPolicies.lean](../Vegas/Pending/EventPolicies.lean) and
[EventMessages.lean](../Vegas/Game/EventMessages.lean).

## 8. What the proofs currently connect

The end-to-end source compiler and its Nash/Bayesian results use the
**command-based serviced game**. They establish the prescribed outcome law
and simulate arbitrary unilateral message-policy deviations against prescribed
opponents. The joint initial-parameter/public-result version supports utilities
depending on private initial types. Their observation is the designated game
result; it is not equality of the entire native packet transcript.

Early delivery is part of that deviation model. The simulation uses immutable
bindings, prescribed packets that determine the eventual public result,
protected service, and graph barriers. A deviator's early reaction is interpreted
at an effective source decision where the relevant result is available.

The **native action and coalesced response protocols** have checked submission
binding, locality, bounded execution, expansion of coalesced histories, and
uniform policy translations with exact endpoint laws at each response entry.
The complete source-policy compiler and whole-service strategic bridge for
these protocols remain open. The existing command-service compiler theorem
cannot simply be applied to them without that bridge. Source-to-response SPE
preservation is also open.

Finally, the response information model requires its legal batch length to be
determined by the player's existing information. That fact is proved for an
empty reaction roster, where every response has length three. General rosters
give varying lengths and still need the corresponding proof. This obligation
comes from retaining and coalescing the specific finite invocation schedule.

See [EventMessageStrategic.lean](../Vegas/Game/EventMessageStrategic.lean),
[ParameterOutcomes.lean](../Vegas/Game/ParameterOutcomes.lean), and
[Action boundaries and subgame perfection](action-coalescing.md).
