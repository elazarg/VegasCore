# Passive observation as an existing runtime service

The checked block composes existing operations: activate a watcher whose
policy is silent, then idle the round's network slot. The watcher transmits
nothing. What it observes is the ordinary pending-message sample of the
application's observation rule, recorded in its leaked list. It adds no
interpreter, observer timestamp, report packet format, or scheduler access to
the private sample. Ordinary players retain the application's original
pending-message observation rule.

## Reports and the challenge window

The watcher's report is the list of signed packets it observed. It reaches the
contract in the watcher's own transaction, which the contract includes within
the challenge window: a report sent before the last deadline is included within
`W` slots, and settlement waits `W`. That window is the only chain assumption
the report adds. No builder duty is assumed: the service never has to include
anyone else's packet on the watcher's behalf, and the watcher never rebroadcasts
a packet to report it.

Settlement judges every packet in the report, and every packet on the contract's
own ledger, against the settled record
(`Vegas.EventGraphRuntime.SettledRecord.Permits`). No verdict reads when a
packet was sent. `Vegas.departureEvidence` is the resulting charge: a packet
signed by the owner, on the ledger or in the watcher's report, that the settled
record forbids.

## Fixed policy and conditional evidence bound

`Interaction/ReactiveMonitoring.lean` defines `silentPolicy` and
`observationRound`: the watcher is activated and responds, then the round's
network slot waits. `observationRound_quiescent` proves that a silent watcher
leaves the network unchanged when pending traffic is published. Both are fixed
before any deviation or equilibrium is selected.

`sampling_observed_lower` proves that a fresh foreign pending envelope is in the
watcher's observed list at the end of play with probability at least its
sampling probability. The observation persists through arbitrary later raw
policies and scheduler commands. The statement evaluates actual activation and
sampling; it assumes no separate delivery kernel.

`Vegas.reserved_observation_departure_lower` combines that bound with the
actual reserved inclusion. A departing packet for the current event is included
at once and lands on the ledger; any other packet stays pending for passive
observation. Either way a condemned packet signed by the owner is marked
(`Vegas.markedDeparture`), the mark persists (`Vegas.markedDeparture_persistent`),
and at a settlement that completed every event it is a charge
(`Vegas.markedDeparture_evidence`).

The bounds are conditional on a concrete starting execution. An SE adapter must
establish them at every compatible retained history, or prove a suitable
belief-weighted bound. They do not establish a universal positive sampling rate,
watcher incentives, or collection of a financial penalty.

The native `idleNetwork` and `run_observation_plan` in
`Vegas/Pending/ReactiveMonitoring.lean` identify the block with the existing
two-instruction plan: watcher activation followed by a wire turn.

## Premature packets

`Vegas/Pending/ReactiveMonitoring.lean` proves
`handle_eq_none_of_other_event_ready_public`: while a public event is ready in
a barrier-ordered graph, every packet addressed elsewhere is rejected. This
covers a future event owned by the same player, not just another player's event.
A packet also carries the readiness token of its event, attached when it is
emitted, and the contract rejects a packet without one. A packet sent before its
event is ready is therefore never accepted, and once the event settles the
settled record forbids it.

The constructed reveal service order is owner response, inclusion reserved for
the current event, watcher observation, then ticks and expiry. A canonical
opening is published before observation. An off-address extra is ignored by the
reserved inclusion and stays pending for observation. This order has complete
local source-step and deadline proofs. The fixed plan settles every event under
arbitrary raw behavior.

This service activates only the source owner for that event. With additional
ambient activations, that owner could send a valid current opening before its
canonical slot. Covering such a roster requires a separate phase argument, or a
proved coalescing argument when no strategic decision intervenes.

Rejection is not automatically misconduct, and a settled verdict judges content,
not timing. A sound enforcement adapter must prove that canonical current
actions have a timely opportunity and are accepted. It must not charge the
original owner merely because another player rebroadcasts an old valid envelope:
a copy of an accepted packet is permitted by the settled record.

`Vegas/Pending/ReactiveOpeningConformance.lean` supplies the format check:
an opening call must carry exactly its matching certificate. Its
`current_opening_submission_cases` theorem classifies each submitted
current-event packet as canonical after normalization, rejected, or a public
format violation. Accepted-handle and fixed-value premises follow from the
binding invariant. The settled verdict additionally requires that an accepted
opening's value pass its event's checks on the settled public store.

## Remaining general reveal-class obligations

- A missed sample may still leak to other players; the utility comparison must
  tolerate every subsequent response.
- Handle spent-envelope replay and private response aliases honestly. Even when
  no other player learns anything, the sender's own recall can differ and later
  raw policies can branch on it. No uniform comparator follows just from equality
  of public results.
- Fix collectible losses from declared payoff bounds before choosing an SE.
  A settled charge is evidence, not an escrow implementation. Once-collected
  penalties do not automatically deter further departures after a prior penalty
  is sunk; the extension proof must complete those off-path continuations.

`InteractionTests/ReactiveMonitoring.lean` checks one-half observation under
arbitrary later policies and permits ordinary pending observation. No general
source-to-native SE theorem is claimed by this service component alone.
