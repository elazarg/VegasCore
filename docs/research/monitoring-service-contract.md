# Passive observation as an existing runtime service

The checked block composes existing operations: activate a watcher whose
policy is silent, then idle the round's network slot. The watcher transmits
nothing. What it observes is the ordinary pending-message sample of the
application's observation rule, recorded in its leaked list. It adds no
interpreter, observer timestamp, report packet format, or scheduler access to
the private sample. Ordinary players retain the application's original
pending-message observation rule.

## Reports and the challenge window

The watcher reports only signed packets it actually observed. The
[challenge-window interface](../../Interaction/ChallengeWindow.lean) separates
the partial observation kernel from report delivery, which may depend on the
entire observed list. Reports can be omitted or arrive too late; only evidence
delivered before settlement enters the audit. The window leaves an explicit
inclusion bound after the report cutoff. Observation and conditional delivery
coverage combine without independence or certain observation.

This is a backend contract, not a proof that an ordinary pending-message client
has the stated coverage. Implementing the report kernel with the same pending
mechanism needs its own service realization. The watcher may continue observing
past player deadlines, but the theorem still needs the stated conditional
probability of actual collection. A longer challenge window can support that
bound; it does not derive it by itself.

Settlement judges reported signed packets against the final contract record
(`Vegas.EventGraphRuntime.SettledRecord.Permits`). No verdict reads when a
packet was sent. Public missed-decision markers are checked separately from
packet evidence; absent reports never certify a miss.

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

[Settled collection](../../Vegas/Pending/ReactiveSettledCollection.lean)
proves `settledPacket_collection`: an actual packet forbidden by the final
record gives a bound on actual collection from observation and conditional
report delivery. [Signed evidence](../../Vegas/Pending/ReactiveSignedEvidence.lean)
separately proves that actual content breaches remain forbidden under complete
play. Establishing the final verdict is an operational premise, not a
consequence of having sampled a packet.

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

The [fixed roster](../../Vegas/Game/ServiceRoster.lean) may repeat owners and
other players before protected event inclusion. More adaptive visits require
the general service and stopped-law proofs. A pending packet ignored by
inclusion may still affect other players' observations and incentives.

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

## Remaining integration obligations

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
