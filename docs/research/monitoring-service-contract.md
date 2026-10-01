# Passive reports as an existing runtime service

The checked block composes existing operations: activate a watcher, let it
respond, then include its public rebroadcast if the identifier is unpublished.
It adds no interpreter, observer timestamp, report packet format, or scheduler
access to the private sample. Ordinary players retain the application's original
pending-message observation rule.

## Fixed policy and conditional evidence bound

`Interaction/ReactiveMonitoring.lean` defines `reportFirstUnpublished`: inspect
the ordinary leaked-packet list, skip identifiers already on the ledger, and
replay the first remaining envelope. This policy is fixed before any deviation
or equilibrium is selected. The public `includeReported` command checks the
broadcaster, excludes watcher-authored envelopes, and applies the existing
at-most-once inclusion filter. Attribution remains the original envelope ID;
it does not identify a later rebroadcaster to ordinary observers.

`reportFirstUnpublished_after_activation` discharges reporting when all older
leaked envelopes are published and the pending pool has only one unpublished
identifier. This is a first-departure condition to derive at retained source
prefixes, not an assertion about arbitrary attack histories or multiple reports
per activation. Published duplicates do not compete with the fresh report.

`sampling_receipt_lower` proves that a fresh foreign pending envelope receives
its actual acceptance/rejection receipt with probability at least its sampling
probability. The receipt persists through arbitrary later raw policies and
scheduler commands. `sampling_rejected_receipt_lower` specializes rejection;
`sampling_ledger_violation_lower` proves persistent static conformance evidence
even if the application accepts the call. These statements evaluate actual
activation, replay, and inclusion; they assume no separate delivery kernel.

The bounds are conditional on a concrete starting execution. An SE adapter must
establish them at every compatible retained history, or prove a suitable
belief-weighted bound. They do not establish a universal positive sampling rate,
watcher incentives, or collection of a financial penalty.

The native `reportNetwork` and `run_report_plan` in
`Vegas/Pending/ReactiveMonitoring.lean` identify the block with the existing
two-instruction plan: watcher activation followed by a wire turn. The generic
`reportInclusion_quiescent` theorem proves that the fixed reporter stays silent
when retained and pending traffic is already published. It retains the actual
response recall and both service commands.

## Premature packets without phase certificates

`Vegas/Pending/ReactiveMonitoring.lean` proves
`handle_eq_none_of_other_event_ready_public`: while a public event is ready in
a barrier-ordered graph, every packet addressed elsewhere is rejected. This
covers a future event owned by the same player, not just another player's event.
`sampling_out_of_phase_receipt_lower` combines that result with the report block.
The failed receipt remains evidence even after the address becomes ready.

The constructed reveal service order is owner response, inclusion reserved for the current
event, watcher/report, then ticks and expiry. A canonical opening is published
before observation, so the watcher skips it. An off-address extra is ignored by
the reserved inclusion; the current event remains ready for the report block.
This order has complete local source-step and deadline proofs. The fixed plan
settles every event under arbitrary raw behavior. Its source correspondence
still requires induction over all ordinary response histories.

This service activates only the source owner for that event. With additional
ambient activations, that owner could send a valid current opening before its
canonical slot: the handler ignores the service calendar, so neither rejection nor a
static packet-format check detects that early timing. Covering such a roster
requires a separate phase witness/enforcement argument, or a proved coalescing
argument when no strategic decision intervenes. The other-event rejection lemma
does not cover this case.

Rejection is not automatically misconduct. A sound enforcement adapter must
prove that canonical current actions have a timely opportunity and are accepted,
and that already published reports are skipped. It must not charge the original
owner merely because another player rebroadcasts an old valid envelope. Successful
noncanonical current traffic, such as an explicit withholding packet when the
compiler implements withholding by silence, needs a separate public format audit
or a proved harmlessness comparison.

`Vegas/Pending/ReactiveOpeningConformance.lean` supplies the format audit:
an opening call must carry exactly its matching certificate. Its
`current_opening_submission_cases` theorem classifies each submitted
current-event packet as canonical after normalization, rejected, or a public
format violation. Accepted-handle and fixed-value premises follow from the
binding invariant. This is a packet classification, not a guard-success theorem;
interpreting its canonical opening as a legal source action still requires the
source guard condition.

## Remaining general reveal-class obligations

- Derive clean-prefix reporting conditions and a conditional sampling lower
  bound from the actual finite service. A missed sample may still leak to other
  players; the utility comparison must tolerate every subsequent response.
- Prove canonical opening and silence/expiry checkpoint laws for every legal
  source policy, including all withholding choices and correlated initial types.
- Apply the checked effective-response classification at every ordinary prefix:
  published replays represent withholding; all other extra responses create
  attributable rejection or a public format violation. The actual reserved
  inclusion/report suffix gives a persistent evidence lower bound equal to the
  fresh packet's sampling probability, even with arbitrary later responses.
- Handle spent-envelope replay and private response aliases honestly. Even when
  no other player learns anything, the sender's own recall can differ and later
  raw policies can branch on it. No uniform comparator follows just from equality
  of public results. A service-specific quotient, closed source representation,
  or another strategic argument is still needed for that case.
- Fix collectible losses from declared payoff bounds before choosing an SE.
  A persistent receipt is evidence, not an escrow implementation. Once-collected
  penalties do not automatically deter further departures after a prior penalty
  is sunk; the extension proof must complete those off-path continuations.

The selected replay route enlarges the source-representable C menu with published
replays as aliases of silence, then applies sanctions to restore the remaining
responses. Pending observation is inert on those C histories, and the checked
reserved selector ignores spent identifiers. The outstanding proof is the
source-to-C history and belief correspondence with these additional private
action names. It should use local incentive equality and the existing one-shot
theorem; no arbitrary raw continuation is claimed replay-insensitive.

`InteractionTests/ReactiveMonitoring.lean` checks one-half detection under
arbitrary later policies, permits ordinary pending observation, and exhibits a
payload rejected now but accepted in a later application state. No general
source-to-native SE theorem is claimed by this service component alone.
