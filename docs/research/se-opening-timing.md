# Opening time: a real channel, not an automatic SE obstruction

## Checked native witness

`VegasTests/OpeningTimingChannel.lean` uses the existing initialized graph,
reactive interpreter and canonical compiled opening. The service offers two
owner responses, with a foreign pending-message observation between them.
The owner sends the same opening at the first or second visit. No inclusion,
clock tick, expiry or grant change occurs during the window.

The checked facts are:

- `both_openings_ready` and `both_openings_compiled`: both possible sends use
  the ready, granted event and its actual compiled opening response.
- `same_opening_packet`: the packet body, certificate, author and identifier
  are identical.
- `same_final_current_view` and `same_final_application`: the final receiver
  view, public environment view, application and clock agree; the ledger is
  still empty.
- `final_information_distinguishes`: the receiver's actual information differs,
  because its own response recall retains the earlier pending-message view.
- `same_traffic_records` and `every_traffic_audit_agrees`: the current terminal
  traffic readout cannot distinguish the timings. It records phase, prior
  ledger and transmission, but no intervening silent activation markers.

Thus eventual equal publication does not establish information equality.
Batching ledger inclusion alone does not hide pending-message timing.
`runRounds_published` does not apply to this window: the opening is unpublished.
The sample-all observation used by the witness is a legal existing rule; no
self-delivery, new private memory field, or new interpreter is introduced.

## What the witness does not establish

Timing a constant opening can communicate a sender-chosen bit. It does not
authenticate a claim about another private value. A receiver may ignore this
cheap talk in an SE supported by type-independent timing trembles. The existing
authentic-disclosure impossibility therefore cannot be applied just by renaming
its disclosure action to an early opening.

No forward-SE impossibility has been proved for this timing window. The witness
does refute an observation-isomorphism argument and a claim that the current
phase-only audit can enforce a unique transmission slot. Neither failure alone
requires adding exact-time observability to the runtime.

## Candidate positive refinement

A possible source-preserving extension chooses one fixed timing distribution
conditional on the eventual public source action. That distribution must not
depend on the sender's further private information. At later meaningful source
decisions, the timing observation would then contribute a common likelihood
factor and leave the source posterior unchanged.

The needed operational conditions are substantive:

1. Before the window closes, other retained player responses are only silence
   or already-public replays; they cannot make a meaningful source decision.
2. The owner acquires no new payoff-relevant private information between visits.
   In particular, the window must not straddle another source decision, a new
   private chance event, or an informative unpublished message.
3. The available timing choices and their service effects do not depend on
   additional hidden facts once the eventual source action is fixed. Every
   source action, including withholding, has its required completion paths.
4. Every permitted opening time receives the same protected service outcome.
   Deadline changes or priority races must not create additional payoff or
   future-choice effects.
5. A single fully mixed construction realizes these conditional timing laws,
   and the projected beliefs and local incentives hold at all decision sites.

These conditions are a proof route, not a checked timing-SE theorem. In
particular, the law cannot be claimed for every retained target strategy:
players can deliberately correlate timing with hidden information. Forward SE
extension selects a suitable implementation and must still defeat deviations
from it.

Existing `LocalResponse.transcript_eq_iteration` handles execution coalescing
when there is no incoming information. It does not erase other players' recall
or prove SE preservation. `FinDist.splitKernel_project` and `split_prob` supply
the finite action-splitting algebra, but the required timing transcript and
posterior factorization are not yet instantiated.

## When stronger timing assumptions would be needed

If a desired backend instead enforces one canonical send opportunity, it needs
an authenticated opportunity marker or a public clock boundary visible to its
audit. Existing `environmentRecall` is scheduler recall, not player observation;
`TrafficRecord` does not record its cursor. Merely assuming that cursor is
public would change the observation model.

A public service phase could identify opportunities without an exact private
scheduler index, but must be implemented or explicitly assumed. Hiding the
channel through batching requires hiding intermediate pending observations too.
Neither mechanism is necessary merely because the checked timing channel
exists. First attempt the conditional-independent refinement; require a
stronger backend only for an actual failed strategic or service obligation.
