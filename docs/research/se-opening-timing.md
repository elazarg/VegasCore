# Opening time: a real channel, not an automatic SE obstruction

## Checked native witness

`Vegas/Examples/OpeningTimingChannel.lean` uses the existing initialized graph,
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
   or known-envelope replays, including the phase's unpublished canonical
   opening; they cannot make another meaningful source decision.
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
or prove SE preservation. `splitKernel_project` and `split_prob` supply
the finite action-splitting algebra. The concrete one-phase transcript and
posterior factorization below do not yet establish the multi-phase SE result.

## Checked ingredients for choosing at the final opportunity

[`DeferredChoice.lean`](../../GameTheoryExtensions/Math/Probability/DeferredChoice.lean)
proves a finite behavioral construction. For an original opening probability
`q < 1` and a distribution `t` over opening opportunities, its conditional
opening probability at opportunity `k` is

```
q * t(k) / (1 - q * sum_{j < k} t(j)).
```

`deferredHazard_survival`, `deferredHazard_first` and `deferredHazard_never`
prove that these behavioral choices give first-opening mass `q * t(k)` and
withholding mass `1 - q`. `deferredHazard_value` proves the corresponding
payoff equality when only the binary outcome affects payoff. Positive `q < 1`
and fully supported timing give positive opening and waiting probabilities at
every opportunity.

Use `t = (1 - epsilon) * finalOpportunity + epsilon * uniform` in the common
source perturbation sequence. `finalTiming_fullSupport`, `finalTiming_tendsto`
and `deferredHazard_tendsto_last` prove convergence to waiting at every earlier
opportunity and using the source opening probability at the final one. This
also covers source probabilities tending to one; the denominators converge to
one. These are probability results, not yet an instantiated roster SE theorem.

[`DeferredObservation.lean`](../../Interaction/DeferredObservation.lean) proves
that an owner's actual passive activation adds no information if every foreign
pending envelope is already known or published. Unpublished envelopes authored
by that owner are allowed. Other players may still read those envelopes; the
result uses the original arbitrary observation rule and delayed inclusion.
`include_pending_published_or_selected` also proves that including one envelope
makes every remaining replay of its identifier already published.

These facts support the following remaining proof obligations:

- Before a first opening, show the owner's posterior and available source
  choices remain unchanged. Waiting until the final opportunity then has the
  original source mixture's value, while opening earlier has its true-action
  value.
- After that opening, prove protected final inclusion fixes the source outcome
  despite permitted silence and exact-envelope replays. A retained rule with
  at most one **fresh envelope** per event is a candidate: replaying that same
  envelope, even before publication, need not be forbidden. Fresh duplicate
  submissions and replay are different attribution obligations.
- Propagate the checked one-phase conditional factorization below across source
  decisions, throughout one fully mixed sequence. An arbitrary sampler may
  respond to pending-copy multiplicity, so the coupled auxiliary starting
  transcript must be retained in this induction.

No inclusion after every owner visit is assumed here. Adopting that service
would be an additional backend restriction and would eliminate some in-flight
observation windows. The intended route retains a protected final inclusion.

The distribution factorization now also holds for the **actual existing
runtime evaluator**:
[`runInteractionPlan_scheduledMixture`](../../Vegas/Pending/ReactivePolicyMixture.lean)
realizes a planned opening slot, or never opening, as one behavioral policy.
Its complete execution law is the corresponding mixture of unchanged
`runInteractionPlan` laws. The plan, other player policies, passive sampler and
network policy are arbitrary. The proof reuses the existing private-strategy
realization; it adds no runtime memory or second evaluator.
[`policyMixture_posterior_dormant`](../../Interaction/ReactivePolicyMixture.lean)
proves that a choice unused before a phase retains its original mixing law at
that phase, including with nonempty earlier own recall.

[`ReactiveOpeningWindow.lean`](../../Vegas/Pending/ReactiveOpeningWindow.lean)
now instantiates actual canonical opening and known-envelope replay policies.
`openingWindow_coupling` proves equal complete auxiliary/focal transcript laws
across hidden states with coupled auxiliary starts and equal focal source
information. This works for arbitrary finite rosters and observation rules,
including repeated activations and unpublished replay.
[`openingOutcome_posterior`](../../Vegas/Pending/ReactiveOpeningPosterior.lean)
then proves the exact posterior identity for an arbitrary correlated law of
hidden initial execution and source disclosure result: conditional on that
result, timing/sampling/replay adds no further update. Coupling a fixed auxiliary
start is proved; propagation of its distribution across successive phases is
still required.

[`scheduledMixture_after_open`](../../Interaction/ScheduledOpening.lean) and its
runtime instance `openingWindowMixture_after_open` prove that every supported
first opening makes subsequent replies replay/silence.
[`ScheduledOpeningSupport.lean`](../../Interaction/ScheduledOpeningSupport.lean)
proves positivity at all lawful waiting histories.
[`ScheduledOpeningPosterior.lean`](../../Interaction/ScheduledOpeningPosterior.lean)
computes the exact latent posterior and hazard from actual own recall, then
proves the common policy limit before and after opening. It retains the stop
rule at zero-probability early-opening histories; a zero-weight latent mixture's
arbitrary conditional fallback need not equal that limit. Instantiating these
local facts at every actual roster information site, constructing one common
consistent assessment across phases, and proving sequential incentives remain
open.

## Why general coalescing is insufficient

Action coalescing does not preserve sequential equilibrium in general.
[Clark, Fudenberg and He (2022), Section 3.2 and Figure 4](https://kevinhe.net/papers/induction.pdf)
give two games with the same reduced normal form: splitting a choice among
`Out`, `In1` and `In2` into `Out/In` followed by `1/2` removes an SE outcome.
The proposed positive result therefore depends on the binary deferral
structure: waiting keeps both source outcomes available, the owner acquires
no new source information while undecided, and an opening fixes revelation.
Reduced-normal-form equivalence alone cannot discharge these obligations.

## When stronger timing assumptions would be needed

If a desired backend instead enforces one canonical send opportunity, it needs
an authenticated opportunity marker or a public clock boundary visible to its
audit. Existing environment recall belongs to the scheduler, not player observation;
`TrafficRecord` does not record its cursor. Merely assuming that cursor is
public would change the observation model.

A public service phase could identify opportunities without an exact private
scheduler index, but must be implemented or explicitly assumed. Hiding the
channel through batching requires hiding intermediate pending observations too.
Neither mechanism is necessary merely because the checked timing channel
exists. First attempt the conditional-independent refinement; require a
stronger backend only for an actual failed strategic or service obligation.
