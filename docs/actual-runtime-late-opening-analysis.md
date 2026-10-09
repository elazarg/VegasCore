# Late openings in the actual Vegas runtime

See [the standard-runtime status](standard-runtime-se-status.md) for the
distinction between the checked calendar SE theorem, asynchronous Nash
correspondence, narrower SE comparisons, and the checked
[native uniform SE obstruction](commit-reveal-research/native-se-obstruction.md)
under partial pending observations. The fully public comparison below remains
a separate positive result.

The checked `LateLeak` impossibility theorem does not yet imply an
impossibility theorem for the actual Vegas compiler on a fully observed public
mempool. Its distinguishing feature is that a failed opening sent at the first
late turn reveals the committed bit, whereas one sent at the second late turn
does not. If the listener reads both failed packets before answering, that
feature disappears. In fact, the resulting fully public version has a
preserving sequential equilibrium in the same parameter regime as the negative
theorem. The native comparison-model SE construction is checked in
[CompleteObservationPreservation](../Vegas/Examples/LateLeak/CompleteObservationPreservation.lean).
It covers all behavioral continuation deviations and uses one common sequence
of fully mixed Bayes assessments.

A stronger checked comparison theorem covers **every** late inclusion
probability $0<q<1$: when $R>0$, the failure forfeit is $D=2R$ and the
dropped-packet charge is zero, every SE of the intended comparison game has
its complete initialized terminal-state law preserved by a public-traffic
target SE. The forfeit is part of both games' utility; it is distinct from
an audit escrow added by the compiler. The proof is in
[CompleteObservationCostPreservation](../Vegas/Examples/LateLeak/CompleteObservationCostPreservation.lean).
Its intended source forces opening. The source language's lawful FALSE choice
is covered by the broader paper theorem below, not silently removed from a
checked source-language adapter.

This distinction concerns what opponents actually observe. It does not depend
on declaring pending messages invisible or on treating a reveal as something
other than a message.

The broader [disclosure-phase paper proof](full-public-disclosure-phase-preservation.md)
allows any finite number of late opportunities with arbitrary inclusion
probabilities in $[0,1]$, lawful source withholding and arbitrary receiver
failure preferences. With a failure forfeit larger than the sender's base
payoff range, it implements every source Nash outcome by a target SE, hence
every source PBE and SE outcome. Its protected opening succeeds surely; its
later transmissions need not. It is not yet a checked compiler theorem.
The strongest paper version also permits correlated private receiver types
with full joint support and inclusion probabilities depending on the disclosed
value. A [restricted composition proof](public-reset-phase-se-preservation.md)
covers genuine public subgames already present in the source; it does not
introduce automatic disclosure of withheld secrets.

If even protected honest publication has unavoidable failure before the fixed
horizon, [the probabilistic-runtime analysis](probabilistic-runtime-preservation.md)
gives a different obstruction: exact publication-law preservation is impossible.
This now has a checked instantiation for every native behavioral strategy of
every nonempty compiled program under an explicit probabilistic public
controller, retaining the actual initialization and typed readout.
It also explains why a highly reliable service does not, by itself, guarantee
a nearby exact equilibrium for each source equilibrium.

## The closest existing runtime example

[CommittedResolutionService](../Vegas/Examples/CommittedResolutionService.lean)
already supplies an actual source program, setup, scheduler, and checked
asynchronous service contract. Alice and Bob each own an initial committed
Boolean. After a sample, the program reveals Alice's value and then Bob's.
Alice has a protected activation at clock zero, a later activation at clock
one, and another activation after her event expires. A coin includes her late
packet with probability `3/4`; a later command includes her latest packet
after expiry. Bob is activated afterward.

The module proves the service's opportunity, protected inclusion, and
completion obligations over all raw legal histories. It also proves that
prescribed packets are clean under the actual signed terminal audit, and that
a canonical first opening of `true` fixes Alice's successful public output
under every later raw player policy. Its `mixed_bob_reach_bound` quantifies
over all raw policies, including noncanonical action aliases. These are actual
execution facts; they are not a complete compiler SE theorem or a complete
actual-runtime SE counterexample.

The final Bob decision also has checked adapters over every legal RAW prefix:
[BobAudit](../Vegas/Examples/CommittedResolutionBobAudit.lean) proves that the
canonical response succeeds and has zero owner audit charge even after dirty
Alice traffic; [BobFailure](../Vegas/Examples/CommittedResolutionBobFailure.lean)
proves that an incorrect or silent response fails by the actual horizon.
[BobDecision](../Vegas/Examples/CommittedResolutionBobDecision.lean) reduces
the entire native behavioral continuation to its current response lottery
and the actual passive physical suffix.
[BobReadout](../Vegas/Examples/CommittedResolutionBobReadout.lean) proves
complete typed readout existence at that horizon and identifies the entire
source state for continuations with the same Bob result.
[Forfeit](../Vegas/Examples/CommittedResolutionForfeit.lean) computes the
ordinary compiled own-failure utility on those states. These supply execution
and payoff ingredients for a native sequential incentive proof; they do not
yet supply its belief-local capstone or a general compiler theorem. The
concrete service's pending observation rule is still `pure ∅`, with stale
packets subsequently exposed in the public ledger.

An important feature of this example is its command after Alice's expiry.
`MessageNetwork.includePending` appends the stale packet to the public ledger even when the
application rejects it. Consequently, `leaks = pure ∅` in this example does
not mean that a failed emitted opening remains secret from Bob. A proposed
negative proof must use the ledger, as well as pending observation and the
public application output.

## What the runtime really guarantees

The [asynchronous service contract](../Vegas/Pending/ReactiveAsyncContract.lean)
is deliberately weaker than a fixed admission calendar. `Opportunity` provides
an owner activation during a readiness episode. `ProtectedInclusion` provides
a receipt for an owner's sole identifier once the clock passes its send time
plus its inclusion bound, while the event remains unfinished. A receipt may
say `false`; the contract is not an unconditional acceptance promise.

Suppose an event expires at clock four and its inclusion bound is two. A
single packet sent at clock two can be omitted until expiry without violating
the guarantee: before expiry, the strict inequality `sent + bound < clock`
has never held, and after expiry the event is finished. A packet sent at clock
three has even less protected time. Thus realistic late admission uncertainty
is permitted by the existing interface.

The readiness token is an event credential derived from public prerequisite
completion. It carries no signed creation time or send time. It prevents a
packet issued before readiness from acquiring a valid future credential; it
does not certify that a packet was issued inside the protected inclusion
window.

The first certified opening sent while the event is ready and before its
deadline can satisfy `ConformantResponse` even outside the protected inclusion
window. The clear risk menu therefore cannot automatically be described as
the menu of protected transmissions. Later risk latching also does not change
the final audit verdict of a packet that was accepted.

[CommittedResolutionRecovery](../Vegas/Examples/CommittedResolutionRecovery.lean)
checks this distinction in an initialized source program. Its support-refined
scheduler satisfies the original asynchronous contract, accepts a conformant
opening outside the protected inclusion window, and reaches terminal plays
with an accepting receipt and exactly that submitted packet. On those plays,
every authentic audit backend charges zero for every deposit size. This
refutes deriving a positive penalty floor for all late choices from the
contract alone. It is an operational fact, not an SE nonpreservation theorem.

The [settled verdict](../Vegas/Pending/ReactiveSettledVerdict.lean) reads the
signed packet and the final contract record. It does not read the send-time
view. An accepted, certified opening whose guards accept can be permitted
even when it was sent late. A packet rejected or left pending after its event
settles is forbidden. If the latter is collected with probability $a$ from
escrow $E$, a late opening accepted with probability $q$ can incur an
additional expected audit loss of only $(1-q)aE$, compared with $aE$ for
an inevitably forbidden packet. A recovery-floor proof must account for
that factor and for later raw continuations.

## Pending packets do not disappear on expiry

[MessageNetwork](../Interaction/MessageNetwork.lean) retains every submitted
envelope in its input log. Its carrier operations either leave that envelope
pending or move it to the ledger. Event expiry is an application operation;
it does not remove the envelope from the carrier. There is no network
discard command in this runtime. Leaked packet knowledge also persists.

The player observes leaked envelopes and the ledger. Selecting all currently
pending identifiers at the listener's final activation therefore exposes every
foreign envelope submitted so far, including an opening sent at the second
late turn. An opening included but rejected is already visible in the ledger.
The operational lemma in
[CompletePendingObservation](../Interaction/CompletePendingObservation.lean)
expresses this using the existing `UniqueIds` and `PendingOrPublished`
invariants. It does not give the player access to the carrier's input log.

[ReactiveCompleteObservation](../Interaction/ReactiveCompleteObservation.lean)
supplies the corresponding actual reactive-history adapter: complete pending
observation makes every previously submitted foreign envelope visible at an
actual raw player decision. The legal trace discharges the identity and
retention invariants; neither conformant play nor successful application
acceptance is assumed.

The general observation rule is stateless: it depends on the observer and the
current pending pool, not on the clock or the observer's previous sample.
Selecting only the first late packet by its identifier is not a valid
derivation from full public observation. Both first and second transmissions
can have sender serial zero when no earlier packet was emitted. A negative
embedding that requires different visibility must model and justify an actual
transmission or observation lag, a selective communication channel, or an
earlier irreversible listener choice. It cannot simply erase the second
packet at expiry.

## A preserving SE when both failed late openings are public

Consider the existing finite `LateLeak` game with one information change.
The listener learns `v` after **either** emitted opening fails. It also sees
which turn sent the packet and whether inclusion succeeded. If the sender
never sent, it learns no bit. Giving the listener the complete public timing
transcript does not affect the following construction: the sender's chosen
timing probabilities are independent of both its bit and its private label.

Write `R > 0` for the reward, `D` for the failure forfeit, `c ≥ 0` for the
dropped-opening charge, and `0 < q < 1` for the common inclusion probability
of either late turn. The prior remains `P(v=1)=9/20`, with the independent
label uniform among A, B, and C. Assume the negative theorem's margins:

```
(1-q)c < q(D-R)
R/2 < qR - (1-q)(D+c).
```

They imply `D>R`. Define the following assessment:

- The sender opens at the protected turn.
- At the first late turn, it sends with probability `1/2`, for every type.
- At the second late turn, it sends, for every type.
- After every successful opening, the listener takes the safe answer.
- After every emitted failed opening, the listener guesses the observed bit.
- After never sending, the listener guesses zero.

The two late behaviors prescribe play at information sets off the equilibrium
path. They are part of the SE assessment, not additional on-path transmissions.

**Consistency.** Choose any sequence `ε_n ↓ 0` with `0<ε_n<1`. At the protected
turn let every type send with probability `1-ε_n`; at the first late turn use
probability `1/2`; at the second use `1-ε_n`. At each listener information set,
mix its prescribed answer with `ε_n` times a fully supported distribution on
its legal answers. These profiles are fully mixed and converge to the stated
strategy. Their Bayes beliefs have label probabilities exactly `1/3` at every
success information set, including both late turns. At emitted failure the
bit is known. At never sending, the bit posterior is exactly its prior,
because all sender timing factors are type independent. Thus their Bayes
beliefs converge to the stated beliefs even at zero-probability information
sets. This verifies consistency constructively.

**Listener rationality.** The safe payoff is `2/5`, while every label guess
has expectation `1/3`. Truthful bit guessing is optimal after a visible
failed opening; guessing zero is strictly optimal after never sending,
because `11/20 > 9/20`.

**Second late turn.** Let `F(v,s)` be the sender's reward from a truthful bit
guess after failure and `W(s)` its reward from a zero guess after never
sending. Each lies in `[0,R]`. Sending has payoff

```
qR/2 + (1-q)(F(v,s)-D-c),
```

whereas never sending has payoff `W(s)-D`. The worst difference occurs for
`s=B, v=1`, and equals

```
q(D+R/2) - R - (1-q)c.
```

The second margin gives

```
q(D+R/2) - R - (1-q)c
  > D - (1+q)R/2
  > 0.
```

Hence sending is strictly optimal for every type at the second late turn.

**First late turn.** Sending now and waiting to send at the second turn have
identical payoffs: both have the same inclusion probability, the same safe
success reply, and the same truthful failed-opening reply. Mixing is optimal.

**Protected turn.** Protected opening pays `R/2`. Every late continuation
pays at most

```
qR/2 + (1-q)(R-D-c) < R/2.
```

Thus protected opening is strictly optimal. The finite game has perfect
recall, and these checks also verify all continuation deviations: after
deferring, the sender's best second action is send and its first timing
choice is immaterial; the listener has only its final answer to choose.

This assessment is a sequential equilibrium and has exactly the protected
opening/safe-answer outcome law of the old intended game. It is a positive
result for this public-observation game family. It is not a universal theorem
that a public mempool preserves SE, nor a claim that all its equilibria have
the protected law. Its role is to show that the particular negative
mechanism cannot be exported by forgetting physically visible traffic.

The direct sufficient inequalities for this construction are weaker than the
negative theorem's margins:

```
R ≥ 0,
D+c > R/2,
q(D+R/2) > R+(1-q)c.
```

The checked comparison-model core in
[CompleteObservation](../Vegas/Examples/LateLeak/CompleteObservation.lean)
retains public turn and resolution metadata and own-action recall, constructs
native fully mixed Bayes approximations and their consistent strategy limit,
and proves the sender's exact primitive incentive inequalities under these
direct margins. [CompleteObservationValue](../Vegas/Examples/LateLeak/CompleteObservationValue.lean)
checks every whole behavioral sender replacement at every retained history.
[CompleteObservationPosterior](../Vegas/Examples/LateLeak/CompleteObservationPosterior.lean)
checks the three-label posterior and the withholding prior from one explicit
common Bayes tremble sequence.
[CompleteObservationPreservation](../Vegas/Examples/LateLeak/CompleteObservationPreservation.lean)
combines these with the listener's native final-decision reduction into an
existential SE theorem. These results use the refined information model,
including public resolution metadata and own-action recall. They do not assume
the desired beliefs as a premise of the SE existence theorem.

Complete visibility at the decision is a substantive assumption. With bounded
propagation delay, a public opening may arrive after the receiver's irreversible
choice. [The propagation-lag analysis](propagation-lag-se-boundary.md) gives an
explicit timed comparison model and distinguishes it from a checked full raw
runtime embedding. The negative observation pattern need not require permanent
secrecy; a protocol must account for when the receiver learns the packet.

## What remains before an actual compiler theorem

The old intended `LateLeak` game forces protected opening. Vegas source
reveals allow the owner to choose `false`, immediately resolving the source
publication as failure. That legitimate source alternative cannot be replaced
by a runtime wait while keeping the intended game unchanged. A source-to-runtime
capstone must represent its actual source menu and compare every source SE,
including equilibria using or mixing with legitimate withholding when those
payoffs permit it.

Preserving the initialized outcome law is also weaker than copying an
arbitrary source assessment's off-path beliefs. With lawful source
withholding, type-specific source trembles can produce arbitrary beliefs after
failure. The uniform target trembles above choose the prior belief after never
sending, and do not copy all those assessments.

Complete observation suggests a constructive strengthening. Keep protected
deferral trembles type independent, but use second-turn withholding trembles
proportional to a desired source failure posterior divided by the positive
type prior. The never-sent fiber then converges to that desired posterior.
Second-turn success weights still converge to a type-independent factor,
because withholding vanishes, so success label beliefs remain uniform. Zero
posterior coordinates can be approximated by smaller positive trembles. This
works because the public transcript distinguishes a transmitted failed
opening from never sending. The selective-observation counterexample merges
second-turn failure with never sending, preventing that separation. This
weighted construction still needs a checked comparison-model theorem and a
source execution adapter; it is not established by the uniform construction.

The full raw runtime also permits multiple packets, wrong events, malformed
contents, relayed evidence, prepared-handle allocations and noncanonical
aliases. Repeated identifiers can void the sole-identifier inclusion
guarantee. An early listener activation used as a passive probe still gives
the listener its full raw action interface; it is not automatically a
nonstrategic observation step. A probe packet can modify candidate storage or
later acceptance even if it has no valid readiness token. Any claimed
embedding must cover these branches and their conditional beliefs.

For enforcement, a finite deposit is useful only when there is a positive
**incremental** charge probability for the first excluded action, uniformly
over its possible continuation policies. An already incurred single-escrow
charge is not an additional penalty for every later action. Accepted late
openings can be clean under the settled verdict, so neither a send-time
argument nor the event-only credential alone supplies this premise.

The strongest next positive target is therefore an actual retained-action
runtime with complete observation, canonical submission ownership, and a
source-information adapter, followed by a proved incremental enforcement
extension to the raw menu. The strongest negative target must exhibit an
actual source program and scheduler satisfying the all-history service
contract, compute the listener's true leaked-and-ledger information, and
exclude every raw SE with the required source outcome law. The existing
operational lemmas reduce this work substantially; they do not yet finish
either capstone.
