# Private-seed signalling in a first commitment phase

**Native counterexample: proved ($a<m$) · stronger-forfeit target open.**

The [three-owner argument](se-strong-exclusion-signalling.md) separately tests
fixed exclusion loss above the nonexcluded reward range. Its checked native
milestones are distinguished from the remaining off-path preparation argument
and full native equilibrium certificate.

The issue is that a player can withhold useful information. Alice has two late
submission times; a hidden fair coin determines which succeeds. If Bob sends
early, Alice can learn the successful time from whether his packet is visible
at her callback. If Bob waits, she cannot do better than success probability
1/2. Bob benefits from Alice's failure, so after Alice initially waits, Bob
strictly prefers to withhold this signal. Alice can then profit by waiting too.
The honest game's payoff is zero, whereas this deviation earns at least 1/4.

Observations are allowed to add knowledge throughout this argument. Independent
coins and a scheduler that never reads packet values do not, by themselves,
prevent players from controlling which useful observations others receive.
The native certificate uses the existing runtime definitions and formal
counted-service assumptions; no new restriction on observations is assumed.

This note tests Theorem 3 of [the preservation argument](se-preservation-commit-reveal.md).
Under the literal causal reading of its S1--S3 bullets, independent event
seeds do not prevent players from changing another player's information
about its seed. The finite timing game below has no preserving sequential
equilibrium. It extends to the raw audited game when service privacy is
imposed on permitted counted histories, as in the existing formal predicates.
An all-raw quotient by only the Boolean count-well-formedness verdict is
incompatible with timely native protected inclusion, as proved below.
The packet-content equivalence and the service-information claim in prose
must be distinguished from the existing formal predicates; charge dominance
alone proves neither of them.
The installed native Lean fixture proves the obstruction under the formal
counted-service predicates. It does not close a checklist box, settle the
all-raw content reading, or change any target, semantics or hypothesis.

The native fixture has a checked honest source SE and the full raw contract
[`Vegas.Examples.CommitSeedSignalling.scheduler_asyncContract`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingAsyncService.lean#L26): opportunity
delay zero, protected receipt bound five, and completion within 64 commands.
The unfinished-play bound is 55, including malformed submissions, retries and
exhausted recovery. The conditional native late-acceptance bound is checked
by [`Vegas.Examples.CommitSeedSignalling.original_nohelper_acceptance_half`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingHalfSuccess.lean#L347);
the exact earlier-state/hidden-coin/final-state joint is retained separately
by [`Vegas.Examples.CommitSeedSignalling.bobPrefixFinalJoint_physical`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingBobJoint.lean#L53).
The initialized bound
[`Vegas.Examples.CommitSeedSignalling.bob_initialized_weighted_half`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingInitializedHalf.lean#L239) retains
any earlier physical event jointly, so Alice's earlier delivery need not be
independent of the updated hidden remainder. Alice's corresponding initialized
bound is [`Vegas.Examples.CommitSeedSignalling.alice_initialized_half`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingAliceInitializedHalf.lean#L154).
The actual Bob quiet deviation has exactly the initialized counted experiment's
value ([`Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_initialized_value`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingBobQuietInitialization.lean#L99)),
retaining Alice's later assessed strategy even at off-path decisions.
[`Vegas.Examples.CommitSeedSignalling.raw_equilibrium_own_clean_terminal_charge_zero`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingOwnContinuation.lean#L160)
also proves that the assessed continuation never charges an owner with a clean
own past, without restricting the other owner's raw traffic.
The exact private clock-calendar predicate holds for the installed family
([`Vegas.Examples.CommitSeedSignalling.family_privateActivationCalendar`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingPrivateCalendar.lean#L59)),
including exhausted attempts. Actual original correct-seed acceptance is at
least 1/2 for either owner's fixed late deviation
([`Vegas.Examples.CommitSeedSignalling.fixed_late_acceptance_probability`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingCorrectSeedProbability.lean#L76)).
The final joint acceptance bound
[`Vegas.Examples.CommitSeedSignalling.initialized_joint_acceptance_half`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingJointAcceptance.lean#L85)
retains Alice's original receipt across the complete continuation.
The opening incentive comparison
[`Vegas.Examples.CommitSeedSignalling.counted_successful_publication_wait_not_supported`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingPublicationChoice.lean#L108)
excludes WAIT at an actual callback with a successful stored binding: the
whole assessed continuation gives -1 after withholding and at least 0 after
opening, uniformly across the full raw information fiber. Other owners' past
and future traffic is unrestricted there.
The full existing counted binding-success predicate is checked by
[`Vegas.Examples.CommitSeedSignalling.family_privateBindingSuccess`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingPrivateBindingSuccess.lean#L43), including
arbitrary preparations and evidence in original and retry attempts.
[`Vegas.Examples.CommitSeedSignalling.raw_helper_clock_two_information_fiber`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingHelperFiber.lean#L120)
and [`Vegas.Examples.CommitSeedSignalling.raw_recalled_helper_information_fiber`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingHelperFiber.lean#L156)
establish Alice's helper readout across every history in the full raw information
fiber and every supported original seed there.
Both fixed late deviations have probability at least 1/4 of own original
acceptance with the opponent's original binding missing
([`Vegas.Examples.CommitSeedSignalling.alice_fixed_late_exclusive_acceptance_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingUnilateralDelivery.lean#L25)
and [`Vegas.Examples.CommitSeedSignalling.bob_fixed_late_exclusive_acceptance_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingUnilateralDelivery.lean#L68)).
Missing original receipts imply the actual terminal failed-publication bit
([`Vegas.Examples.CommitSeedSignalling.initialized_missing_original_binding_publication_failed`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingPublicationReceipts.lean#L348)).
Accepted original bindings of a fixed proper late owner protect it through
the entire actual recovery and publication continuation
([`Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_original_binding_survives`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingProperSurvival.lean#L190)).
The resulting native expected payoff is at least 1/4 against any counted opponent
who initially waits
([`Vegas.Examples.CommitSeedSignalling.initialized_fixed_late_netPayoff_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingProperPayoff.lean#L20)).
The same bound holds for Bob's whole deviation at his actual quiet information
set, retaining Alice's assessed continuation even off path
([`Vegas.Examples.CommitSeedSignalling.bobQuiet_fixedLate_context_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingQuietPayoff.lean#L20)).
Consequently a preserving equilibrium cannot have Bob always wait there
([`Vegas.Examples.CommitSeedSignalling.preserving_equilibrium_bobQuiet_not_wait`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingInitialDeviation.lean#L69)).
Full raw information-set comparisons force Alice to wait at the wrong time
and submit openable material at the useful time. Her actual assessed opening
continuation then survives. Thus every permitted early Bob packet makes Alice
survive, giving Bob at most zero, whereas his whole waiting deviation gives
at least 1/4. His waiting behavior is forced
([`Vegas.Examples.CommitSeedSignalling.bobQuiet_counted_decoded_wait`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingBobQuietChoice.lean#L125)).
Consequently every native sequential equilibrium gives Alice expected payoff
at least 1/4
([`Vegas.Examples.CommitSeedSignalling.native_equilibrium_alice_payoff_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingNonpreservation.lean#L19)).
One fixed honest source sequential equilibrium has no preserving native
sequential equilibrium
([`Vegas.Examples.CommitSeedSignalling.exists_honest_sequentialEquilibrium_without_native_preservation`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingNonpreservation.lean#L59)).
These are actual native theorems, with the original assessment strategies,
beliefs and scheduler posterior retained, including off-path decisions.

## Program and payoffs

Start in the empty context. Alice and Bob each commit a Boolean value,
with guard TRUE, in the first commitment phase. Their two reveals form
the next phase. There are no samples or private input types. Each owner has
one event in each phase, so concurrent execution respects information and
same-owner order. Use the actual phase-reset rule for missed bindings.

Fix W>2 epsilon>0. A nonexcluded player receives W if the other player's
reveal fails, and 0 otherwise. An excluded player receives the constant
a=-epsilon. Thus m=0 and a<m. Payoffs ignore the committed bits. In the
honest game both reveals always succeed and every payoff is 0, including
after every honest continuation. Choose independent uniform Boolean choices
at the two commitments. This is a genuine honest sequential equilibrium:
the strategy is completely mixed on its honest menus, its constant sequence
has its Bayes-consistent beliefs, and every continuation has value 0.
Its public law has independent fair revealed bits, certain joint success
and payoff vector (0,0).

This tests Theorem 3's stated bound a<m. It does not refute the stronger
requirement in the asynchronous checklist that the forfeit exceed the payoff
range: the example needs W>2 epsilon, whereas that requirement would need
epsilon>W.

Take certain audit collection and deposit K>W+epsilon. A first charged packet
then gives net payoff at most W-K<-epsilon. An entirely silent remaining
continuation guarantees at least -epsilon without a charge. At every
information set with a known uncharged own past, a first charged action is
strictly inferior. This covers
extra packets, malformed calls, foreign-event packets and disallowed evidence.
It does not assume that already-charged players incur a second deposit loss.

## Original builder law

The initial two bindings become ready together; translate their readiness
clock to 0. Their common opportunity delay is 0, protected-inclusion bound
is 5, and deadline duration is 6. Independently sample fair bits x_A and x_B
as their original event seeds. The remainder is deterministic.

At clock 0, activate Alice and then Bob. No packet is included between these
two callbacks. At every callback show the player all pending packets of the
other owner. This is a content-blind leak rule. An EARLY packet is a packet
emitted by that owner at clock 0 in this original attempt; classify it by its
actual owner, attempt and emission clock, not by its handle or private meaning.

Use these fixed blocks, while the original attempt remains open:

| Clock | First slot | Fixed middle slot | Third slot |
| --- | --- | --- | --- |
| 2 | activate A if x_A=0 | include B's EARLY packet, if any | activate A if x_A=1 |
| 4 | activate B if x_B=0 | include A's EARLY packet, if any | activate B if x_B=1 |

An unavailable activation or absent helper is replaced by an identity
WAIT, which does not advance the public clock. The middle slot executes
even if its associated owner has already completed its binding. Never read
a resolved event's seed to decide an activation. Stutters produce neither
an observed packet nor an own callback; the observation rule exposes no
global command counter. The native interface has this distinction between
identity WAIT and the separate clock-advance command.

There is one further callback for A at clock 3 and for B at clock 5, if
their binding is still ready. For a well-formed first binding packet:

- an EARLY packet is included in its fixed middle slot, for either seed;
- A's packet sent at 2 is included exactly when x_A=0, and one sent at 3
  exactly when x_A=1;
- B's packet sent at 4 is included exactly when x_B=0, and one sent at 5
  exactly when x_B=1.

At clocks 2 and 4 the eligible late packet is included after the entire
three-slot block, with no extra inclusion between its first and middle slots.
At clocks 3 and 5 it is included immediately after its callback.
The marker handler never uses a LATE packet as a helper. At clock 6 expire
unresolved original bindings, then execute the real close/reset. If the
attempt closes earlier, both original bindings are already resolved: retire
this routine and continue below.

Predraw the seeds of ALL possible full attempt/event addresses independently
at initialization, including retry and reveal addresses; their fixed laws
may be degenerate. On all subsequent retries and reveal phases, give EVERY
currently ready owner its first callback and immediate inclusion before any
clock advance, then expire anything unresolved at its deadline. Switch to
this continuation as soon as the original full attempt retires; never finish
old clock padding after a new event becomes ready. Use fresh independent event
seeds at those addresses, from that SAME original draw. Correct Boolean
commitments and openings therefore have sure service. Excluded owners'
events are automatic failures.

The builder is also specified on raw deviations: process each EARLY envelope
in its designated inclusion slot, receiving the contract's acceptance or
rejection verdict. Late own-event envelopes are included only if their
EMISSION clock equals that event's seed-selected eligible clock, in serial
order. A wrong-clock packet stays unaccepted; it cannot wait in the network
and land at the later eligible clock. A packet without valid content
or readiness cannot cause an accepting completion; foreign authors cannot
complete the owner's event. Expiry still completes every unresolved event.
Fix finite raw payload, evidence, serial and candidate-slot bounds with
enough fresh slots for every scheduled callback. There are finitely many
scheduled callbacks, each emits at most one envelope, and every retry removes
an owner. This gives both finite branching and a fixed finite horizon large
enough for every legal raw run, not bounds chosen after the strategy.

There is at most one callback to a given owner at each original clock: the
two seed-controlled polls in one block are mutually exclusive. Thus the
eligible late inclusion selects at most one actual envelope, even on raw
histories; it does not need extra inclusion slots for same-clock packets.

## Variant with deferred late receipts

The same payoff obstruction can hold even if future callback CLOCKS for the
original coordinate reveal no additional seed information under any fixed
own emission plan. Modify only these four inclusion slots in the builder above:

| Slot | Modified command |
| --- | --- |
| After the clock-2 polling block | WAIT instead of including A's late packet |
| After A's clock-3 callback | Include A's packet emitted at 2 if x_A=0, or at 3 if x_A=1 |
| After the clock-4 polling block | WAIT instead of including B's late packet |
| After B's clock-5 callback | Include B's packet emitted at 4 if x_B=0, or at 5 if x_B=1 |

The selectors use the packet's actual EMISSION clock. In particular the
clock-3 inclusion must still select a clock-2 packet when x_A=0; this is not
a rule admitting only packets emitted at the current clock. Leave both
EARLY helper inclusions and immediate namespace switching unchanged.

No original A packet can accept before its clock-3 callback: late packets
are considered only after that callback, and its EARLY packet only at 4.
Private submission changes no cut or readiness timer; foreign packets cannot
complete or exclude A. Hence on EVERY legal raw run its original callback
word is exactly [0,2,3], including after a SEND at 0 or 2.

B's only possible accepting completion before its clock-5 callback is its
EARLY packet at 2. Its admission is determined by the physical first-call
content and state, before x_B is read, and is independent of x_B. If it
accepts, B's original callback word is [0]. Otherwise its word is [0,4,5]:
the clock-4 late inclusion is now WAIT, and the sole late selection follows
its clock-5 callback. No unresolved binding can retire or exclude its owner
before these callbacks. Thus for fixed other randomness and a fixed chosen
continuation, the two local seeds give the same remaining original callback
clocks at every corresponding unsent input. This holds for raw responses,
not just for the prescribed SEND/WAIT choices.

The full inputs still differ. At A's clock-2 callback, a B EARLY packet is
pending when x_A=0 and already receipted when x_A=1. Its information value
now concerns only WHICH EMISSION will accept later. A proper SEND2 accepts
at 3 exactly for x_A=0; after WAIT2 a proper SEND3 accepts exactly for x_A=1.
The extra callback after SEND2 cannot provide a count-clean repair. B's
clock-4 helper experiment is identical with clocks 4 and 5.

The acceptance bits, raw admission quotient, and budget are unchanged.
An intervening own response can prepare fresh cells but cannot change a
frozen candidate's meaning, accepted map, readiness or handle-used status.
Eligible admission therefore persists until its selection; all late
selections still precede deadline 6. Protected EARLY receipts remain at 2/4,
with the same completion/sole-packet exceptions. The routine still uses 22
commands, at most six original callbacks and the same protected tail.

The proof below applies without changing its inequalities. With a helper,
proper SEND2 now guarantees acceptance after the extra clock-3 callback;
silence there is forced once the free packet is spent. Without a helper,
the first late send probability still bounds the two acceptance chances by
q and 1-q. A's delivery is determined by the clock-3 inclusion, before B's
clock-4 polls, so the joint bound and deviation value W/4-epsilon/2 remain.

This variant rules out sufficiency of future ORIGINAL-EVENT callback-clock
experiments under fixed own emission plans. The precise seed comparison
holds the other original randomness fixed, as above. It does not say an
arbitrary adaptive policy generates the same clock law across different
full inputs: at B0, the policy SEND-if-A-packet-visible otherwise WAIT
deliberately changes its own future callback word when that input changes.
That is a policy-induced difference, not information about x_B.
Nor are future full observations, within-clock placement, or later owner
activations across retry/reveal phases equated: success can still change
those later phases. The full service-posterior premise would exclude this
variant. This is mathematical; no native Lean implementation or certificate
for it is claimed.

## Concrete native realization and finite bounds

Use the existing empty-context `setup` and `program` in
[the two-commitment fixture](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/OnePacketCommitRevealHypotheses.lean),
with the utility just specified in place of its matching-pennies utility.
Only the program and setup are reused: its default sequential scheduler,
empty leak rule and two-slot bounds are not the construction here.

Compile in `.concurrentReveals` mode. Events 0 and 1 are bindings; events 2
and 3 are their publications. The two bindings are ready initially. Each
reveal depends on the bindings, and neither reveal depends on the other:
the guards are TRUE and the owners differ. Both surviving reveals are
therefore ready together. The compiled maximal phase plan is exactly
commitment [0,2), then reveal [2,4). Indeed, a phase cannot cross the
binding/publication boundary; first/last/adjacent boundaries cover all four
events; and maximality forbids splitting either same-kind block. This uses
the actual chosen compiled plan, not a substitute plan assumed equal by
definitional reduction. A checked specialization of this finite equality is
still required.

Use deadline duration 6 for every event, opportunity delay 0, protected
bound 5 and the complete-pending observation rule. The implementation can
use only the application's existing activate, include, WAIT, clock-advance
and expire commands. Normalize/close/reset are the actual application's
automatic transitions. Draw the two fair bits at the original binding
addresses and use degenerate laws at every other full attempt/event
address. Realize that original product draw by
`Interaction.ReactiveApplication.schedulerMixture`; its
posterior scheduler must retain the same seeds throughout the run. The
bits are not added to player-visible application state or redrawn after a
callback.

One explicit command budget, replacing unused slots by WAIT, is:

| Original segment | Maximum environment commands |
| --- | ---: |
| The two clock-0 activations | 2 |
| Advances to clock 2 | 2 |
| Clock-2 block and eligible late inclusion | 4 |
| Advance to 3, A callback and inclusion | 3 |
| Advance to 4, clock-4 block and late inclusion | 5 |
| Advance to 5, B callback and inclusion | 3 |
| Advance to 6 and the two expiry slots | 3 |
| **Original routine** | **22** |

An original binding miss excludes at least one owner. There is at most one
sole-survivor commitment retry, costing at most 9 commands: callback,
inclusion, six advances and expiry. There is one reveal phase, costing at
most 12: two callbacks, two inclusions, six advances and two expiries. Thus
every raw play reaches a terminal native cut within 43 environment commands.
There are at most 6 original callbacks, 1 retry callback and 2 reveal
callbacks, hence at most 9 transmissions. Horizon 64 and candidate capacity
64 suffice uniformly. Player responses do not consume the environment
command budget. After native completion, identity WAIT exhausts the
remaining protocol fuel. Both Boolean raw values are retained in the bounds,
as are the bounded raw preparation, evidence and malformed-call choices.

Candidate catalogues persist through reset. A proper retry uses a fresh
slot in that retained catalogue; it does not reuse or erase a voided cell.
The protected tail services all ready owners before advancing the clock,
including when both concurrent reveals become ready together. These details
are necessary for the all-raw opportunity and completion claims. The budget
and embedding here are mathematical checks, not checked native theorems.

## Service assumptions

Opportunity holds because both original owners are activated at 0. EARLY
packets receive their receipts by clocks 4 and 2, respectively, within bound
5. Every other original callback is late: s+5>=6, so expiry completes the
event before a protected receipt would be required. Timeliness is 0+5<6.
The protected-only continuation has opportunity and sure inclusion as well.
Clock advances and expiry give completion on arbitrary raw responses.

More explicitly, a raw response changes private preparation and network
traffic, but not the current cut, readiness timers or public clock. An accepted
binding completes its event without excluding its owner, whatever its hidden
preparation. Only expiry excludes a binding owner. Thus any unresolved original
binding stays ready with timer 0 until its due expiry at command 20 or 21;
both original coordinates retire by command 22. A proper or malformed response
cannot create an earlier binding exclusion. At most one survivor can retry.
Its timer is its ACTUAL namespace-entry clock c, not 0, and the retry's six
advances make expiry due at c+6. The reveal block has the same relative
deadline calculation and no retry. Switching blocks immediately on namespace
change avoids advancing a newly ready event before its first callback.

For protected inclusion, only original clock-0 emissions can have their
strict inclusion bound pass before that attempt ends. Each gets an actual
receipt by clock 4 or 2 if its original attempt is still live at that slot,
including a rejected malformed or extra-evidence packet. If raw extra packets
have already completed the original coordinates and retired the attempt, the
contract's completion exception applies; an old clock-0 envelope need not
then receive a receipt. A receipt, rather than acceptance, is the raw
contract's obligation.
Every tail response gets an inclusion immediately after its own activation.
Its identifier is the owner's serial recorded just before that activation;
the serial increases exactly when a packet was emitted. Silence therefore
cannot accidentally select an old pending packet. All ready tail owners get
their opportunity before the first advance, including both concurrent reveals.

These are all-raw TRACE arguments for each supported original seed. They also
hold for the mixed scheduler, not just its prescribed run marginals. Given
any finite legal mixed-scheduler trace, retain the seed set consistent with
its environment commands. Initially this set is the four-point product
support. At each scheduler step a positive-probability command retains a
nonempty subset of the preceding set. Application steps and player responses
use the same support kernels for every retained seed. Hence a seed retained
at the final prefix realizes that ENTIRE prefix under its fixed scheduler.
Apply the fixed-seed opportunity, receipt and terminal-completion assertions
there. No seed redraw or restriction to equilibrium strategies enters this
transfer. Counted privacy is separately quantified over fixed-seed traces.

Each original binding's accepting-completion bit depends only on its own
seed, its own relative emission clocks and packet well-formedness. Its
potential unsent clock calendar is [0,2,3] for A and [0,4,5] for B. The seed
chooses its within-clock activation slot; foreign actions never change that
calendar. Fresh handles, hidden prepared meanings and payload aliases do
not affect these delivery bits. Wrongly typed or unopenable bindings can be
accepted, as required by the contract; they fail later if not voided.

The selector and middle inclusion slots are fixed independently of the
seeds. A local seed is read only to insert its own activation, or determine
its own late service. Everything else is the deterministic remainder acting
on history. No rule reads an unopened value. Consequently this satisfies
the causal S1--S3 seed restrictions, the permitted-packet success quotient,
per-event value-blindness and content-blind leaks. It violates the stronger
clock-transcript sufficiency used in the
proposed proof: identity WAIT does not close the coordinate's current tick.
If S3 is instead defined to include that stronger composition discipline,
this builder is excluded; that is a different precise premise, not a
deduction from independent seeds or private delivery bits.

The exact service scope matters. The existing
`Vegas.EventGraphRuntime.PhaseService.PrivateActivationCalendar` and
`Vegas.EventGraphRuntime.PhaseService.PrivateBindingSuccess` quantify over
traces of `Vegas.EventGraphRuntime.PhaseCount.onePacketMenu`. On those
count-clean histories every nonsilent first binding has the required fresh,
authorized shape, and the construction's delivery bit depends only on its
seed and emission clock. The separate
`Vegas.EventGraphRuntime.PhaseService.AsyncContract` still quantifies over
all raw histories. Thus counted-service privacy plus the raw contract and
count audit is the precise formal interpretation obstructed here. This is
not a claim that a native instance of these predicates has already been
mechanized.

Here is the complete classification for the two formal privacy predicates.
All clocks are relative to the coordinate's own readiness clock.

| Full coordinate | Potential unsent calendar | Accepting binding for its counted emission word |
| --- | --- | --- |
| Original A binding | [0,2,3] | [0] always; [2] iff x_A=0; [3] iff x_A=1 |
| Original B binding | [0,4,5] | [0] always; [4] iff x_B=0; [5] iff x_B=1 |
| Active retry binding | [0] | [0] always |
| Active reveal | [0] | Outside the binding-layout premise |
| Never-ready or excluded coordinate | [0], immaterial | No matching emission or accepting receipt |

For every binding, an empty emission word has no accepting receipt. These
cases exhaust the full bounded attempt/event address space, including
addresses never installed by a particular play. A coordinate cannot receive
an accepting receipt without an authentic own emission for that coordinate.

For calendar exhaustion, a never-sending original owner cannot finish before
its clock-6 expiry. Foreign packets cannot complete its event, no other event
of this owner can exclude it in this phase, and an unfinished binding
prevents phase retirement. It therefore gets all three callbacks. Every
never-sending active tail owner gets its single clock-0 callback before any
advance, then expires. Automatically skipped coordinates have no genuine
ready-request witness, so the exhaustion implication has no premise.
Post-SEND callbacks do not cause a conflict: the calendar-prefix clause
requires an unsent own history, and exhaustion requires no emission at all.
Those clauses no longer apply after transmission.

Retirement does not erase owner recall or receipts. The clock words and
accepted-receipt predicate are filtered by the full physical attempt/event
ID. A retry changes generation and a phase advance changes the phase
address, so subsequent callbacks cannot contaminate the old coordinate.
The table thus proves the required calendar prefixes/exhaustion and resolved
binding-success equivalence mathematically, with arbitrary counted actions
and every supported original seed. It is not a verified instance of the
Lean predicates.

### Why the all-raw Boolean quotient cannot hold

Consider the stronger interpretation that, on ALL raw histories, the original
binding's accepting-completion bit is determined by its local seed, its own
relative emission clocks and only the Boolean count-well-formedness verdict
of each packet. This is a precise extra interpretation of S1's informal
word "content"; it is not the existing counted privacy predicate. Under
this interpretation NO builder for the Boolean program above satisfies
the timely all-raw native contract. The argument does not use the signalling
schedule or any equilibrium.

Fix a supported full builder seed, and let everyone remain silent except
for one response by A. Opportunity, completion and delay 0 force A's first
callback at clock 0 while its initial binding e is ready. Its own prepared
catalogue is empty. Choose a fresh owned prepared handle h and Boolean true.
The bounded raw menu contains both of these responses:

| Response at the first callback | Count-well-formed? | Native handling while e is ready and timely |
| --- | --- | --- |
| Register true at h; bind e to h; attach the authentic certificate for h=true | False: a binding must carry no evidence | Accepted |
| Send an opening of h=true addressed to the SAME binding event e | False: an opening is not a binding call | Rejected |

The first certificate exists even in the empty initial context: registration
precedes certificate issuance in the SAME atomic response. No earlier packet
or separate hidden preparation is needed. The second call explicitly names
e; an unaddressed malformed call would not give the same emission word.
Both runs retain the same original local seed, exactly one own emission for
e at clock 0 and the one-entry verdict word [false]. All later own responses
are silent. There is no reveal guard involved in this comparison.

The first packet must receive an accepting receipt before clock 6. To see
this, suppose it does not. No foreign action can complete or exclude A's
initial binding, and its fresh handle cannot be displaced by another own
packet. An inclusion while ready and before 6 accepts: the native handler
does not inspect the extra evidence. If no inclusion occurs, native
completion requires reaching expiry. Immediately after the advance to clock
6, but BEFORE the separate expiry command, e is still unfinished in its
original namespace. The sole-packet protected-inclusion premise applies
because 0+5<6, requiring a receipt already. Such a receipt before 6 would
have accepted, contradicting the supposition. Automatic phase normalization
does not expire a still-active owner's unfinished event at the clock
advance. Hence the first original coordinate has an accepting receipt.

The second packet can never receive an accepting receipt: the call's event
has binding layout, so the opening handler rejects it. No later own packet
exists. Completion therefore eventually resolves the original coordinate
without an accepting receipt. Reset and archival retain this distinction;
it concerns the ORIGINAL coordinate, not a later retry or final survival.

Thus the equal local seed, emission word [0] and verdict word [false] give
opposite resolved accepting-completion bits. This contradicts the proposed
all-raw Boolean quotient. The required premises are genuine initial
readiness, both raw responses in the bounded menu, the numerical margin
delay 0/bound 5/deadline 6, and the all-raw contract; the contract alone
without timeliness would not suffice.

Keeping the full signed packet content does not by itself settle the raw
scope either. Couple two protected commitment prefixes that privately
prepare A's same handle h with true and false, respectively, without
attaching evidence. Their emitted binding envelopes are identical.
Per-event value-blindness gives the same public prefix, reveal address and
readiness clock under the same builder seed. At A's first reveal callback,
send the SAME opening of h=true with NO certificate in both runs, and stay
silent afterwards. The raw menu allows both. The emitted call, evidence,
token and relative emission clock 0 are identical. Both packets are
count-audit-invalid because their own certificate is missing; the static
guard is TRUE in both cases.

The native handler nevertheless accepts in the true-preparation run and
rejects in the false-preparation run: it ignores the evidence field but
checks the candidate's value and the value of the accepted binding. An
opening submission cannot change that private candidate. The same timely
sole-packet argument forces acceptance before expiry in the matching run;
completion resolves the mismatching run without acceptance. Thus a proposed
all-raw content classification must specify whether it also includes the
STATE-RELATIVE fact that this opening matches the accepted binding. That
fact distinguishes these two runs; it is not a function of the current
signed packet or its count verdict. Count-clean authentic certificates make
the compatibility derivable, which explains why counted privacy avoids
this issue. The relevant handler and certificate semantics are in
[native admission](../Vegas/Pending/EventApplication.lean) and
[authentic evidence](../Vegas/Pending/OpeningEvidence.lean).

The contradiction does not apply to counted privacy, which excludes both
responses. Nor does it apply to a raw content classification that distinguishes
their state-relative native admission statuses. Prose S1 lists packet
"content" and names
well-formedness, while its positive builder example also refers to content;
it does not give a formal all-raw equivalence relation. Consequently the
intended all-raw scope remains a specification question. If the Boolean
quotient is intended, the proposed nonvacuity example fails it as well.
If the counted/native-admission reading is intended, the signalling
obstruction still applies. Neither conclusion licenses silently changing
the theorem's assumptions or asserting a checked native refutation.

### An all-raw quotient by admission at emission

There is a richer, nonvacuous all-raw interpretation for which this particular
builder still gives the obstruction. This is a conditional classification of
S1, not a choice of its intended meaning. For each actual emitted envelope m,
record the bit a(m) saying that IMMEDIATE inclusion in the state just after
its atomic submission would give an accepting native receipt. Use the full
phase handler, including namespace, token, call/layout, author, handle and
deadline checks. This bit tests the present state, not future delivery. It
contains neither the service seed nor a future receipt.

For an original binding owned by i, let L_i(x_i) be its eligible late clock:
2 or 3 for A, 4 or 5 for B. On EVERY raw run continued through resolution
of the original coordinate, its retained accepting bit is

    D_i = OR over its own matching-coordinate emissions m of
            [emissionClock(m) in {0,L_i(x_i)} and a(m)=1].

The clocks are relative to the original readiness clock 0. This is a function
of the local seed and the owner's own clock/status word. It ignores handles,
private preparations and other traffic once the admission statuses are fixed.
It is not a statement that raw admission is the Boolean count verdict.

To prove the formula, each original owner has at most one callback at each
of its three clocks. Only its clock-0 envelope and its eligible late envelope
can be included for this binding. While the original event remains unresolved,
a positive admission bit cannot be invalidated by foreign traffic: the other
owner cannot bind this event or consume one of this owner's handles. There
is no second own binding event in this phase. The original timer remains 0,
and both possible inclusion clocks are strictly before 6. Private submission
cannot change the cut or accepted handles. If a different own packet resolves
the binding first, D_i is already true and that packet supplies the positive
term instead.

A matching original-coordinate emission occurs only at its owner's ready
callback, strictly before clock 6. Its event cannot be unready at emission
and become ready later. A raw packet naming a future static event is instead
unauthorized in this full attempt and cannot become a packet for its later
phase. A negative bit cannot turn positive before the binding resolves: its
call, author, handle ownership and token are immutable; an already used handle
cannot become unused inside the same live attempt. Hidden preparation does
not enter binding admission. Wrong-clock envelopes are never selected later.
Thus if every eligible term is false, no own packet can accept, foreign
packets cannot complete this binding, and expiry resolves it without an
accepting receipt. These two directions prove the formula on raw histories,
including multiple identifiers and packets forbidden by the audit.

For each active tail coordinate there is one owner callback at relative
clock 0 and immediate inclusion of its exact new envelope, with no intervening
player response. At a resolved endpoint its accepting bit therefore equals
that envelope's admission bit, or false if silent. In this Boolean TRUE-guard
program an admitted opening also succeeds; a general program would additionally
require its native publication/guard result in the status. Skipped or
never-installed coordinates have no accepting receipt. Full attempt tags
prevent a packet from an earlier
phase or generation reviving after reset, regardless of the retained catalogue.

Do not replace this admission bit by a conjunction containing slot freshness.
A raw earlier forbidden submission can fix an owned handle without binding it;
a later binding may still accept that fixed but UNUSED handle. Its immutable
meaning matters at the reveal, whose admission test checks it. Nor does this
classification make the builder inspect the bit: its inclusion choices still
read no private meaning; the native handler alone decides acceptance.

Thus expanding content to state-relative native admission does not by itself
remove the timing obstruction. The unsent activation-calendar classification
also extends to raw histories in this fixture: only one event of each owner
can be live in a phase, foreign packets cannot complete or exclude that owner,
and a nonmatching own packet cannot resolve another own event in that phase.
An owner that never sends for this coordinate therefore stays ready until
expiry and receives the entire calendar, irrespective of its other raw traffic. Avoiding the
obstruction requires resolving the activation and observation condition as
well. No such stronger condition is adopted here.

## What the observations reveal

If B sent EARLY, A sees B's packet pending at its clock-2 callback exactly
when x_A=0, or sees its receipt already present exactly when x_A=1. Thus A
knows which of 2 and 3 will deliver its packet. This works for any helper
handle; it does not rely on a hidden choice of request alias.

If B did not send EARLY, the middle slot at 2 is an unobserved stutter.
Both A seeds give precisely the same full player input at that callback:
clock 2, its earlier WAIT, no B packet or receipt, and the same public state.
The private seed remains fair. A first SEND at either 2 or 3 succeeds with
probability 1/2; no adapted uncharged rule does better. Choosing never to
send gives probability zero. Randomization gives a convex combination.

The analogous statements hold for B at 4 and 5 with A's EARLY packet as
helper. When both players waited at 0, B's seed was not read anywhere in
A's late history. Conditional on that entire history, B's seed is still
fair, and the absent A-EARLY marker reveals nothing about it. B may condition
its timing on A's accepted receipt, but its maximum delivery probability is
still 1/2 in EACH such history. This is a conditional argument, rather than
an inference from two unconditional success marginals.

No hidden prior-doom type can replace these beliefs. Bob's first input
reveals every A transmission, and none has yet been included. Observing
no A packet therefore means Alice did not transmit at her first callback.
In the first commitment phase from empty context she has no earlier accepted
binding. Preparation is part of a transmission, not an extra hidden action.
Initial seed independence and the observation equivalences give these Bayes
facts under every completely mixed sequence. No relative tremble rate can
make Bob interpret that empty view as an inherited unopenable binding.

More explicitly, pair hidden histories by toggling the relevant bit while
retaining every other original coordinate and the same player actions. With
no helper, the changed activation slot adds only an invisible WAIT on the
other side of the callback. All full inputs before each recorded action
are equal in the pair. Thus their behavioral likelihood factors agree
pointwise for every approximation index n; equal prior bit masses give
equal conditional masses before taking a limit. After an initial WAIT,
the same pairing applies to the second late callback if the first late
response was WAIT. For B it also retains the entire earlier A history,
which has not read B's bit. This proves the conditional fair-bit claims
without comparing rates of different trembles.

This last point is why starting the same timing game at a reveal phase would
not suffice: Bob could then assign an off-path WAIT to an inherited bad
binding and rationally send EARLY.

The relevant information facts agree with the application interface:
[responses and player views](../Interaction/ReactiveApplication.lean) expose
optional transmission and own recall, while
[native information](../Interaction/ReactiveProtocol.lean) does not expose
the remaining response budget or global command index.
[Private registration](../Vegas/Pending/EventSubmission.lean) is bundled
with submission. An identity WAIT changes environment recall without
changing any player view. These facts support the observation argument;
they do not replace verification of the complete native instance.

## Raw preparations and reset continuation

First justify eliminating the first charged action without assuming any
later charge-free incumbent play. At a full input I, own recall fixes the
complete list of signed own outputs. The count permission verdict of an
own envelope depends only on earlier signed own outputs, and is immutable
under later foreign traffic. Thus an own-clean recall is clean at EVERY
history in I, including histories assigned zero limiting belief. At the
two initial inputs the own output list is empty; after the initial WAIT it
is still empty at each owner's first late input. A WAIT neither emits a
packet nor privately registers a candidate. Foreign packets cannot create
a signed own output.

At any such clean input, the whole continuation policy that stays silent
has zero own charge and terminal utility at least -epsilon on every
compatible history. Committing to a forbidden current packet gives a
permanent certain charge, so even with an arbitrary later incumbent policy
its utility is at most W-K<-epsilon. Sequential rationality compares whole
continuation policies. Every supported current atom must attain the
optimal value; consequently a forbidden atom has probability zero. For
W=3, epsilon=1, K=5, these are the uniform bounds -2<-1. The existing
supported-choice uniform-gap theorem supplies precisely this inference;
its hypotheses require bounds on the entire information fiber, which the
own-recall argument supplies. Native terminal runner factoring and decision
recall supply the current-choice mixture decomposition. There is no claim
about optimal behavior after a sunk own charge, and no invocation of a
converse to the counted-to-raw equilibrium extension theorem.

The relevant existing permission APIs are in
[count verdicts](../Vegas/Pending/PhaseCountVerdict.lean) and
[permanent charge collection](../Vegas/Pending/PhaseCountCollection.lean);
the native recall identity is in
[input recall](../Interaction/ReactiveRecall.lean). These identify the
adapters needed for a checked reflection proof. This paragraph supplies
the mathematical argument, not those new checked adapters.

Let D_A,D_B be accepting delivery of the two ORIGINAL bindings. A valid
same-handle preparation has the same emitted envelope, markers and delivery
law as a bad one. Compare their sequentially optimal continuation VALUES,
not the behavior of an arbitrary fixed continuation reading different raw
recall. Work backwards through the protected-only future first. A sole
survivor's proper retry and reveals guarantee W, its payoff ceiling, at
either history. With both bindings delivered, a proper owner guarantees a
nonexcluded payoff >=0 by opening, while its own bad binding forces payoff
-epsilon. These facts give the preparation comparison:

- if own delivery misses, own payoff is -epsilon in either case;
- if the other delivery misses, the actual reset voids the changed binding
  and its guard obligation; the surviving optimal continuation has value W
  at both histories, although their retained raw recall differs;
- if both deliver, proper material guarantees own survival at the protected
  reveals, giving at least 0, whereas bad material causes own exclusion and
  payoff -epsilon.

The last improvement is strict whenever joint delivery has positive
conditional probability. Do not eliminate bad actions merely by citing weak
dominance: when another binding certainly misses, the material is erased
and may be indifferent. At B's late site, an already accepted A binding
makes this strict comparison immediate; after an irrevocable A miss, its
own bad/proper distinction is erased. At A's late site, an unread B seed
alone does not prove positive B delivery: B could stay silent. Eliminating
bad A material there additionally requires a best-response argument proving
positive B acceptance and retaining its law when A's hidden preparation
changes. That comparison is not established here and is not used by the
shorter contradiction below, whose helper case already has B's receipt.
In particular, weak dominance alone does not eliminate every bad binding.

A sole survivor's retry has a sure proper move. At subsequent protected
reveals, opening a proper value guarantees a nonexcluded payoff >=0,
whereas withholding gives -epsilon. Neither comparison needs another
player's off-path belief. Exhaustion after two misses gives both players
-epsilon. Conditional on the additional preparation comparison just identified,
sequentially optimal clean continuations have the following payoff table;
the shorter contradiction does not rely on this characterization:

| Original D_A | Original D_B | Payoff A | Payoff B |
| --- | --- | --- | --- |
| 0 | 0 | -epsilon | -epsilon |
| 1 | 0 | W | -epsilon |
| 0 | 1 | -epsilon | W |
| 1 | 1 | 0 | 0 |

Extra identifiers or disclosure packets cannot supply an uncharged extra
signal: they incur the deposit loss above. A well-formed first packet,
regardless of slot or preparation alias, is included as a helper exactly
when it was EARLY. Before the first late callback the relevant seed is
unread, so these aliases cannot carry advance information about it.
If the precise raw audit admits an invalid but uncharged first own packet,
do not relabel it charged: it cannot complete its event, burns that event's
free first packet, and a later repair needs a charged extra identifier.
Such a choice therefore gives own exclusion payoff -epsilon. The comparison
with a proper delivery rules it out wherever it would affect this argument.

## Sequential rationality forces the failures

### A shorter contradiction to preservation

For the construction above, with counted-service privacy and the all-raw
contract, every native SE gives A expected net payoff at least

    delta = W/4 - epsilon/2 > 0.

The chosen honest SE gives A payoff 0. Thus no native SE preserves its joint
public-result/realized-net-payoff law. This mathematical conclusion concerns
the precise counted interpretation above. Its installed W=3, epsilon=1 native
fixture is checked by
[`Vegas.Examples.CommitSeedSignalling.native_equilibrium_alice_payoff_quarter`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingNonpreservation.lean#L19);
the unresolved all-raw reading of prose S1 remains separate.

Here is a proof that does not classify the late equilibria. Fix any assessed
native SE. The clean-recall argument excludes a forbidden current packet at
EVERY genuine clean own-recall input, including an input with zero probability
under the equilibrium strategy. Consequently clean own play stays clean
under the assessed strategy even after another player deviates. This is a
support restriction on the assessed policy at that input; it does not require
the assessment's posterior to equal the deviating play's posterior.

First record the no-helper timing bound. Let Z be the complete physical
prefix BEFORE the owner's seed-dependent first late polls. For B this is
the prefix before command 12. None of that prefix reads its local seed,
which is therefore still fair conditional on Z. Couple the two seeds using
the same remaining player randomness. Their first late full inputs coincide:
the absent middle marker is an unobserved identity WAIT. Let F mean that
the owner emits for this original coordinate at its first late clock, and
write q(Z) for its conditional probability. The equality of inputs makes
q(Z) the same under both seeds. Under seed 0, acceptance requires F. Under
seed 1, acceptance requires an emission at the second late clock, hence
requires not F because the owner can emit at most once. Thus

    P(D=1 | Z) <= (q(Z) + 1-q(Z))/2 = 1/2.

This argument permits arbitrary later inputs, bad preparations, silence and
randomized policies. It needs neither equality of the second late inputs nor
a fair seed posterior after the first poll. It must not condition on the
hidden polling position. For A after both initial WAITs the same argument
starts before command 4; for B it retains the entire earlier A prefix.

At B's initial input after A WAIT, compare two whole continuations. Full
pending observation and empty initial own catalogues make this a fixed physical
prefix with the original product seed law, even when A's WAIT was off path.

A permitted B EARLY packet guarantees B's original accepting binding. Its
marker identifies A's seed at A's late input. A proper packet at the known
eligible slot followed by protected proper play guarantees A survival, with
payoff at least 0. To infer actual A survival, work backward through the
viable late inputs. When x_A=0, the useful slot is 2: waiting or using bad
material irreversibly gives -epsilon, whereas a proper packet gives at least
0. When x_A=1, first consider clock 3 AFTER A WAIT at 2; the same strict
comparison forces a proper packet there. Then at clock 2, WAIT followed by
that proper continuation gives at least 0, whereas sending any packet in
the wrong slot burns the only free packet and gives -epsilon.
No comparison asserts safe value at an arbitrary clean clock-3 input: an
earlier wrong-slot SEND can leave it clean but doomed, and full own recall
separates that fiber. Optimality at clock 2 excludes entering it here.

B's accepted binding prevents a commitment reset that could erase A's bad
material. A proper owner's later protected reveal similarly gives at least
0 rather than the exclusion payoff. These comparisons are uniform over their
complete information fibers, so they apply under any consistent beliefs.
Thus A's ORIGINAL assessed strategy survives under every supported B EARLY
choice. B's EARLY continuation has value at most 0, including when its own
hidden preparation is bad. This does not substitute a safe strategy for A.
In this fixture the actual permission test at B's empty first input allows
only fresh owned binding calls, which the native handler accepts regardless
of preparation. If a larger audit menu admitted invalid but uncharged first
calls, they would instead require the separate burnt-slot argument above.

Instead B can WAIT and then send a proper packet at the fixed clock 4.
Without a helper A's accepting probability p is at most 1/2 by the timing
bound and clean support restriction. B's still unread seed gives delivery
probability 1/2 conditional on every A prefix before B's late polls. B's
proper tail is charge-free against every A future and guarantees W when
its own binding lands and A's misses, at least 0 when both land, and at least
-epsilon otherwise. Its expected net payoff is therefore at least

    (W/2)(1-p) - epsilon/2 >= W/4 - epsilon/2 > 0.

Every non-WAIT B atom has value at most 0 or is forbidden. Thus B strictly
WAITs at that initial input. A can now deviate to WAIT,
send a proper packet at the fixed clock 2, and play properly in the protected
tail. Its own delivery probability is 1/2. Conditional on each entire A
prefix before B's late polls, B's no-helper delivery probability is AT MOST
1/2, even if that prefix reaches an originally zero-probability B input.
Clean own recall excludes B's extra repairs there without using a Bayes
identity for the deviating law. An upper bound suffices; no characterization
of B's late best responses is needed. If B's binding misses, reset gives
surviving A its ceiling W. If B's binding lands, A's protected proper
continuation gives at least 0. Consequently this fixed A deviation has value
at least

    W P(D_A=1,D_B=0) - epsilon P(D_A=0)
      >= W/4 - epsilon/2 = delta.

To see the first bound explicitly, let Z be the complete physical prefix
immediately before B's clock-4 polling block. A's delivery bit is already
determined by Z: after A's initial WAIT, its only eligible inclusion commands
are 7 and 10, both strictly before this prefix. There is no later original-A
callback or inclusion, and expiry cannot add an accepting receipt. B's seed
remains fair conditional on Z. Hence

    P(D_A=1,D_B=0)
      = E[1{D_A=1} (1-P(D_B=1 | Z))] >= P(D_A=1)/2 = 1/4.

The second probability is exactly 1/2. Sequential rationality at A's first,
surely reached input makes its equilibrium payoff at least delta,
contradicting the honest payoff 0. No assertion about B's late best responses
was used.

The two positive lower bounds average over the original fair seed law.
They are not bounds at each separately seed-tagged world. In the actual
application, immutable seeds live in the scheduler implementation rather
than the public execution state. A's first callback and B's first callback
after A WAIT have fixed pure physical prefixes; their hidden-seed mixture
is still the original product law. Later no-helper probabilities must sum
over full native information fibers, including the different hidden command
positions of the two same-clock callbacks. A physical environment log
reveals that position and must not be conditioned on by itself. The
at-most-1/2 delivery bound is for at-most-one-packet continuations; arbitrary
raw policies can send at both late clocks and exceed it, which is why the
charge argument is indispensable.

For W=3 and epsilon=1, the experiment checks BOTH fixed deviations' worst-case
values against every opposing reduced late pure policy: each minimum is 1/4.
Mixed policies follow by affinity. These checks support this shorter proof;
they do not certify its native information or raw-audit adapters.

### Exact boundary of the mathematical conclusion

The preceding argument establishes a conditional mathematical proposition:
for this finite schedule, complete-pending observation, actual reset rules,
and count audit with W>2 epsilon and K>W+epsilon, every assessed native SE
has initial A payoff at least W/4-epsilon/2. It fixes one honest source SE
and excludes every preserving native SE; it does not merely show failure of
a proposed lifted strategy. Clean support is proved at all genuine own-clean
information sets, so neither positive lower bound assumes equilibrium reach
or substitutes the deviation's posterior into the assessment.

Its application to the abstract preservation theorem has a separate premise
question. The causal seed-read restrictions in the S1--S3 bullets and the
counted calendar/success predicates allow the schedule mathematically. The
factorization assertion after S3, if imposed as an independent requirement
of full seed-posterior sufficiency, excludes it. These readings are different
hypotheses: a signal about within-clock activation position is a permitted
causal effect in the first and forbidden extra information in the second.
The narrower sentence about future activations needs the distinctions in the
[mathematical audit](se-preservation-math.md#future-callback-clocks-and-future-service):
potential unsent calendars agree, but actual callbacks after a chosen SEND
can differ. The all-raw packet-content quotient is a further, independent
choice, classified above. Consequently the payoff proposition is not an
unqualified refutation of the intended abstract theorem. Conversely the
claimed clock-filter inference cannot prove preservation from the causal
bullets alone. The remaining work is to certify the construction under the
existing runtime model, including its full service contract and the universal
equilibrium incentive bounds. This note does not add the stronger premise or
claim that its native certificate has been completed.

### Full outcome calculation

Suppose first that A sends a proper EARLY binding. Its delivery and later
survival are guaranteed. B can guarantee its own survival by sending EARLY,
or by waiting and decoding its seed from A's helper. Success gives B at
least 0; own failure gives -epsilon. Every B best response therefore survives
surely, even if B is uncertain about A's hidden preparation. For the actual
proper A, the resulting payoff is 0. An EARLY bad preparation does worse.
B need not strictly prefer EARLY here: safe late delivery also gives 0.

Now suppose A WAITs. At B's first callback no A packet exists.

- If B sends a proper EARLY packet, A learns its seed and delivers properly
  with certainty. Both survive, so B earns 0. A bad EARLY packet is worse.
- If B WAITs, neither helper exists. Write p<=1/2 for A's delivery chance.
  B can attain conditional delivery probability 1/2 after every A history
  using a proper packet. Its payoff is therefore at least

      (W/2)(1-p) - epsilon/2 >= W/4 - epsilon/2 > 0.

  This lower bound does not assume A already uses optimal late play, and
  remains valid if an A bad preparation makes its later reveal fail.

Thus B strictly WAITs after A WAIT. At the resulting late inputs, A can
choose proper timing with delivery probability 1/2. B then maximizes its
delivery probability in each A history, because the gain from own survival
is strictly positive. Its conditional success probability is exactly 1/2.
Hence A's WAIT continuation earns

    W/4 - epsilon/2 > 0,

strictly more than its EARLY payoff 0. Both first WAITs are therefore forced
by sequential rationality, under any consistent beliefs.

On these histories P(D_A=1)=1/2 and P(D_B=1|D_A)=1/2, so all four delivery
patterns have probability 1/4. Both public reveals succeed with probability
only 1/4; some player is excluded with probability 3/4. This differs from
the honest law, under which both reveals always succeed. For example
W=3, epsilon=1 and K=5
give honest payoffs 0 and the strict initial WAIT value 1/4.

This does not refute Nash preservation. An unconditional EARLY prescription
for the other owner makes a unilateral WAIT obtain its helper and survive
without gaining over 0. Such prescriptions can support the honest Nash
outcome. They fail sequential rationality at B's off-path callback after
A WAIT, where B's own WAIT has the strict positive value computed above.

The exact finite calculation in
[the experiment](../scripts/experiments/private_seed_signalling_probe.py)
enumerates the late pure timing policies, including B's conditioning on A's
outcome, and checks these probabilities with rational arithmetic. It does
not certify the native embedding, arbitrary raw-menu reduction or S1--S3
interpretation; those require the mathematical argument and the checked native
theorems above.
