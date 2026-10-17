# Private-seed signalling in a first commitment phase

**Counted-service obstruction worked out; native Lean counterexample not checked.**

This note tests Theorem 3 of [the preservation argument](se-preservation-commit-reveal.md).
Under the literal causal reading of its S1--S3 bullets, independent event
seeds do not prevent players from changing another player's information
about its seed. The finite timing game below has no preserving sequential
equilibrium. It extends to the raw audited game when service privacy is
imposed on permitted counted histories, as in the existing formal predicates.
An all-raw quotient by only the Boolean count-well-formedness verdict is
incompatible with timely native protected inclusion, as proved below.
The intended content quotient in prose S1 still needs a precise reading;
charge dominance cannot decide an exogenous service hypothesis.
This is mathematical evidence, not closure of a checklist box or a checked
refutation for the native Lean runtime. No target, semantics or additional
hypothesis is adopted here.

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

## Concrete native realization and finite bounds

Use the existing empty-context `setup` and `program` in
[the two-commitment fixture](../Vegas/Examples/OnePacketCommitRevealHypotheses.lean),
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
own bad/proper distinction is erased. At A's late site the still-unread B
seed gives positive probability of B delivery, so standing bad material is
strictly inferior. This is a backwards argument, not an assumption that
all raw bindings have proper values.

A sole survivor's retry has a sure proper move. At subsequent protected
reveals, opening a proper value guarantees a nonexcluded payoff >=0,
whereas withholding gives -epsilon. Neither comparison needs another
player's off-path belief. Exhaustion after two misses gives both players
-epsilon. Consequently sequentially optimal clean continuations have the
following payoff table:

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
interpretation; those require the mathematical argument above and eventually
checked native theorems.
