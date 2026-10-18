# Arbitrarily large penalties do not ensure concurrent preservation

## Theorem and scope

There is a fixed finite two-player source game with a fair private Boolean
parameter such that every honest source strategy profile gives Alice expected
payoff 1/2. For every finite clean own-exclusion loss C_A>1, C_B>1, and every
finite enforcing count-audit charge, there is a value-blind, content-blind
interactive asynchronous packet service with fixed finite bounds for which
EVERY sequential equilibrium gives Alice expected payoff at least 181/200.
Consequently no runtime sequential equilibrium preserves any honest source
payoff distribution.

The source, operation counts, candidate supply, reaction bounds, inclusion
bounds, deadlines, packet-delay bound and horizon are independent of the
penalties. Only one service coin law depends on the chosen loss. Thus the
statement rules out a sufficiently-large-finite-penalty preservation theorem
for this whole callback service class. It does not say every service fails.

This is a mathematical theorem for the interactive model: a player chooses a
raw response when the scheduler activates it. It is not a theorem for clients
that can send at any real time. Native mechanization of the particular padded
service and unequal deadlines below is not claimed.

With the fixed finite raw menu bounds, this is a finite perfect-recall game.
Sequential equilibria therefore exist; the assertion about every runtime
equilibrium is nonvacuous.

The source is the existing [private-bit source fixture](../Vegas/Examples/CommitTimingInformationSource.lean).
The mathematical derivation uses the actual phase-local checkpoint, exclusion
and publication rules in [the phase runtime](../Vegas/Pending/PhaseApplication.lean),
the signed permission and masking definitions in
[the count verdict](../Vegas/Pending/PhaseCountVerdict.lean) and
[the count projection](../Vegas/Pending/PhaseCountProjection.lean), and the
all-raw opportunity, sole-packet receipt and completion predicates in
[the phase service contract](../Vegas/Pending/PhaseServiceContract.lean).
The changed deadlines and padded dispatcher are a mathematical instantiation
of those definitions; their new Lean certificate is pending. No source,
runtime semantics or preservation checklist is changed by this note.

## Source, settlement and audit

Bob knows an immutable fair private bit b. Alice chooses a private Boolean x;
Bob chooses an irrelevant Boolean helper. Both later publish, with TRUE guards.
Alice's honest payoff is 1{x=b}; Bob's honest payoff is zero. Alice chooses
before receiving any information about b, so her honest expected payoff is
1/2 under every source profile. An honest source sequential equilibrium exists
(for example, constant guesses and helper, followed by mandatory publications).

In the runtime, surviving Alice receives 1{x=b}. Surviving Bob receives
s(b)*1{Alice's required publication failed}, where s(false)=1 and s(true)=-1.
Permanent own exclusion pays -C_i. The constants C_i include ALL clean
own-failure forfeitures, not merely one named penalty component. The bit b is
retained by reset. Audit deductions are burned and nonnegative.

There are two logical phases: both commitments, then both publications.
The primary semantics are the actual expel/restart rules: exclusions are
permanent; a commitment attempt retries among survivors once the phase has
resolved; publication failures exclude and drain/advance, without rolling
back the consumed commitment phase. The separate immediate-first-binding-
failure variation is addressed below.

At an activation, a raw response emits at most one envelope. The full count
audit checks the actual signed one-packet permission: current readiness token,
owned/correct call, fresh candidate, first response for the physical event,
and opening/binding consistency. Local envelopes attach the current attempt;
invalid/off-phase calls have invalidated permission tokens. Thus different
owners/events, second packets and stale handles cannot masquerade as legal
original commitments. Fresh usable aliases AND hidden unopenable preparations
are permitted; the audit does not inspect a secret Boolean's truth or demand
proof of usability. A silent action has no separate preparation effect.

Choose an authentic audit that collects K_i once after the first forbidden
packet with conditional coverage rho_i>0, on every subsequent continuation,
and assume

    rho_i*K_i > 1+C_i.

A full terminal audit has rho_i=1; independent settlement sampling of the first
forbidden packet also suffices. Collection persists after reset and exclusion.
Permitted late packets and legal omissions receive no count-audit charge.

At a clean full own recall, perpetual silence emits no forbidden packet and
guarantees at least -C_i against arbitrary foreign behavior. A forbidden current
action gives at most 1-rho_i*K_i<-C_i, irrespective of later rescue or further
actions. Sequential optimality excludes it at every such input. Induction keeps
all supported initialized equilibrium histories counted. The same induction
applies against unchanged equilibrium opponents after a focal permitted whole
policy deviation. It requires no globally-counted belief assumption at an
arbitrary raw information input. Every own private alias remains in the full
recall when applying this comparison.

The theorem concerns arbitrarily large finite enforcing charges, not every
small positive bond. This is enough to refute a universal sufficient deterrence
threshold. If a different compiler fines legal late packets, or uses a single
bond whose clean omission forfeiture precludes the displayed enforcement
inequality, its audit must be analyzed separately.

## A concrete bounded service

Let

    q=9/10,  d=1/10,  e=1/[10(C_A+1)].

Predraw independent bits G,L, independent of b and behavioral randomization,
with P(G)=q and P(not L)=e. Alice's original local seed is (G,L); other event
seeds may be degenerate. Every retry is a fresh physical coordinate. No
scheduler decision reads b, a private preparation or an unopened Boolean.

Both original bindings are ready at clock0. Set

| Owner | Reaction bound | Inclusion bound | Deadline |
| --- | --- | --- | --- |
| Alice | 0 | 6 | 7 |
| Bob | 2 | 3 | 6 |

Use the corresponding same bounds for publication events. Both strict margins
hold: 0+6<7 and 2+3<6. All pending envelopes are shown at an activation; selection
of leaks is independent of payload/evidence.

The original core has the following 22 tasks, omitting an activation if its
request has resolved and immediately switching after an actual phase exit:

| Position | Task |
| --- | --- |
| 0 | activate Alice at0 |
| 1,2 | advance to1; deliver Alice0 if present |
| 3 | advance to2 |
| 4 | activate Alice iff G |
| 5,6 | activate Bob; deliver Bob2 if present |
| 7 | activate Alice iff not G |
| 8 | deliver Alice2 iff G |
| 9 | advance to3 |
| 10,11 | activate Alice; activate Bob if unresolved |
| 12,13 | deliver Bob3; deliver Alice3 iff not G |
| 14 | advance to4 |
| 15,16 | activate Alice; deliver Alice4 iff L |
| 17,18,19 | advance to5; advance to6; expire Bob |
| 20,21 | advance to7; expire Alice |

An absent response or unselected task is WAIT. Deliver Alice's other original
packets at8, when the old event is completed or its namespace retired. Thus
proper original admission is exactly

| Emission | Native admission |
| --- | --- |
| Alice0 | always, at1 |
| Alice2 | iff G |
| Alice3 | iff not G |
| Alice4 | iff L |
| Bob2 or Bob3 | always, immediately |

Deliver ANY raw envelope emitted at a response label on that label's schedule,
not only a correctly formed packet. Native rejection still produces a network
receipt. Ineligible Alice2,3,4 packets have respective delays6,5,4; Bob/tail
packets have delay0. The global packet-delay bound is6. Stale-attempt packets
are physically delivered/rejected, not abandoned when their obligation retires.
Non-FIFO, emission-time-dependent delays are allowed.
Release labels are part of this schedule, in addition to due clocks: original
Alice0, Alice2, Bob2, Alice3 and Bob3 release at core tasks2,8,6,13,12;
Alice4's single admitting trial is core16. Earlier padded subslots cannot
deliver a newly emitted envelope before its designated release task. Tail
Alice/Bob responses likewise release at their following include tasks1/3.
There is NO special immediate-delivery exception for malformed or off-coordinate
packets: they use the same owner/response-label schedule. A wrong-owner or
not-ready named event does not meet the protected receipt antecedent; a packet
naming the owner's ready event has exactly the receipt-bound argument below,
regardless of whether its call is accepted.

After any phase exit, each new namespace's tail activates ALL currently ready
owners and immediately delivers each response before advancing time. Then
advance to relative6, expire Bob, advance to relative7, expire Alice. Skip
inapplicable tasks. There are at most13 core tasks per tail block. Commitment
failure may create a survivor retry; publication never re-enters commitment.
Provide more candidates than all possible emissions. This supplies a whole
proper policy that registers only its chosen handles; foreign owners cannot
alter its catalogue. It is not a guarantee of fresh space after an arbitrary
raw preparation that registered many unused handles.

To cover all raw histories, reserve12 dispatch subslots at every core boundary,
including absent-response WAIT slots; dispatch due labels before advancing.
An overdue old label is dispatched after retirement before the next advance.
The cursor counts the reserved slots independently of packet presence. After
gameplay, advance only as needed to MAX(currentclock,8), dispatching all
remaining due original labels, and finally flush12 slots. Payoffs already fixed
at logical termination do not change during this network cleanup.

There are at most six original callbacks. At most three further namespace
blocks, each with at most two responses, give at most M=12 raw emissions,
independently of the horizon. There are at most61 gameplay core tasks and8
cleanup advances. The conservative environment-task bound is

    (61+8)*13+12 = 909 < H=1024.

All constants are independent of the penalties and e. A fresh-candidate supply
of64 suffices. The budget is not defined circularly by setting M equal to H.

### Service certificate on every raw history

Opportunity: original Alice is activated at0 and Bob at2, before their strict
reaction bounds are exceeded. Every new tail request has an elapsed-zero
activation before any clock advance. Raw early completions remove a request;
an early phase exit immediately applies this rule to its successor requests.

Protected inclusion means RECEIPT, including native rejection, for a sole owned
packet naming its ready physical event. Tail responses receive immediately.
Original Alice0 receives at1<0+6. For later original Alice emissions, before
sendclock+6 is strictly exceeded the event has completed at7 or the physical
attempt has retired; the protected-inclusion antecedent requires both same
current attempt and unfinished event. Bob2/3 receive immediately. This proof
uses neither audit validity nor native success, and permits arbitrary foreign
raw submissions. A different identifier for the same owner/coordinate removes
only that packet's sole-packet guarantee, as in the actual contract.

Native timeliness follows from ready/deadline/attempt checks. Ineligible Alice
packets delivered at8 cannot reopen an expired or retired event. Every core
namespace resolves or expires all unfinished owned events. A retry permanently
removes an owner; a successful phase consumes a descriptor. Raw calls cannot
reverse either progress measure, so the fixed horizon completes the surviving
graph. The dispatcher also settles every submitted network envelope.

The service is value-blind and content-blind. G is used only for Alice's own
activation placement and own accepting service; L only for her own4 admission.
Bob's fixed slot is between the two alternative Alice slots; it does not itself
read G. On counted packets, acceptance is a function of the event's own seed,
readiness-relative emission word and proper owned content/status. Thus the
literal causal/counted private-seed predicates hold. No posterior-sufficiency
consequence is assumed from those predicates.

## Binding persistence and protected continuation

When both original bindings admit, the commitment descriptor is consumed.
The drained state becomes the next phase's checkpoint and current state.
Publication never restores that old commitment checkpoint. Therefore usable
and unusable binding meanings persist; a foreign publication failure cannot
clear an unusable commitment. A bad binding can be rescued by a foreign
COMMITMENT failure before that phase closes, and that possibility is retained.

A whole proper policy starting with an unpolluted catalogue survives protected
retries against arbitrary foreign behavior: register only its chosen fresh
usable candidates, receive immediately, and later submit truthful accepted-
handle openings. Foreign failures cannot mutate its catalogue or undo a
completed own publication. The finite number of owners bounds retries.
The binding comparisons below start with literal own WAITs, which have no
preparation effect, so this catalogue premise is factual. Publication already
has a usable stored binding and needs no new candidate. Consequently the
proper Bob comparison at a quiet2 input or after WAIT2 at3 guarantees at least
-1, without a fresh-space claim for arbitrary polluted raw histories.

At the FIRST usable Alice publication input, every whole continuation pays at
most 1{x=b} pointwise. Proper publication attains that ceiling. Any positive
own-exclusion probability strictly loses, so every equilibrium continuation
from that entry survives. An unusable Alice binding instead necessarily fails.
Alice's publication failure is therefore its immutable unusable-status bit,
independently of Bob's publication choices. A usable Bob can attain
s(b) times that bit by truthful publication; own exclusion is strictly below
it. Thus every usable Bob also survives. This first-entry argument does not
assume rational rescue at a later, already-doomed input after omission.

## Backward normal form

Bob's last original WAIT3 causes exclusion at6. Alice's expiry7 cannot rescue
him first. Proper SEND3 plus protected recovery gives at least -1>-C_B. Every
supported equilibrium continuation therefore admits Bob by3, without assuming
his private preparation is usable.

L has not affected any transition before Alice4. At an unsent Alice4 input,
proper usable SEND4 strictly improves the positive L-good branch; Bob is already
admitted, so joint admission prevents any commitment reset from erasing a bad
Alice meaning. Thus every supported SEND4 is usable and WAIT4 is inferior.
At the common empty Alice2 input, G has positive weight. A usable same-envelope
preparation improves that branch and cannot worsen the ineligible branch.
Thus every supported SEND2 there is usable; leave its SEND probability s free.

A Bob receipt already visible at Alice2 implies not G. SEND2 certainly misses;
Bob is already admitted, so Alice would be excluded. WAIT2 followed by proper
SEND3 gives at least0. Hence this helper-seeing Alice2 strictly waits.

To determine the remaining Alice3 choices, retain a single fully mixed
consistency sequence. Let s_n be the SEND probability at the common empty2
input and ell_{b,n} Bob's WAIT probability at its quiet first input of type b.
The latter input has G/not-G weights q(1-s_n),d. At Alice3 after literal own
WAIT0,WAIT2 and no Bob receipt, those weights for EACH b are

    q(1-s_n)*ell_{b,n},  d(1-s_n)*ell_{b,n}.

Empty pending/receipt observations rule out any hidden earlier transmission:
every emitted packet is either pending or has a retained receipt, Bob has no
earlier activation, and NONE has no private preparation. Clock, requests,
public store, private own store and full own records coincide on the paired
prefixes. Original setup/type weights cancel before taking the limit. Thus
Alice's WHOLE input has P(G)=q even when its reach tends to zero. L remains
independent with bad probability e; it is not redrawn for a deviation.

At empty Alice3, SEND3 has upper value d-q*C_A. WAIT3 followed by proper4 has
lower value -e*C_A, which is strictly larger. If the Bob receipt first appears
at3, G is true and SEND3 certainly misses, so again WAIT3. If the receipt was
already visible at2, G is false. Bob is resolved and has no further meaningful
binding callback; publication cannot begin until Alice binds; L is unread.
No new b-information arrives from this input through her4 input BEFORE she
sends. If V is her current optimal guessing probability, proper SEND3 gives V,
whereas WAIT3 gives at most (1-e)*V-e*C_A<V. Thus she properly sends at3.

## Strict type separation and failure of preservation

Put s=lim s_n and D=d+q(1-s)>0. At Bob's quiet input the reference Alice failure
probabilities under proper early2 and proper late3 helpers are

    p_E = q(1-s)e/D,
    p_L = [d*s+(1-s)e]/D,
    p_L-p_E = d[s+(1-s)e]/D > 0.

The references J_E,J_L are Alice's failure bits under the corresponding proper
Bob admitting policy. If Bob actually admits, the normal form gives that same
Alice failure bit, independent of his private preparation alias. If Bob omits
and is excluded, immediate restart might rescue Alice, so actual failure need
NOT equal J. Nevertheless his own payoff is -C_B<=-1<=s(b)J. Hence every Bob
policy in a timing class has value at most s(b)p_E or s(b)p_L; proper whole
continuations attain those bounds, including survivor recovery after an Alice
miss. The formulas never substitute prior q for Bob's quiet posterior, and
never identify an arbitrary unusable Bob binding with certain own loss.

Therefore type false strictly waits until3, and type true strictly sends at2,
at the quiet input. This holds even if that input is off the equilibrium path.

Alice can unilaterally WAIT0 and WAIT2 and use her own full observation record:

| Actual receipt observation | Inference | Response |
| --- | --- | --- |
| Bob receipt already visible at own2 | b=true, not G | proper guess true at3 |
| empty own2; receipt first visible at own3 | b=true, G | WAIT3; proper guess true at4 |
| empty own2 and own3; receipt first visible at own4 | b=false | proper guess false at4 |

Bob's binding admits even if its private meaning is unusable. The table uses
WHEN Alice observed its receipt, not the packet's timestamp. Under the actual
original fair b and original independent G,L law, her expected payoff is

    1 - (1+q)e(C_A+1)/2 = 181/200 > 1/2.

The opponents' strategy remains fixed at the same quiet input, including when
Alice's deviation reaches it in a seed world of zero equilibrium conditional
weight. Sequential optimality therefore gives every runtime SE Alice value
at least181/200, while every honest source profile gives exactly1/2. This proves
the theorem.

## Immediate-first-failure robustness and limitations

The same argument works if the FIRST commitment failure immediately retires
its attempt and restarts among survivors: Bob6 precedes Alice7, so last Bob
omission still loses -C_B. On proper-Bob reference branches, an Alice miss7
excludes Alice and protected recovery survives Bob. If both admit, no commitment
failure can occur. Publication must still preserve the consumed commitment
block; restarting the entire source program is a different semantics.

The next section gives a DIRECT behavioural implementation satisfying the
optional all-input packet-erasure identity. It does not claim generic closure
of fixed-seed schedulers under mixtures, which would be false. Always-online
clients can send outside activations, including Bob0, and
can ignore the seed-dependent within-clock callback order. This proof does
not establish impossibility for that larger action set, FIFO channels,
independent fixed-delay channels, or a new enforced public-window interface.

## A direct behavioural implementation with all-input erasure blindness

The optional packet-erasure identity can additionally be imposed. Define the
scheduler directly on every finite recall/view input as follows; no mixture
posterior or historical-reachability test is used.

### The exact identity

Write z=(R,v) for command recall and current environment view. Let E_r z erase
all network occurrences of identifier r in every recorded and current input,
pending list, ledger and receipt list, and compress later serials of r's author.
The application component is unchanged. Let restore_r rename an erased-world
include command back to its original identifier; non-include commands are
unchanged. For every pending occurrence x, with r=x.id, we prove

    S(z) = alpha*Dirac(include r)
           + (1-alpha)*(restore_r)_* S(E_r z),     0<=alpha<=1.       (1)

This is stronger than requiring (1) only for packets classified late. It is an
ALL-INPUT statement: pending lists may repeat an identifier with different
payloads, recorded commands may be incompatible with those lists, and clocks
need not agree with the past. No support/posterior argument repairs such inputs.

Erasure is injective on identifiers other than r, preserves their authors and
payloads, and preserves list order. After restoration it is the identity on
those identifiers. It leaves recall length and every application observation
unchanged. An inclusion command remains an inclusion command under erasure;
in particular its conversion cannot turn it into an Alice activation.

### Erasure-invariant control and sending records

Use the padded core/dispatch slot layout of the baseline construction. The
phase-local cursor is recall length minus the first recorded occurrence of
the current application attempt tag, with the current view as the fallback
occurrence. Divide into fixed blocks of twelve dispatch slots and one core
slot. Attempt tags, first occurrence indices and recall length are unchanged
by erasure. Every fake input therefore has a defined, erasure-invariant cursor.

The original G marker is the FIXED core slot4, located using the first original
attempt-tag occurrence. At that core slot, if Alice's original request is
currently ready, use

    q*Dirac(activate Alice) + (1-q)*Dirac(WAIT).

If it is not ready, use WAIT. At subsequent slots set g=true exactly when that
marker exists, has original attempt tag, and its command is activate Alice.
Missing markers and every other command give g=false. This test is invariant
under erasure on ALL inputs. It never infers g from likelihood, pending packet
count, serial counters, or an inclusion command. In a genuine history where
the marker is suppressed by an already resolved Alice event, that event cannot
become ready again in the same attempt, so the missing coin is irrelevant.

For a current pending occurrence m, let t_z(m) and a_z(m) be the application
clock and attempt tag in the EARLIEST recorded view whose input list contains
m.id; default to v when no such record exists. Membership is by identifier,
not by list position or full payload equality. If m.id differs from r, the
first membership index is unchanged by E_r: injectivity on kept identifiers
prevents creation of an earlier match and prevents loss of the old first
match. Its first application clock/tag are therefore unchanged. This also
holds on fabricated histories and with duplicate occurrences.

In this construction eligibility uses ONLY the author, these first-recorded
clock/tag fields, current and recorded application fields, the fixed cursor
and the fixed activation marker. It ignores payloads entirely, which is
stronger than merely preserving them. In particular it never reads absolute
serials, nextSerial, an nth packet, fresh-candidate equality, pending cardinality,
or the presence of any OTHER packet to decide an occurrence's eligibility.
Cardinality appears only in normalization of the lottery below.

### All-input deterministic dispatch

The ordinary due predicate D_z(m) is defined occurrence by occurrence:

* A message first recorded in the original attempt, by Alice at0, becomes due
  at clock1 and the EXACT original core release slot2; after attempt exit the slot condition
  is waived.
* Alice2 becomes due at the exact core release slot8 if g=true, otherwise at clock8.
* Alice3 becomes due at the exact core release slot13 if g=false, otherwise at clock8.
* Original Alice4 is NOT ordinarily due until clock8, regardless of the result
  of the single lottery below.
* Original Bob2 and Bob3 become due at their exact same-clock core release slots6 and12.
* A tail response in its current first-recorded attempt releases at the exact
  following include core slot1 for Alice or3 for Bob. A retired tail label is due.
* Every other off-grid fake label is due immediately. Original release-slot
  conditions are waived for retired coordinates, keeping the stated clock gate.

If a phase origin is b and a core task has index j, its exact release slot is
recall index b+13*j+12, AFTER its twelve padded slots; use a greater-than-or-equal
comparison with that index for a still-pending label. Do not merely compare
floor((recall.length-b)/13) with j: that would release a packet in the padding
BEFORE its designated core task and change within-clock observations.
The clock condition is included in each scheduled-release case. The predicate
reads no packet value or malformedness. In particular ANY raw envelope at an
original response label uses that label's schedule. It is pointwise invariant
under identifier erasure for every surviving occurrence by the preceding
first-record argument. These rules also define a law on fake clocks, marker
commands and attempt histories; no test of historical reachability is used.

At every slot, first choose the FIRST pending occurrence satisfying D, if any,
and include its identifier. List order is permitted here, whereas nth-packet
selection is not: erasure preserves the relative order of ALL remaining
occurrences. If the chosen identifier equals r, (1) holds with alpha=1. If it
differs from r, deleting occurrences with id r leaves exactly the same first
due kept occurrence; the erased command restores to the original command, and
(1) holds with alpha=0. If no occurrence is due, none becomes due after erasure.

On genuine histories, twelve reserved dispatch slots clear old due envelopes
before advancing or taking the next core task. A newly released original or
tail response is selected at its designated core include task, not in its
preceding padding. At most one actual packet has any such response label, and
all older due packets were cleared. Thus delivery occurs at the SAME designated
core task, preserving its order relative to every activation and clock advance.
No fake-input packet-count bound is used in proving (1).

### The single L lottery

Only at the original core slot16, after deterministic due-packet priority, use
the following eligible occurrence predicate:

    H_z(m) iff author(m)=Alice,
                a_z(m)=originalAttempt,
                t_z(m)=4.

The predicate does not select a particular serial or a particular rank in the
pending list. For each identifier j, define the AGGREGATED weight

    w_z(j) = (1-e) * number of pending occurrences m with H_z(m) and m.id=j,
    Z_z = e + sum_j w_z(j).

The lottery is the finite law

    K_z = (e/Z_z)*Dirac(WAIT) + sum_j (w_z(j)/Z_z)*Dirac(include j).   (2)

The sum is over the finite identifier support. Since e>0, Z_z>0 even with an
empty eligible pool. The formula aggregates duplicates BEFORE computing an
include command's probability; pretending every identifier has one occurrence
would fail on fake views.

Erase identifier r. All its eligible occurrences disappear. For every other
identifier j, first-record preservation gives

    w_(E_r z)(erase_r j)=w_z(j),
    Z_(E_r z)=Z_z-w_z(r)>0.

With alpha=w_z(r)/Z_z, each non-r coefficient of
(1-alpha)*(restore_r)_* K_(E_r z) is

    [(Z_z-w_z(r))/Z_z] * [w_z(j)/(Z_z-w_z(r))] = w_z(j)/Z_z.

The WAIT coefficient is e/Z_z. The remaining coefficient is exactly alpha at
include r. Hence (1) holds. If r is not eligible, w_z(r)=0 and the law simply
commutes with erasure. This is a direct measure identity, without any equality
of posterior seed filters.

After this ONE slot, never consult an L outcome or repeat the lottery. Every
remaining original Alice4 envelope is deterministically due at clock8. A
lottery WAIT consumes the slot and advances the fixed cursor. There are no
additional independent trials that could drive its ultimate acceptance
probability toward one.

### Combining the cases

For ANY z and ANY pending identifier r:

1. If deterministic due priority selects r, use alpha=1.
2. If it selects another identifier, use alpha=0 and priority commutation.
3. If priority is empty and this is slot16, use the coefficient calculation
   for (2). Priority remains empty after erasure.
4. If priority is empty and this is the G-marker slot, current readiness and
   the cursor are unchanged, so its two-point activation/WAIT law is identical
   after erasure. Use alpha=0.
5. Otherwise the core command reads only public application, cursor and the
   fixed activation marker. It contains NO hardcoded include identifier and
   is invariant under erasure. Use alpha=0.

These cases are exhaustive on fabricated as well as genuine inputs. Thus S
satisfies (1) for every pending packet, and consequently every late packet.
The proof is not the false generic assertion that mixtures of erasure-blind
fixed schedulers remain erasure-blind.

### Genuine gameplay and preservation of the obstruction

On a genuine raw run there is at most one original Alice response at clock4,
and its network identifier is fresh. Hence the eligible pool at slot16 has
size zero or one. If empty, (2) is WAIT. If it has one occurrence, the denominator
is e+(1-e)=1: inclusion probability is 1-e and WAIT probability e. Tail packets
sent at global clock4 have a different first-recorded attempt tag and do not
enter this pool.

The only genuine nontrivial random SCHEDULER transitions are therefore the one G-marker
choice and, if reached with an eligible packet, the one L-slot choice. They can
be coupled to independently predrawn G and L of the baseline laws. Revealing
G's command marker stores it in the scheduler's FULL command recall, while
players still observe only their own callbacks and shown packets. The independent
L coin is never needed before slot16 or reused afterward. If an event resolves
before a draw, the draw is operationally irrelevant.

This is equality of the genuine raw gameplay law with the corresponding
label-dispatch implementation of the baseline service. It is NOT a claim that
the direct law equals a chosen global fixed-seed mixture on every fabricated
input. Such equality is unnecessary: the target permits arbitrary behavioural
schedulers, and (1) is already proved directly for this scheduler on all inputs.

All original/tail receipts, opportunity bounds, native admission outcomes,
source-seed independence, counted calendars and H1024 completion bounds are
unchanged. Thus the same full-information normal form and 181/200 deviation
prove nonpreservation even with the additional all-input packet-erasure law.
This strengthens the mathematical witness; new Lean certification is pending.
