# Per-author capacity and a compact audit service

Per-author lanes can replace a bound on the number of all possible raw bodies
with a bound on the authorized protocol work and a small audit allowance. They
do not, by themselves, preserve conflict evidence. The sufficient construction
below adds durable authenticated capture and a positive-witness monitor. It
also replaces strategic report-all with a nonstrategic audit service.

This is a mathematical backend alternative for the
[authenticated construction](se-asynchronous-authenticated-construction.md),
under the same ideal authenticated commitments. It does not claim that an
ordinary peer-to-peer transaction pool supplies the required capture service.
It changes the capacity and evidence producer; the proper-core timing theorem
still needs its own hypotheses and proof for the chosen service.

## What a FIFO lane proves

Suppose an honest ingress has already accepted an authenticated body p. Its
author's lane serves at least c work units per block; p needs at most w units;
the work ahead of it is at most Q. Admission creates an immutable queue job,
later jobs append, and other authors cannot consume this lane's allocation.
With a fixed additional ledger-finality bound L, p completes within

    ceil((Q + w) / c) + L

blocks. This is a deterministic bound under arbitrary subsequent flooding.
Indeed, none of that flooding increases the work ahead of p, and every block
removes at least c units until p has completed. Scheduling within a block can
be accounted for by one additional block if the stated c guarantee begins at
the next boundary.

The ordering here is the ingress's actual receipt order. It is not a signed
claim about when a sender emitted a packet. No global emission-order oracle is
used. Replacement of a player's carrier transaction must not remove this
already accepted inner-body job.

If a retained execution has at most H admitted work units from this author
ahead of its current body, use Q <= H. The bound then depends on retained
protocol work rather than the number of raw body variants. Per-author lanes
also prevent this author's flood from delaying another author's admitted job.

This does not establish a bound from a private emission that has not yet
reached the ingress. A later body may overtake it before arrival. FIFO is not
a substitute for that missing routing or capture guarantee.

## Why a first-body-only lane is insufficient

Let p and q be distinct authentic bodies for the same physical slot. The
sender emits p, then q; q reaches a relay first. If the relay retains only q
and permanently discards p, no recipient holding only q can prove a conflict.
Its evidence is also compatible with the legal execution in which q was the
only body ever sent. A sound positive verifier cannot charge the sender on
that evidence alone.

The same problem arises if p was queued but replacement, expiry, or a
sender-controlled priority rule removes it before it becomes collectible.
An identifier, sender-chosen sequence number, or hash of p does not supply
the absent signed body. Publishing a flood body supplies a conflict only
when a different body for that same slot is also available.

This refutes that evidence argument, not every possible equilibrium theorem
for a cancellable network. In particular, an alternative proof would have to
handle the sender's ability to change an earlier, still-unobserved choice at
later information sets. The existing retained-prefix comparison does not
automatically identify that ability with a retained action.

The minimal evidence requirement is consequently:

* an earlier retained-prefix body used in a conflict remains collectible under
  every later deviation;
* every later body whose effect triggers the comparison is either itself
  collectible, or has a separately justified conditional detection bound;
* the collection path and audit deadline cannot be disabled by that author's
  subsequent flood.

The two bodies may arrive in either order. A conflict witness is an unordered
pair and makes no sending-time claim.

## A finite positive-witness monitor

For author i, let S_i be the finite set of physical slots that the controller
can authorize over the whole session, including retries. Let H_i = |S_i|,
and let C_i bound the number of distinct commitment components in those
slots. An actual readiness certificate identifies a member of S_i; a player
cannot mint further certified slots. The body grammar, component references,
immutable binding names, and genuine phase certificates are those of the
authenticated construction.

An honest monitor maintains, separately for each author:

1. a representative body for each slot it has seen;
2. the first binding/component reference using each commitment handle;
3. either no violation, or one complete positive violation witness.

The monitor processes an actual received complete body as follows.

* Reject unauthenticated bytes as evidence against the claimed author. Such
  bytes need separate resource admission; they do not consume an authenticated
  author's reserve by claiming that author's name.
* A genuine body's intrinsic format, ownership, type, or authorization defect
  creates a singleton witness, with the immutable public certificate data.
* An identical canonical body is a retransmission. It does not create a new
  representative, publication job, or offense.
* A different body for an already represented slot creates a two-body witness.
* Reusing a handle for two binding components creates a witness from the two
  indexed components, either in one body or in two bodies.
* Otherwise retain the body and enqueue its one archive-publication job,
  including when its inner action is already stale. The ledger records the
  complete authenticated body; the application executes its inner action only
  if that action is valid at processing time. A late opening therefore becomes
  public even when it cannot complete its former game slot. Archive publication
  and semantic execution are separate operations.

The monitor never needs to infer that no other private body exists. Accepted
binding and readiness certificates supply the positive authorization checks.
For an old slot of an active owner, its public successful-completion record
supplies the existing representative when needed. If the owner did not
complete that slot, the controller must already have excluded it.

Before a violation is found, there is at most one stored body per slot and
one stored first-use reference per commitment component. Thus the monitor
stores at most H_i bodies and C_i handle references for author i. Every
additional distinct current-slot body either fills a previously empty
authorized slot or creates a witness. This bound does not depend on the
number of possible semantic values or fresh handle names.

Upon finding a witness, retain it permanently, enqueue one mandatory audit
job, and mark the author's account as witnessed. Further entries from that
author need no additional archive-publication or audit jobs. The backend may
quarantine their publication and semantic processing. The raw communication
model may still expose their contents to recipients; the one unavoidable charge must
cover the author's entire remaining possible gain. This uses the existing
one-charge comparison, not a claim that a spent binary penalty deters every
later act separately.

Opaque unusable or guard-invalid bindings need not be detectable by this
monitor. They remain subject to the saved-obligation argument in the
authenticated construction: rollback erases the unsaved block; an
irreversibly saved bad obligation forces its owner's eventual exit. The
monitor does not pretend to prove a private guard failure from a handle.

## Capture and audit must be actual service obligations

Use bounded eventual durable capture: each accepted retained-prefix body and
every effectful offending body reaches the monitor in full by a fixed capture
deadline, or its author already has an unavoidable collected charge. The
monitor can stop retaining further bodies after it has persisted a complete
witness. Before that point its capture obligations cannot be cancelled by
later traffic. Private network recipients may receive
copies before the monitor. Its store is not automatically public and its
receipt does not create common knowledge. Players use one partially observed
broadcast primitive; this is not a sender-selected confidential channel and
does not require registration before any peer receipt.

More concretely, let T be the final permitted application-broadcast time and
let Gamma_C bound capture from such a broadcast. All required bodies are then
durably available, or their authors already have persistent witnesses, by
T+Gamma_C. Subsequent audit transmissions use the separate
service allowance; they are not new strategic application broadcasts. This
finite lifecycle is needed to choose a final settlement time.

The bodies may reach the monitor in a different order from their emissions.
An earlier representative is either already stored or a later arrival
completes the unordered pair. If two other conflicting bodies have already
caused a charge, retrieving one particular earlier body is no longer necessary
for the binary-charge comparison. The audit service need not identify which
body was emitted first.

This is enough for eventual evidence, but the private-flight coupling and
proper-publication timing properties must be proved separately. Two numerical
delay bounds do not imply those coupling properties. In particular, removal
of an extra body must not change another body's delivery before the extra
itself has some modeled receipt or service effect. At such an effect the
comparison can stop and use its eventual charge.

The required publication invariant is consequently weaker than publication
of all raw traffic: a retained-prefix body is published by its promised bound
**or its owner has an unavoidable collected charge by final settlement**.
If a conflicting body overtakes it, eventual capture supplies the pair. If
the owner's flood already supplied another pair, that charge is sufficient.
Clean authors keep their proper-body publication guarantees; an author with
a fixed witness cannot demand unbounded additional execution work.

Capture still is a substantive network obligation. A complete body privately
delivered to a player but permanently lost to the audit service is not covered
merely because the player was asked to ignore or report it. An optional
stronger topology captures before fan-out, but it is not needed for the
construction here and is not inferred from ordinary peer-to-peer networking.

For either topology, the audit job has a segregated delivery allowance and
funding that the accused author cannot spend or cancel. Its carrier can be
submitted by the audit service using the service's own transaction sequence.
Actual inclusion and finality by settlement are assumptions about the ledger
service; escrow alone does not prove them. The controller freezes the base
game outcome before final audit settlement and waits for this bounded audit
tail. Later traffic cannot reopen the base outcome or delay the promised
audit job.

## Capacity and funding

Let a_i bound the encoded work needed to publish one application body from
author i, including its bounded component vector. Let e_i bound the encoded
work needed for one complete singleton/pair witness and its verification.
The maximum archive-publication-plus-audit work of the monitored backend is

    sum_i (H_i * a_i + e_i).

This bound covers arbitrary raw contents and multiplicities in the declared
finite domain. Before the first witness there are at most H_i distinct
representatives; after it the monitor adds no new archive-publication jobs and
only one audit job. Exact retransmissions add no ledger work. A witness can publish
a previously unpublished retained body as one of its two members; the bound
already permits both full bodies in e_i.

If each author has a reserved archive-publication lane of c_i work units per
block, the worst total queued work for that lane is at most H_i*a_i. A first proper
body's deadline can therefore use that finite queue bound, or a smaller
bound proved from the fixed-window spacing. An audit lane of rate c_A drains
all author witnesses within

    ceil(sum_i e_i / c_A) + L_A

blocks after the last eligible witness is captured. L_A accounts for finality.
That allowance is reserved independently of publication-lane flooding.
Thus T+Gamma_C+ceil(sum_i e_i/c_A)+L_A is a sufficient final audit time.
A clean body's broadcast-to-publication bound is its capture bound plus the
proved publication-lane bound. The controller's deadlines and publication
interval use that total bound, not merely the final ledger step.

Reserve the corresponding bounded publication and audit fees for each
author before play. Quarantine ensures that a sender cannot consume an
unbounded sponsor budget by cycling through different conflicting bodies.
The witness allowance is separate from the refundable deterrence deposit;
either the author funds both or an explicit sponsor funds the service cost.
Proper-play service costs must be refunded or excluded from the intended
utility comparison, exactly as in the base construction.

These are ledger-work and stored-evidence bounds. They are not a claim that
processing an unbounded incoming byte stream is free. Authentication and
initial intake still require per-principal rate isolation, a bounded envelope
domain, or another explicit denial-of-service assumption. A valid packet
which never passes an overloaded capture boundary has no liveness guarantee
from the ledger lanes alone. Rate limiting before capture is safe for this
proof only if rejected traffic has no strategic external effect, or if the
earlier admitted prefix and relevant evidence retain independent delivery.

The construction scales with the maximum authorized execution, including
bounded retries, rather than just the selected equilibrium path. It removes
the multiplicative dependence on all possible values and labels. It does not
remove the necessary dependence on the program's actual size, maximum vector
size, number of players, or possible retries.
These are service allocations, not exclusive player sending turns: all players
may broadcast asynchronously. The reserved rates must fit the ledger's actual
capacity, and larger workloads require longer deadlines or a larger declared
reservation. Correct-body encoding and verification must also satisfy the
proper-core payload-independence conditions; a value-dependent service cost
cannot silently be treated as constant.

## Audit-service comparison and equilibrium extension

Keep the finite ideal raw game, bounded base utilities F_i <= u_i <= U_i for
active terminals, and permanent excluded-owner base payoff F_i. The actual
authenticated construction supplies a causal retained comparator which is
quiet and audit-clean after its stopping event, hence obtains at least F_i.
Its separate hidden-binding argument handles save or exit before an auditable
effect. The monitor replaces only the collection producer in that comparison.

Let E be the first externally effective forbidden entry before those other
stops. Before E the raw and retained runs have the stated causal coupling.
On E the monitor eventually has a singleton witness or a pair consisting of
the offending body and a durable retained-prefix counterpart. Its protected
audit job causes a charge D_i with certainty. Therefore, conditional on any
copied information set and under any later raw policies,

    expected raw payoff - expected comparator payoff
      <= (U_i - F_i - D_i) * Pr(E).

The other stopping branches have raw payoff at most F_i and comparator payoff
at least F_i. Thus D_i >= U_i - F_i suffices. There is no assumption that E
has a uniformly positive probability: bodies with no effect before exit need
not be charged for this inequality. The comparator and witness existence,
rather than the size of Pr(E), are the substantive premises.

With this audit service there is no strategic report choice, no report-all
equilibrium lift, and no reporting perturbation error. Evidence collection is
a chance/service transition with a verified outcome, not a player incentive.
The generic continuation-extension argument still supplies equilibrium play
at newly admitted information sets once the retained SE and these comparisons
are established. This backend therefore does not require every player to
report others' traffic at the end of the game.

A weaker service with conditional collection probability at least q_i > 0
can use q_i*D_i >= U_i-F_i, provided the bound holds after every copied
information set and every triggering exposure, under every later raw policy.
An ex ante chance of some watcher receiving a packet does not imply that
conditional statement. For pair offenses the service must also retain the
other body. Independent one-body reception probabilities cannot repair an
information set at which the only prior counterpart has already disappeared.

## What carries over, and what does not

The positive-witness classification and first-exposure comparison carry over
to this monitor. Durable capture replaces eventual publication of every raw
body as the source of the earlier conflict counterpart; a small mandatory
audit job replaces the full foreign-evidence bundles. The public readout on
proper paths is unchanged when the monitor finds no offense.

There is a useful smaller capacity producer before the first public exit.
Suppose each fixed window needs at most one first body per author, no later
window becomes ready before the present one settles, successful completion
requires actual recording, and a missed completion immediately publishes an
exit. Then an exit-free retained prefix has at most one outstanding first-body
job per author. Every earlier window completed, so its author's body was
already recorded; the current window contributes at most its one first body.
Initial source commitments are installed state, not queued publication jobs.
Exact retransmissions add no job; their pending gossip occurrences must not
consume the protected inclusion-lane allocation. An author lane able to record one maximum-
size body per block can therefore realize the same individual inclusion
kernel on such prefixes without reserving capacity for all raw alternatives.
If the desired kernel includes positive chances of deferral, the lane may
leave unused capacity; the capacity bound does not force prompt inclusion.

This observation is independent of whether the proper-core theorem retains
or removes its delayed-delivery support hypothesis. Capture and inclusion
must jointly realize that theorem's specified kernel. Once an extra raw body
affects its author's lane, the eventual-witness comparison handles the
resulting continuation rather than requiring the lane to emulate independent
service for an arbitrary number of raw bodies. The retained handler after a
public exit must be defined and completed for this monitored backend; it is
not silently identified with a different unlimited-capacity game. In the
audit-clean-handler route, the retained handler permits structurally authorized
choices, including hidden bad semantic values, and the final extension adds
positively auditable bodies at handler sites as well. The monitor and the
saved-obligation comparison apply to that choice of intermediate game too.

Per-author isolation provides noninterference between different authors'
archive-publication work. It does not by itself preserve the law of another job from
the same author, nor prove the proper-core timing equilibrium. The stopped
comparison can tolerate own-lane interference once a captured forbidden body
makes a charge unavoidable; before that stopping event the chosen ingress,
queue and observation kernel must supply the required coupling. The model
also needs its previous-proposal publication barrier on retained paths.

No new common knowledge is postulated. Only actual ledger records, including
any published witness, are public. The additional assumption is an honest,
durable and appropriately isolated capture/audit service. Without either that
service or a proved strategic-reporting replacement, per-author lanes alone
do not supply the evidence theorem.
