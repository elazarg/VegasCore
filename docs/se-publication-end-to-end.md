# End-to-end preservation for a registered blockchain service

The implementation specified here compiles a finite intended commit–reveal
game to an authenticated, funded broadcast service with a public ledger.
Mempool reception stays private. Every admitted transmission is registered
durably and then published, including rejected game calls. Deposits remain
locked until publication and automatic auditing finish.

The preservation claim is mathematical, not Lean checked. Its source padding,
native action classes, probability transfer, authorization, replay and settlement
arguments are derived in the companion documents linked below. The construction
gives one complete finite service instance. It does not assert preservation for
an arbitrary hidden service tape, an ordinary unreserved mempool, or
unregistered private communication.

## Fixed inputs and the theorem

Fix a source setup satisfying the existing finite intended-game hypotheses:
a finite player set, a finite supported joint initial law, finite binding
choices, successful initial commitments and source well-formedness. Correlated
private inputs are allowed. Fix the source payoff and public readout. The
expression language must supply the constant distributions and context
transport constructed in
[the padding specification](se-publication-padding-mathematics.md).

For a direct monetary implementation, take the source payoff to be a bounded
transfer in the currency's base unit, computed from the public settled readout
rather than private ghost fields. Use permanent
exclusion with the current theorem's payoff-floor conditions. In particular,
an excluded player's base utility is a fixed F_i under every subsequent
profile. This is a condition on utility, not merely on its cash payment.
The more general quasi-linear version requires separately specified intrinsic
valuations, cash transfers and a realizable fixed excluded utility; see
[the settlement construction](se-publication-audit-implementation.md).

Fix, before selecting a source equilibrium:

* the padded compiler and canonical packet format;
* the public transport calendar, deadlines, finite message/candidate bounds
  and all storage and processing reservations;
* the actual finitely branching private reception rule;
* ideal authentication and opaque, binding commitment capabilities;
* the audit predicate, payout funding, segregated deposits and settlement rule.

**Finite registered-service preservation theorem.** For every sequential
equilibrium of this intended source game, the raw game of the implementation
below has a sequential equilibrium preserving the joint law of the original
initial inputs, original typed terminal state, original public result and
realized net-payoff vector. The selected implementation equilibrium has no
exclusions or audit charges. Auxiliary padding cells, transport metadata and
the final forced audit tail are erased by the specified observation map.

The implementation and deposits are independent of the selected source SE.
Only its preserving strategy and belief construction depend on that SE.
The raw strategy space includes every bounded constructible authenticated
strategy, including malformed submissions. The selected profile is sequentially
rational against all such deviations.

## The service instance

Use a public cycle calendar. Every cycle has these phases:

1. An atomic processing batch records the whole pending occurrence queue.
   It interprets each distinct protocol entry at most once, in first-admission
   order. Repeated occurrences are still recorded but do not execute again.
2. Every player has one callback, in a fixed public order. The player may
   submit one occurrence or remain silent.
3. The existing one-sample slot, event-expiry slots and clock advance run.

No player decision or private learn step interleaves with a processing batch.
Every admitted occurrence from one cycle is recorded at the next batch.
The processing and activation gaps are therefore one cycle. This is a
transport schedule: source phases still become ready according to execution,
guard results, expiry and rollback. It does not assign each source move a
predetermined calendar slot.

At its callback, a player receives the actual private reception draw from
pending transport data and retains its previous receipts and literal own
actions. Reception may inspect contents, authors and occurrence metadata.
It cannot inspect an untransmitted commitment preimage or another player's
private preparation store. The fixed law may be arbitrary within this interface;
it is not required to reveal every pending entry.

An admitted occurrence has an immutable transport identity. A protocol entry
has a separate immutable identity determined by its canonical authenticated
body. A relay of an existing entry creates another occurrence of that entry;
it is not another signature by its original author. Both identities and every
observed receipt are retained in the model.

Admission appends the occurrence to a durable queue **before** any modeled
recipient can receive it. Rollback, semantic rejection, expiry and exclusion
cannot delete that queue entry. The reserved service is prepaid; inner invalidity
or a player's choice of an insufficient fee cannot make a visible entry evade
registration. This is an explicit storage and delivery contract for the chosen
service, not a property inferred from the word “mempool”.

Authentication uses ideal capabilities, as in the current runtime: malformed
terms are available, but a player cannot manufacture another principal's
signature or a future ledger authorization. The theorem is not over all
bit strings with computationally unbounded signature forgery. Replacing these
ideal capabilities by concrete cryptography requires a separate computational
or approximate result.

## Compiler and resource calculation

Insert three fresh deterministic public samples after each maximal reveal
block that has a later commitment block. This is the processingGap+2
construction specialized to processingGap=1. No original commitment block
is split. Choose every owned event's deadline to satisfy the existing strict
margin 1+1+2<deadline; five cycles is one uniform choice. Padding samples may
have deadline zero because they are ownerless and cannot expire.

For original event count n and number r of inserted padding boundaries, put

    N = n + 3r
    W = (N+m)(N+1) + N
    C = (W+1)(Dmax+2)
    B = mC
    w = B+m+N+2
    H = Cw.

Here m is the player count and Dmax is the expanded runtime's maximum
deadline. These are the completion, occurrence-capacity, cycle-width and
command-horizon bounds from the
[padding calculation](se-publication-padding-mathematics.md). Choose the
candidate reserve at least H. All finite alphabets and reservations are fixed
before the source equilibrium.

There are at most mC chosen transmissions, including malformed messages,
historical first admissions and visible replays. Thus capacity B suffices to
clear every batch. With an empty initial queue the sharper per-batch bound m
also works for this concrete calendar, but using B reuses the existing full
processing calculation. Bigger batches add no owner callbacks and create no
circular traffic bound.

If a reveal block closes at cycle c, the three samples cannot all execute
before cycle c+2. The next binding callback is at cycle d>=c+3 because owner
callbacks precede the sample slot. The batch at c+1 records all openings
already submitted when that block closed. For any reached later binding,
c+1<d<C, so this batch lies inside the actual finite execution.

The usual chance instructions are public. For the concrete expression language,
one can implement a rational weighted table by a fresh uniform integer and
its cumulative-count map. A common denominator of the finitely many syntax
tables gives one finite random-word alphabet; deterministic samples are its
constant maps. The sampling service draws a fresh independent word and publishes
its mapped output at the sample slot, giving exactly the specified conditional
distribution. If it also publishes the underlying word k, this adds public
noise: conditional on the public branch and output y=f(k), k is uniform on
the fiber of f over y. That likelihood is independent of private state.
Lifting the entire source consistency sequence to ignore the residual word
therefore preserves beliefs, gains and original outcome laws; there is no
decision between drawing the word and publishing its output. The initial private-type
prior is an environmental input shared by source and target, not a lottery
that the compiler must reveal or resample.

## The ledger state machine and its private ghost state

The contract need not store a commitment's secret value. Its executable state
contains the public completion/phase record, accepted opaque handles, public
openings and samples, exclusions, clock, activation times, public checkpoints,
retired public summaries and authorization records. The typed hidden source
store and private candidate catalogues are proof state maintained by the
compiler simulation, not publicly readable contract storage.

The transition rules are:

* Record an admitted occurrence regardless of the inner action's validity.
* For a new timely current binding, check its owner, event, current phase,
  vacant event binding and nonuse of its handle in the live accepted table;
  install the opaque handle and complete the binding event.
  This public update does not inspect its hidden preimage.
* For a new timely current opening, check its certified handle and opening
  witness, decode the typed value, publish it and evaluate the now-public
  guard checks. Perform the existing failure/exclusion transitions.
* For a public sample, execute its finite specified distribution and record
  its output. For expiry, apply the existing timeout/exclusion rule.
* Normalize phases and restore the existing public checkpoint on commitment
  rollback. Preserve exclusions, registered traffic and private opening
  capabilities; do not reopen an earlier reveal phase.
* Treat stale, malformed, duplicate and otherwise rejected calls as application
  stutters. Their occurrences and audit evidence remain recorded.

These are the public counterparts of
[EventApplication](../Vegas/Pending/EventApplication.lean) and
[PhaseApplication](../Vegas/Pending/PhaseApplication.lean). Source guards have
no direct private-input reads and are checked only when their commitment
reads have been published; see [Basic](../Vegas/Source/Basic.lean).

The simulation relation says that public fields are the public projection of
the typed ghost state, every accepted handle denotes its fixed private
candidate, and every public opening agrees with its certified preimage.
It holds initially. Binding preserves it by installing the same handle while
the ghost step stores its private decoded value. Opening preserves it by
binding of the commitment and identical public guard evaluation. Samples,
expiry and normalization perform identical public updates. Rejected calls and
repeated occurrences leave both application projections unchanged.

The live-table handle check is the current contract check. Global handle
nonreuse across retired attempts is the separate count/audit condition;
literal agreement with the native raw transition does not assume that a
retired handle remains in the live table.

Private construction or signing of an untransmitted body is strategy memory,
not a new public operation. At a binding body's first admitted transmission,
register its fixed chosen preimage, or its unusable result, in the ghost
catalogue exactly as the current submission does. Subsequent references
cannot change it. A held body keeps its own fixed preimage; a different body
is a different raw alternative, subject to handle/event conflicts. This lazy
registration represents arbitrary private planning available from perfect
recall without adding externally visible precommitment steps. Arbitrary
unregistered exchanges of those bodies are outside the communication model.

On arbitrary raw histories, extra transport occurrences do not suppress any
clock, sample or expiry slot. Every accepted fresh game call is an existing
runtime transition; an invalid or stale call is a stutter. The existing
finite progress bound therefore remains valid with the recomputed capacity.
Public simulation does not claim that everyone learns the private ghost state.

## Permanent authorization without a trusted sender stamp

At each actual ready installed physical event, the ledger issues its canonical
authorization. It fixes session, physical phase/attempt, event and owner.
For an opening it also fixes the accepted binding handle. An initial binding
setup certificate authenticates that binding; it does not replace the later
resolve-phase authorization.

A sender can retain an authorization forever, create a new message using it,
choose an old attempt in raw syntax, or replay a previous authenticated entry.
The contract does not rely on a wallet overwriting these choices with its
current state. Sender-chosen nonce order does not determine which binding an
opening certifies.

A rollback that never installed its reveal phase produces no authorization
for that physical reveal. Another attempt's certificate cannot validate its
opening or its different handle. The precise serial-gap attack against a
naive attempt-free token, and this repair, are derived in
[the authorization specification](se-publication-authorization.md).

Authorization records add no hidden information on retained histories.
With the public calendar, successive ledgers identify the preceding complete
batch. The retained public sample output and fixed expiry/clock commands
determine the intervening public transitions. Binding public effects ignore
hidden preimages; correct openings expose the values used by their guards.
Induction reconstructs every intermediate public ready/phase/accepted-handle
state from the player's original own recall. Its canonical authorization
wallet and certificate bytes are therefore functions of that recall. The
full derivation, including source-public samples and rollback, is in the
authorization document.

## Visible replay and the privately observing counted equilibrium

Application idempotence alone does not make replay strategically irrelevant.
A second receipt or its timing can communicate information. The construction
therefore keeps those observations and gives every legal replay positive
probability at each consistency index.

The [transport proof](se-publication-end-to-end-review.md) derives:

1. A complete-observation player's own recall reconstructs the entire base
   transport word before its callback. Between successive own callbacks,
   every other owner has exactly one opportunity, and every base emission
   remains in the ledger or current complete pending pool.
2. Along a fixed masked base history, the semantic action factors are those
   of the existing fine reference sequence. Private reception, literal
   response aliases and replay choices are normalized auxiliary kernels.
3. Foreign private preparation aliases sum out. Replay choices use transport
   knowledge rather than hidden source values. The focal private alias memory
   is reconstructed from its fine own spine and its simulated own record.
   The remaining likelihood is K_i,n(F,I), constant on each fine information
   fiber F.
4. Thus the actual Bayes posterior is a mixture of the original fine
   posteriors. Every literal action, including a replay of a still-pending
   known entry, has the corresponding controlled continuation law.
   Replays project to WAIT.

Consequently each actual conditional local gain is exactly

    G_actual,n(I,a) = sum_F Pr_n(F | I) G_fine,n(F,pi_I(a)).

The existing fine construction has a uniform bound epsilon_n->0. This equation
transfers it without dividing by a limiting information-set probability.
One subsequence of the actual fully mixed Bayesian assessments gives an SE.
The projected initialized terminal law agrees with the fine reference law at
every index; that reference law converges to the selected source SE's law.
Replay rates
can tend uniformly to zero, so the selected limit has the original no-replay
execution law as well.

This argument includes the native wrong-typed preparations, evidence aliases,
failed guards and retries through
[the exhaustive counted adapter](se-publication-native-adapter.md). It does
not restrict deviations to source-independent replay choices: only the proposed
sequence uses those choices, and every legal alternative is compared.

## One extension to all raw actions

Let R be this private counted game with visible replay. Let G allow every
bounded constructible authenticated body, including fresh messages using old
authorizations. Use the canonical singleton/pair audit:

* intrinsic format, ownership, type, authorization or opening-proof defects;
* two distinct authenticated entries for the same physical event;
* two distinct binding entries reusing the same prepared handle.

An identical-entry relay is not a conflicting second signature. All reports
refer to actual entries; forged accusation is unavailable. These witnesses
remain true after more traffic is appended. Every R history is audit clean.

Keep private construction material in the strategic action and own recall,
even though it is absent from the public wire body. In particular the retained
preparation and evidence-alias syntax embeds injectively; materializing an
identical packet does not identify two literal private actions. G extends this
same action type with historical and malformed constructions. On the retained
image, initial state, transition, receipt kernels and terminal readout agree;
the canonical-certificate readback supplies the information correspondence.
These are the history, information and dependent-menu maps of the action
restriction, rather than a map of terminal outcomes alone.

At an embedded R information set there are only two comparator cases.

**The actor is active.** An extra new body has one of those witnesses. A
well-certified unused current request is already in R. A closed event of an
active owner already has its completing authenticated packet; a different
body conflicts with it. An event from a never-installed phase fails
authorization. A first registration by a different author is impossible:
foreign entries become known only through their earlier registered admission,
and retransmitting them is already a replay.

**The actor is excluded.** Every subsequent base utility is F_i, including
after a newly disclosed old value. For any nonnegative audit charge and
deposit, its expected net utility is at most F_i. Its clean R continuation
pays exactly F_i. No lower bound on the probability of charging this extra
action is required.

The public exclusion flag makes this case split constant on the information
set. Choose bounds L_i<=u_i<=U_i covering all protocol states, including
defaults and exclusions, and deposit D_i>=U_i-L_i. The final audit collects
every active-actor witness with probability one. Its gain comparison is

    expected raw net utility <= U_i-D_i <= L_i
                             <= expected clean continuation utility.

For an excluded actor the direct comparison is instead

    E[F_i-D_i*charge_i] <= F_i.

Both hold for every compatible belief and every later raw policy.
Instantiate
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
from [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean),
classifying the active case as collection-enforced and the excluded case as
directly compared. Its source continuation is the clean R continuation.
There is no claim that a continuation after a past raw charge still pays F_i.

This single theorem gives consistent rational behavior at all new information
sets, including survivors' asymmetric knowledge after an excluded player's
old disclosure. The current-phase source-archive decoder is used only to
construct R; it is not asserted at those new sites.

## Final publication, audit and realized payments

Close the registered gameplay interface after its C cycles. Freeze its base
game state. Run one further archive-only processing batch with capacity B:
it records the last pending occurrences and cannot execute late game actions.
No player action interleaves with the tail. The ledger now contains all
admitted traffic.

A funded deterministic scan verifies each body and the event/handle pairs,
then records the audit verdict and settles. A quadratic scan of the bounded
entry set is sufficient; its storage and computation are reserved before play.
Thus both evidence observation and verdict delivery have probability one,
conditional on every actual traffic record. No player needs to report or to
expect a reporting reward.

Append this same deterministic frozen tail to R before constructing the
action restriction. It adds no decision, preserves decision beliefs and
base payoffs, and makes terminal histories align. It is not legitimate to
embed an already terminal source history into a still-running target prefix
without this step.

For monetary payoffs, separately lock

    K_i >= max(0,-L_i),       D_i >= U_i-L_i.

The sponsor funds the positive payout reserve sum_i max(0,U_i) and the
entire fixed service cost. Audit escrow cannot be consumed by fees or a base
liability. Settlement returns

    D_i + K_i + u_i(s_close) - D_i*charge_i.

This is nonnegative. Subtracting the original K_i+D_i payment gives exactly
the asserted net payoff. On the selected equilibrium law every charge is zero.
The sponsor's fixed service cost is outside the players' declared game utility;
variable gas costs deducted from their winnings would require a different
source payoff model.

The source-padding map erases fresh constant cells. The replay map erases
auxiliary transport occurrences. The raw extension preserves the entire
embedded terminal-history law and its payoff vector. Composing their readouts
therefore preserves the original initialized joint law, including realized
payments rather than just their expectations.

## Receipt-based late charges are optional

A sound additional rule charges a previously unrecorded opening when its
earliest actual ledger record r is later than x+Delta, where x is its event's
public settlement time and Delta is the proved recording bound.

Every retained current-phase send occurs at s<=x. Bounded recording gives
r<=s+Delta<=x+Delta, so this rule has zero charge on every R history.
For excluded-owner extra actions, even a random charge satisfies the direct
F_i comparison. Replays use the entry's earliest record, not a later repeat's
timestamp. An opening of a never-installed reveal phase still needs the
independent authorization check; a retired phase's timestamp alone leaves
a slack interval and does not prove every such packet chargeable.

The primary construction does not need this additional late charge.
Its mathematical compatibility is established in
[the audit implementation](se-publication-audit-implementation.md).

## What is supplied, and what the model idealizes

The compiler, legal packet classes, historical authorization, visible replay,
raw-action comparison, final audit and escrow are specified above with their
proofs. They are not left as uninstantiated information-sufficiency or audit
coverage hypotheses.

The external primitives are explicit: authenticated registered communication
with bounded durable delivery and reserved capacity; a finalized public
ledger; ideal cryptographic capabilities; the source's public chance law;
and the declared funding and utility model. They are reasonable objects for
an idealized service theorem but are stronger than an arbitrary blockchain
network. In particular:

* A hidden correlated processing calendar requires an additional replay
  information argument. The public-calendar instance is the one proved here.
* Arbitrary unregistered private disclosure is a larger communication game.
  [The audit analysis](se-publication-audit-implementation.md) gives a finite
  verifiable-disclosure obstruction when that channel is unreported and cannot
  be penalized soundly.
* Concrete cryptographic security, probabilistic finality, fee competition,
  unavailable capacity, and action-dependent physical costs require their
  corresponding refinement or approximation. They are not consequences of
  the exact finite theorem.

No impossibility of the unpadded current compiler is established. The
implementation here is a concrete sufficient design for the original intended
game under the stated service, not a claim that every restriction is necessary.
