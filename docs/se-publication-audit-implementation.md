# A finite registered-broadcast audit and settlement backend

This document constructs the audit service for a closed, authenticated session
broadcast network. Every admitted session envelope is retained and eventually
recorded on the ledger, including envelopes whose inner game action is malformed.
Private mempool reception may reveal any supported subset of pending envelopes;
the ledger alone supplies public publication. The construction derives complete
audit collection from this transport and an explicit final drain. It does not
postulate `EvidenceCoverage` as an unexplained property of a private observer.

The mathematical statements are finite hand proofs. They have not been assembled
in Lean. The primary service uses the original source program: its full processing
batch before every callback block already gives publication, with no inserted
samples. The counted-game ingredients are in
[the native adapter](se-publication-native-adapter.md) and
[causal transfer](se-publication-transfer-mathematics.md). The separate
[audit boundary](se-publication-audit-boundary.md) explains why retained old
signatures require an action extension. The
[publication-padding construction](se-publication-padding-mathematics.md) remains
a sufficient alternative for a service with processing gaps; it is not required
by this primary every-cycle construction.

## The communication and payment model

Fix a finite set of registered players, a compiled finite game, a finite session
identifier, bounded wire alphabets, and a finite gameplay horizon. An outer
session write authenticates its principal and contains a bounded byte string.
Inner parsing, game authorization and game acceptance happen after admission.
In particular, an invalid guard, invalid opening, stale attempt, wrong game
certificate or malformed inner call does not prevent durable registration.

The transport contract is concrete:

1. Each scheduled owner callback admits at most one outer write, or silence.
   All such writes have been funded before the session starts. Choosing an
   underpriced transaction is not a way to make a message visible without
   registering it.
2. Before an envelope is made available to any modeled recipient, the session
   transport appends it to its durable admission log and pending queue. Its
   principal and fresh registration identifier cannot be changed by the sender.
3. The admitted body remains recoverable until it is recorded in the ledger.
   Application rejection, rollback and owner exclusion do not delete it.
4. The reserved processing rule includes every pending envelope, independently
   of inner validity, under the stated bounded service and capacity guarantee.
5. The ledger has finality and authentic, publicly verifiable contents. A
   recorded envelope cannot later disappear or be substituted.

These are delivery, storage and authentication assumptions about the chosen
session service. They can be implemented by a funded inbox or data-availability
service with the same guarantees. An ordinary public mempool with discretionary
admission, fee starvation or unbounded censorship does not satisfy them merely
because it is called a mempool. The transport may keep an admitted packet private
until its inclusion; no pending contents become common knowledge by assumption.

The game contains only this registered communication interface. A privately
communicated plaintext outside it is a different action and observation model.
The last section gives an exact obstruction to extending the theorem to arbitrary
unobservable private disclosures.

Use the same base utility function as the source implementation. The audit adds
one additive penalty per charged player. To realize these quantities as money,
assume that the designated payout is contract-computable and that the player's
utility from an escrow deduction is the stated additive deduction. For a digital
currency, exact contract payouts and deposits must be representable in its base
unit. Bounded subjective utility alone does not imply a corresponding monetary
deposit: the utility of losing money must also be specified.

## Canonical packet grammar and authentication

A semantic packet body has the following bounded fields:

    session, principal, physical attempt, source event,
    kind, prepared/accepted handle, optional typed opening,
    phase authorization, opening certificate.

The kind is binding, opening, or a bounded malformed encoding. Bindings carry an
opaque handle, with no opening value or opening certificate on the wire. An
opening carries its exact accepted handle and typed value. There are no optional
padding strings, freely chosen sender nonces or ignored memo fields in a clean
body. Their presence is an intrinsic inner-format violation. Private preparation
syntax remains local, as in the existing runtime.

Authentication is idealized in the same sense as the existing certificate
model: a player can authenticate its own body; it cannot create another player's
signature or a false ledger/capability certificate. Forwarding preserves the
original authenticated body. All initial authenticated material is specified by
the session setup. In particular there is no initial stock of unregistered
future protocol packets held by other players.

Responsibility is attached to the authenticated outer writer. A new wrapper
claiming a different principal is a defect of that writer; it does not frame the
claimed principal. Passive network forwarding does not create another player
action. An exact copy of an already registered canonical envelope uses the replay
rule below rather than acquiring a new responsible principal.

The canonical body, rather than signature randomness, determines its immutable
protocol-entry identity. The ideal authentication representation is unique; an
arbitrary metadata variant is either the same canonical entry or a new malformed
entry, not an unaccounted signaling field. A transport occurrence has a separate
identifier and records its broadcaster. Replaying a known entry creates a real
occurrence whose receipt and metadata may be observed and whose bytes are logged.
It does not mutate the entry, consume a new semantic nonce, register a new
candidate, or apply the game action twice.

The primary backend uses a deterministic public calendar: one processing batch
per cycle followed by exactly one callback per owner in a fixed order. At a
nonemitting callback, a player may retransmit any entry it actually knows through
own earlier admission, ledger inclusion or private reception. First admission of
a previously unregistered signed body is not a replay. The controlled replay
construction in [the end-to-end review](se-publication-end-to-end-review.md)
proves an SE extension for these observable occurrences, including replays of
known still-pending entries. Its transcript likelihood proof uses the fixed
calendar and must not be generalized to arbitrary hidden service tapes.

An optional simpler backend can instead suppress exact replays before all
observation, queueing and receipts. That requires genuinely invisible ingress
deduplication; ledger-only deduplication is insufficient. The primary construction
does not assume that retransmissions are invisible.

For each new canonical body the transport assigns an outer registration serial.
These serials reflect first registration order and are strictly increasing for
each author. A previously signed inner nonce cannot choose or rewrite this
order. Occurrence identifiers, including a different relay broadcaster, do not
change the original entry serial. The audit below uses unordered distinct-entry
pairs and does not need to date the inner signature.

### Authorization means an actual installed phase

A phase authorization is a finalized ledger certificate of the session's actual
installation of that physical phase and the event's actual readiness for that
unexcluded owner. It binds the attempt namespace, event and completed
prerequisites. An opening authorization additionally identifies the accepted
handle for that resolve event. The public certificate is derived from the ledger
state machine; it is not a sender's claim that a hypothetical phase would be
ready. Merely certifying the containing phase is insufficient if the owner's
event is not yet ready within that phase.

Certificate verification is a fixed predicate on authenticated certificate
contents and their finality proof. Its result does not depend on when a packet
is eventually delivered. A sender may retain a genuine authorization forever.
An abandoned commitment attempt that never reached its reveal phase has no
reveal authorization. A publicly predictable attempt name or an owner signature
alone is not such an authorization.

Initial commitments use the corresponding setup certificate to authenticate the
initial handle/value binding only. Opening that initial commitment still requires
the actual phase/readiness authorization of its resolve event. Both certificates
are required; setup certification does not authorize early disclosure. A current opening
must identify the accepted binding certified for its physical resolve event;
claiming a different handle is an intrinsic mismatch. Opaque binding content may
be unusable or fail a source guard. That is a permitted game choice, resolved by
the existing exclusion semantics, rather than automatically an audit violation.

The ideal authentication capability is causal: an authentic certificate can first
be held only after the certified ledger event occurs. Arbitrary raw strings are
not guesses which may later become valid certificates. In a symbolic model, held
authentic capabilities and permanently invalid encodings are separate cases;
there is no operation that manufactures a future authentic capability from its
predictable event name. A cryptographic implementation replaces this idealization
with its forgery/guessing security bound. Merely checking at settlement that a
predictable phase label eventually appeared would not give persistent evidence:
that would allow premature guesses to become retrospectively valid.

The public certificate mechanism must be included in the compiler's actual
ledger state machine. It cannot be replaced by an axiom that a sender's token
has a phase-reach provenance which the implementation never records.

Certificates have canonical proof representations and no optional timestamps,
private scheduler data or random metadata. At a retained current callback, the
certificate contents and its availability are determined by the ordinary public
view and retained own recall: installed phase, attempt, completed prerequisites,
exclusion status and accepted handle. The cycle-by-cycle reconstruction in
[the authorization analysis](se-publication-authorization.md) proves this for
the primary public calendar. Each new ledger suffix is the preceding cycle's
complete batch, each public sample writes one retained cell, and bindings,
certified openings, expiry and rollback have publicly reconstructible effects.
Thus even original private own recall reconstructs the canonical issuance archive
without access to private pending receipts. This supplies the observation square
of the retained-game embedding. Publishing a richer historical
trace or allowing certificate lookups that reveal additional information requires
a separate information-transport proof; authenticity alone does not prove that
square.

## A persistent audit predicate

Let T be the finite set of distinct registered authenticated protocol entries,
obtained by deduplicating the full occurrence log. The audit
charges a principal if T contains one of the following witnesses:

* **Intrinsic defect:** its signed body has a noncanonical format, incorrect
  session, wrong event owner/type, forbidden initial handle, malformed inner
  action, invalid authorization, invalid opening certificate, or a handle/value
  inconsistent with the included accepted-binding certificate.
* **Repeated physical event:** two distinct signed bodies of that principal
  address the same physical attempt/event.
* **Reused prepared handle:** two distinct signed binding bodies of that principal
  use the same prepared handle, even in different attempts or at different events.

Every witness consists of one or two actual signed bodies and fixed public
certificate data. No witness asserts that a signature was created at a particular
time, that a packet was not received by someone, or that an unobserved message
does not exist. A guard-failing but well-certified opening is not in the first
case. Retransmission of the same immutable entry, even by another broadcaster,
does not create a distinct-entry pair and is not charged.

Write Bad_i(T) for the disjunction of these witnesses for principal i. Then

    T subset T' and Bad_i(T) imply Bad_i(T').

Proof: retain the same one or two signed bodies in T'. Intrinsic verification
uses their fixed contents; a repeated-event or reused-handle pair remains a pair.
Thus later registrations, nonce reordering and later exclusion cannot repair
the witness. This is the persistence fact needed after a first forbidden action.

The full-log predicate can be evaluated by a deterministic scan. Index bodies by
principal/event and principal/prepared-handle; verify their fixed certificates
and mark a Boolean charge. A quadratic pair scan is also sufficient because the
session traffic bound is fixed. No player chooses the verdict, and no reporting
reward or voluntary watchtower action is needed in this backend.

### Why an active owner's first extra packet creates evidence

Start at a history of the retained, audit-clean game. A transmission has
three possibilities.

1. It is a current well-certified counted response, using a fresh prepared
   handle when binding, or a known immutable-entry retransmission. Its action
   is already retained. A replay creates no new entry in T.
2. It is a genuinely authorized first response for a past request of an already
   excluded principal. Its surrounding phase may still be open after the owner's
   own request expired. A direct payoff comparison handles this case, whether
   the final audit charges it or not.
3. It creates an intrinsic defect or one of the two pairs above.

For a current physical event, a well-certified unused binding handle or the
unique certified opening is a legal counted class. If an earlier body already
addresses that event, a distinct new one creates the repeated-event pair. If a
binding reuses a noninitial prepared handle, an earlier registered binding using
that handle supplies the other pair. Boundedness, canonical format, ownership,
type and certificate failures are singleton witnesses.

For an old actual phase, phase completion supplies the remaining classification.
If the owner survived, its owned event completed successfully. A successful
binding or opening required its corresponding authenticated packet, which is
already registered. A new distinct body for that event therefore supplies a
repeated-event pair. If no such successful packet exists, the event completed by
exclusion and the owner is permanently excluded. Commitment rollback occurs
only after the entire commitment phase is finished; it does not allow an alive
owner's incomplete event to vanish. A hypothetical, never-installed old phase
fails authorization and belongs to case 3.

This argument must use the concrete phase-completion invariant, not only an
informal appeal to a timeout. Its source ingredients are
[PhaseCompletion](../Vegas/Pending/PhaseCompletion.lean),
[PhaseCompletionStampHistory](../Vegas/Pending/PhaseCompletionStampHistory.lean),
[PhaseExclusionOrigin](../Vegas/Pending/PhaseExclusionOrigin.lean), and
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean).
In particular,
`Vegas.EventGraphRuntime.phase_completed_owned_message` supplies an actual
authenticated submission for a completed installed-phase event of an active
owner. Apply it at the phase's completion boundary and retain the resulting
registered packet through later transitions.

The classification is at retained histories, where there are no earlier audit
violations. At a retained site of an active owner, case 2 is impossible, so every
extra action has a persistent witness. It is not a claim that every arbitrary
later packet has a useful independent new penalty. One permanent first witness
is sufficient at an active first departure.

## One extension handles old signatures and audited actions

Let R be the original-program current-phase counted game after the controlled observable
replay extension for the fixed public calendar. Its prescribed replay probabilities
vanish in the common consistency sequence, so its equilibrium has the selected
original execution and outcome law. Let G allow every bounded authenticated
session action, including retained historical authorizations and all audited
defects. Supply the ActionRestriction embedding of R histories, information,
dependent menus and retained transition kernels into G. Append the same forced
frozen audit tail to both games, as specified below. Every retained R history is
audit clean, so its source payoff matches the actual target net payoff.

Apply the single theorem
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
from [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean).
At a retained information site I of player i, set its enforced predicate to
"i is not publicly excluded at I". Exclusion is observable, so this predicate
is constant on I's hidden histories.

For an active owner, each extra action has the persistent witness just proved.
The final audit collects it with probability one under every continuation.
The funded comparison is U_i-D_i<=L_i, with any clean retained continuation as
the source comparator.

For an already excluded owner, no collection bound is required. Permanent
exclusion, completion and the payoff definition give base payoff F_i under
every full-raw continuation, including after a late disclosure. A Boolean
nonnegative charge and nonnegative deposit imply, pointwise,

    target net payoff = F_i-D_i*charge <= F_i.

Every retained SOURCE continuation from that site has payoff exactly F_i and
zero charge. Therefore, for every source profile, every extending target profile,
every extra action and every belief over the retained information set,

    E[target net payoff after the action] <= F_i
      = E[source continuation payoff].

This is exactly the theorem's direct-comparison premise. It does not assert that
an arbitrary raw continuation remains uncharged. A historical message remains a
real packet and can change survivors' information; the theorem supplies their
joint consistent completion. No source-archive decoder is needed in those new
histories.

A two-step proof, first adding audit-free excluded-owner messages and then other
audited actions, is also possible. It is unnecessary here. The essential condition
is the clean SOURCE comparator, not a requirement to postpone the existence of
audit penalties until after every old-message capability has been added. Starting
from an already charged source continuation would require its actual net payoff
in the comparison; replacing it by F_i would be invalid.

All transmissions, including replays and first old admissions, consume a scheduled
callback slot. Therefore allowing retained signatures and visible retransmission
does not invalidate the occurrence bound. The controlled replay proof and the
action-restriction interface are actual backend requirements, not consequences
of a ledger's eventual application-level idempotence.

## Explicit lifecycle, queue bounds and publication

Let N be the original program's event count and m the number of registered
players. No source instructions are inserted. Choose owned deadlines satisfying
the existing strict margin 1+1+2<deadline; five cycles is one uniform choice.
With maximum deadline Dmax, use the existing completion and resource definitions:

    W = (N+m)(N+1)+N,
    C = (W+1)(Dmax+2),
    B = Cm,
    w = B+m+N+2,
    H = Cw.

The candidate reserve is at least H. Each of the C gameplay cycles has at most
m owner callbacks, so at most

    B = C m

transport occurrences can be admitted during gameplay, hence at most B distinct
entries. This bound includes every malformed, replayed, conflicting, stale and
old-authorized action. It is independent of
prescribed behavior. Finite prepared-handle and body bounds are chosen before
the selected source equilibrium. Processing and callback reservations are
separate, so choosing the large batch capacity B creates no additional callbacks
or circular traffic bound.

### Publication before another semantic choice

The existing reserved implementation has B processing slots in an enabled
processing prefix, with no admission interleaved inside that prefix. Its FIFO
rule removes the pending head and appends the full occurrence to the ledger even
if the application rejects its entry. It applies each entry at most once, in
first-admission order. No player acts inside the batch. Therefore a full prefix
empties any pending list of length at most B. The primary public calendar has a
processing batch every cycle.

Fix any retained binding callback in cycle c. The prefix has already recorded
every occurrence admitted in earlier cycles. Throughout the subsequent owner
callback block, the installed phase is constant: a response only registers its
private preparation and appends its envelope, while reception only extends
private leaked-message memory. Neither executes a game call or advances a phase.
The exact current-runtime facts are
`Vegas.EventGraphRuntime.PhaseCount.submit_publicView` in
[PhaseCountProjection](../Vegas/Pending/PhaseCountProjection.lean),
`Interaction.ReactiveApplication.Execution.environmentStep` in
[ReactiveApplication](../Interaction/ReactiveApplication.lean), and
`Interaction.MessageNetwork.learn` in
[MessageNetwork](../Interaction/MessageNetwork.lean).

Because this block's installed phase is a commitment phase, every retained new
first entry emitted earlier in the same block is an opaque binding, never an
opening. A replayed opening was first admitted in an earlier cycle and is already
in the ledger. Initial traffic is empty. Therefore, at this callback,

    all submitted opening proposals = ledger opening proposals.

The archive is a set, so replay multiplicity changes no proposal. The equality
holds at every retained counted history, including failed guards, waits, retries
and one-step alternatives. Phase changes during processing occur before the
callback block; sample and expiry changes occur after it. Neither is a missing
case. Historical first messages outside the retained menu are handled by the raw
extension, not by asserting this decoder after such a departure.

This proves publication without any source transformation. The primary theorem
needs no additional point-mass distribution constructor or context-weakening
operation. Original typed source states and their intended SE are unchanged.

For a different service that may skip processing cycles, this phase-constant
argument alone does not clear earlier-cycle openings. The separate padding
construction inserts p+2 constant samples and gives a clearing epoch before
the next binding callback under a processing-gap bound p. Its language and
expanded-resource hypotheses belong to that alternative construction.

With smaller blocks of b>0 envelopes, a drain after admission closes requires
ceil(B/b) enabled epochs. If consecutive enabled epochs are at most p cycles
apart, a conservative cleanup interval is p*ceil(B/b)+1 cycles. During ordinary
gameplay, continuing arrivals require an additional backlog argument. The
existing p+2 padding proof must not simply substitute b for B and keep the same
delay.

### The final drain

After the last gameplay callback, permanently close session admission. This
cutoff concerns the whole registered communication interface, not just acceptance
of game actions. No further envelope is shown through that interface during the
drain. End the finite game only after this cleanup and settlement.

At this cutoff also freeze the gameplay state s_close and its base payout. The
tail's inbox handler only records and audits envelopes; it does not execute their
game actions. This makes the tail an extension of the existing bounded game's
terminal payoff even when a malformed/raw history has pending messages. On
retained counted histories the existing completion bound already completes the
game. Merely allowing a finite horizon to expire while continuing to execute
pending game calls afterward would not justify an unchanged-payoff claim.

Retain the pending queue. Schedule one processing prefix of B slots after the
cutoff, or wait for the next enabled prefix within its explicitly extended
processing-gap bound. It has no owner callbacks. It empties the queue, so the
ledger contains every admitted occurrence and therefore every distinct entry.
The certificate and sample records
needed to replay the public state machine are retained as well.

Let T_close be the admission cutoff, Delta the final drain bound, and A the
bounded number of steps needed to check all B bodies and their certificates.
Reserve the audit computation or transaction with its own inclusion bound a.
Choose

    T_publish = T_close + Delta,
    T_audit   = T_publish + A + a,
    T_settle >= T_audit.

The processing service must cover this tail in addition to gameplay. This does
not follow from a gap bound whose quantifier stops at the original C cycles.
The frozen tail changes neither source decisions nor payoff-relevant application
state; it only completes publication and computes penalties. All records and fees for
the tail are included in the fixed resource reservation.

If the ledger executes the bounded audit automatically as part of settlement,
take a=0. If a transaction is required, it is submitted by the reserved service
and its funded inclusion is part of the service schedule. Replacing this with a
voluntary player report would require a separate incentive argument.

Append the same forced frozen tail to the retained game before using the generic
action-restriction theorem. Each old terminal history has a unique tail expansion,
no new player decision, and the same base payoff; on retained clean histories the
audit verdict is zero. Lifting the consistency sequence through this deterministic
expansion preserves its decision beliefs and gains. The restriction then compares
equal-horizon games with aligned terminal histories, rather than mapping an old
terminal history to a still-running target prefix. The final readout erases the
tail. No source padding is erased in the primary construction because none was
inserted.

## Derived audit observation and delivery

At T_publish the complete authenticated traffic log is public. Define the audit
evidence record to be that exact log together with its fixed certificate data.
The deterministic scanner derives every singleton and pair witness. Its
observation kernel is therefore a point mass on the full genuine evidence record.
At T_audit its reports/verdict are in the finalized ledger with probability one.

For every actual traffic T and every genuine witness w contained in T,

    Pr[w is observed at T_publish | T] = 1,
    Pr[w is included by T_audit | the observed evidence record] = 1.

These equalities follow from the final-drain lemma, deterministic verification
and the reserved audit step. They hold for every traffic and every continuation;
there is no independence assumption and no division by an information-set reach
probability. Thus the two coverage rates are alpha_i=beta_i=1. In the existing
report-service interface this is a concrete realization of complete authentic
observation and timely delivery, rather than an appeal to an omniscient observer.

The relevant source interfaces are
[ChallengeWindow](../Interaction/ChallengeWindow.lean),
[CompleteEvidenceService](../Interaction/CompleteEvidenceService.lean), and
[PhaseCountCollection](../Vegas/Pending/PhaseCountCollection.lean). The new
pair/certificate verdict and enlarged retained domain require their corresponding
evidence adapter; the unchanged phase-specific raw theorem does not itself
instantiate that larger packet grammar.

## Optional receipt-dated late-opening charges

The backend may additionally charge provably late first admissions. This is not
needed for the preceding active-owner evidence argument, but it is compatible
with the same single localized-enforcement application.

Store x(e), the actual public completion/expiry time of each physical owned
event, when that event first completes. Retain the entry across rollback. Store
r(m), the earliest actual ledger inclusion time of each immutable protocol entry.
Replays do not replace r(m). These are contract records derived from the actual
public execution, not sender-supplied signing times. The fixed-calendar public
trace reconstruction also reconstructs this completion-time table.

Let d_inc be the maximum actual registration-to-inclusion delay, in the same
clock units, including the final tail. For the full-flush reserved service it is
the processing-gap bound p; for the primary every-cycle calendar it is one cycle.
For a registered entry sent at s,

    s <= r(m) <= s+d_inc.

Define Late(m) for an opening of a genuinely installed, completed event by

    Late(m) iff r(m) > x(e)+d_inc.

The final audit may use charge_i = 1[Bad_i or some own Late entry]. A retained
current opening is sent while its event is still open, hence s<=x(e). Therefore

    r(m) <= s+d_inc <= x(e)+d_inc,

so Late is false on every retained history, including in-window waiting and
replays of an entry already included. This proves retained payoff matching for
the stronger verdict. It does not charge based on whether a sender followed an
immediate-send prescription.

For the separately padded general-gap construction, if a reveal block closes
at c and a later binding callback is at
b>=c+d_inc+2, then x(e)<=c for each event of that block. A previously unrecorded
opening entry still pending at b has future earliest record r(m)>=b, and hence
r(m)>x(e)+d_inc. It will be charged. A replay can still be pending with an earlier
record r(m)<=x(e)+d_inc; its opening value is already public, and its receipt
signals are covered by the replay proof. Thus "every pending occurrence is late"
would be false.

The primary every-cycle service does not need, or generally satisfy, that
additional delay. A reveal may close in the processing prefix of cycle c, and
an excluded owner may first admit its old opening during that cycle's binding
callback block. Its next-cycle record can be r=c+1=x(e)+d_inc, so Late is false
while another same-cycle binding callback can receive it privately. This does
not affect the retained archive theorem: the historical first admission is
outside R, and the excluded-owner direct comparison handles it without any
charge-probability premise.

An excluded owner might send after x(e) but still obtain a record within the
slack interval. Its Late status can depend on future processing, and there need
not be a positive charge probability uniform over those actions. No such bound
is used: its arbitrary target net payoff is still at most F_i. For active extra
actions, the independent intrinsic/pair witness gives certain charge regardless
of Late. A verdict need not be known when signed if these actual continuation
comparisons hold.

Never-installed reveal phases remain a separate case. There is no legitimate
x(e) for such a reveal. Dating it instead from a retired commitment phase does
not make every such opening late: a record within that retirement time plus
d_inc escapes the threshold. The actual-phase/accepted-handle authorization
requirement therefore remains essential. Receipt dating cannot replace it.

The audit uses actual ledger inclusion, not a fabricated convention that an
unrecorded pending packet counts as recorded at settlement. The final drain
guarantees that r(m) exists before the audit, and its service bound must really
cover that final interval. Without that bound, the displayed retained-clean
inequality has not been established.

## Escrow, deterrence and exact settlement

Let L_i <= u_i(s) <= U_i on every protocol state, including incomplete readout
defaults and excluded-owner payoffs. Lock a fixed nonnegative audit escrow

    D_i >= U_i-L_i

before gameplay. It cannot be withdrawn, reused for fees or consumed by another
claim before the final audit. A single Boolean charge is assessed per owner:

    net_i(s,T) = u_i(s) - D_i * charge_i(T),

where charge_i is the basic Boolean Bad_i verdict or its optional receipt-dated
extension. Both are zero on all retained R histories and nonnegative everywhere.

At an embedded audit-clean history of an ACTIVE owner, any first extra action
creates a persistent witness. Final collection is certain under every continuation. Hence its
conditional payoff, for any belief supported on that information set, is at most

    U_i-D_i <= L_i.

Every retained continuation has base payoff at least L_i and no audit charge.
This supplies the finite restriction-extension comparator uniformly over
off-path beliefs and later policies. No punitive coordination equilibrium or
voluntary reporting threat is required.

The generic localized-enforcement/restriction result then supplies one consistent
raw SE extending the selected R SE, using the direct F_i comparison at excluded
sites. The terminal history law is the retained
one. Along this law charge_i is zero for every owner. Escrows are returned in full,
and the realized net-payoff vector equals the original base-payoff vector, jointly
with the original initial inputs and unchanged typed terminal state. The final
readout erases only auxiliary replay/transport records and the forced audit tail.

Funding is explicit. The session sponsor reserves the full admission, storage,
inclusion, verification and settlement cost before play. These costs are not
charged according to player actions on the preserved path. The game payout pool
must separately fund its designated base transfers; audit escrow is not a proof
that arbitrary positive base payouts can be paid.

In the pure monetary specialization, u_i itself is the contract transfer. A
sponsor can reserve sum_i max(0,U_i) in addition to service costs. Each player
separately reserves K_i >= max(0,-L_i) against negative base transfers, while its
D_i audit escrow remains segregated. At settlement it receives

    D_i + K_i + u_i(s_close) - D_i * charge_i(T).

This is nonnegative even when charged, because K_i+u_i(s_close)>=0. Subtracting
its original D_i+K_i payment gives exactly the claimed net payoff. The sponsor's
positive-transfer reserve covers simultaneous positive base payouts; negative
base payments and penalties can remain in the contract's residual balance.

For general quasilinear utility write u_i(theta,z)=v_i(theta,z)+t_i(z), where the
contract can compute transfer t_i and audit deductions change utility by their
monetary amount. Use separate cash bounds l_i^cash <= t_i <= u_i^cash. Reserve
K_i >= max(0,-l_i^cash) and sponsor sum_i max(0,u_i^cash). The actual receipt is
D_i+K_i+t_i-D_i*charge; its net monetary transfer is t_i-D_i*charge, and adding
the unchanged private valuation gives u_i-D_i*charge. Deposit size D_i still uses
the full utility spread U_i-L_i. Utility bounds alone do not bound cash liability:
a large positive valuation can mask a large negative transfer. The source's
fixed exclusion-utility premise must also hold for v_i+t_i; it is not implied
merely by fixing an excluded player's monetary transfer.

Full escrow refund gives zero *net monetary* audit cost on the preserved path.
Liquidity costs, interest, time preferences, transaction utility and congestion
externalities are excluded unless already included in the source payoff model.
If they matter, adding a delay or locking a deposit can change equilibrium, and
the exact unchanged-payoff theorem does not apply unchanged.

## A finite end-to-end composition statement

Fix the source setup and its original-program compiler, finite session grammar, genuine
phase/accepted-binding certificate implementation, replay rule, registered
transport, deterministic public calendar and extended tail schedule, payoff function and funding
before selecting the source SE. Assume the same well-formedness, finite-value,
timeliness and exogenous-service hypotheses used by the counted construction;
the fixed public calendar is a concrete instance of that service family.
Assume the closed-opening/phase-completion classification and controlled retained
history embeddings described above.

Then every intended source SE has a raw registered-session SE with exactly its
initialized original terminal/public/net-payoff joint law. The proof composes:

1. direct full-batch publication, the common-sequence private counted proof, and
   the controlled observable-replay extension for the fixed calendar;
2. the persistent-witness classification for active first extra actions and the
   direct net-payoff comparison for already excluded actors;
3. the common forced frozen-tail expansion and retained history embedding;
4. the finite queue drain and deterministic audit, deriving unit collection;
5. one localized-enforcement extension and deterministic settlement.

The proof preserves existence of the selected equilibrium and its entire stated
joint law. It does not assert that every target equilibrium projects to a source
equilibrium. The missing formal work consists of the explicit compiler/certificate,
history/action embeddings and finite audit adapters, not an unproved behavioral
assumption that players voluntarily report each other.

## Why arbitrary unregistered private communication cannot be covered

An audit cannot distinguish two executions that give it exactly the same public
transcript and evidence. In particular, if a private message is never registered
or reported, no sound ledger-only procedure can charge its sender merely because
that message was privately received. Applying a charge in only one such execution
would require evidence the procedure does not have.

There is also a direct SE obstruction. Nature chooses theta in {0,1}, with
Pr[theta=0]=2/3. Player A knows theta and holds an unforgeable, transferable proof
of it. Player B initially sees neither. In the source, B chooses a guess x and
receives 1[x=theta]. A receives 1 exactly when theta=1 and x=1, and 0 otherwise.
A has no source action before B's guess. The unique source choice is x=0, so A's
source payoff is always zero. The proof may be a certified opening of A's
initial commitment whose intended reveal is later.

Now permit A, before B's guess, to send its proof privately without registration.
For fixed subsequent actions and chance outcomes, inserting this private send
leaves the audit record unchanged. Every resulting public record also occurs
in a source-legal execution with the same theta and B's same chosen guess.
An audit that charges nobody on all retained legal histories therefore cannot
charge A in the private-send execution. Charging merely because B guessed 1
would punish a legal retained action without evidence of A's disclosure.
At a history where B receives a valid proof of theta=1, every consistent belief
assigns theta=1 probability one: no theta=0 history can produce that proof.
Sequential rationality forces x=1. If a target SE preserved the source joint law,
A at theta=1 would receive zero but could disclose the proof and obtain one.
That contradicts sequential rationality. No target SE preserves the source law.

This counterexample assumes there is no later guaranteed reporting channel for
that private proof. If such a channel or a funded reporting mechanism is added,
its evidence and incentives must be analyzed. It does not refute the registered
broadcast construction, whose defining property is that every modeled message
has entered persistent, eventually public storage before anyone receives it.
