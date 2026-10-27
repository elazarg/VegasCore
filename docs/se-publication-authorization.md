# Historical authorization and delayed disclosure

This document specifies the authorization adapter between the current phase
runtime and a finite model permitting retained signatures. The mathematical
construction preserves the intended game's equilibrium law; it does not assume
that a ledger can delete a participant's private copy of an old packet.
The primary service uses the original, unmodified phase compiler and a full
processing batch before every cycle's callback block. It needs no source
padding. The pointwise publication argument below feeds
[the native adapter](se-publication-native-adapter.md) and the
[end-to-end construction](se-publication-end-to-end.md).

The exact current-model result, the proposed retained-authorization model, and
its equilibrium extension are separate statements. Source inspections below
identify existing declarations. New adapter equations are mathematical proofs
to formalize, not additional checked Lean declarations.

## What a current response actually emits

The time-independent permission predicate is evaluated on the packet actually
materialized by the phase emitter. A response cannot supply an arbitrary old
token or an already signed envelope.

In `Vegas.EventGraphRuntime.PhaseCount.localEnvelope`, the submission is given
the current attempt and the current native readiness token, and then passes
through `Vegas.EventGraphRuntime.PhaseCount.maskPacket`. These definitions are
in [PhaseCountProjection](../Vegas/Pending/PhaseCountProjection.lean). The mask is

\[
 \operatorname{mask}(V,p)=
 \begin{cases}
 p[\mathrm{token}:=\mathrm{none}],&
   \operatorname{owner}(p)\in V.\mathrm{excluded}
   \text{ or }p\text{ is outside the installed phase},\\
 p,&\text{otherwise}.
 \end{cases}
\]

The actual emitter has the same two tests:
`Vegas.EventGraphRuntime.RecoveryState.emit` in
[ExclusionApplication](../Vegas/Pending/ExclusionApplication.lean) masks excluded
owners, and `Vegas.EventGraphRuntime.PhaseRuntimeState.emit` in
[PhaseApplication](../Vegas/Pending/PhaseApplication.lean) masks calls outside
the installed phase. The declaration
`Vegas.EventGraphRuntime.PhaseCount.emit_after_submit` identifies their result
with the local reconstruction. Private preparation does not change these
public tests.

For an excluded owner, every opening of its own event therefore has no token
in the reconstructed envelope. Its
`Vegas.EventGraphRuntime.WitnessedPacket.tokenValid` is false, so the first conjunct
of `Vegas.EventGraphRuntime.PhaseCount.Permits` fails. Firstness, possession of
the correct opening certificate, and the continued existence of a lower-level
readiness token do not change that conclusion.

There is also a stronger existing statement:
`Vegas.EventGraphRuntime.PhaseCount.onePacket_request_of_nonsilent` in
[PhaseBindingIdleMenu](../Vegas/Pending/PhaseBindingIdleMenu.lean) proves that
every nonsilent counted response on an initialized history has a real current
`Vegas.EventGraphRuntime.PhaseRuntimeState.SeedRequest`. Such a request includes
membership in the installed phase, readiness, ownership and nonexclusion.
Consequently
`Vegas.EventGraphRuntime.PhaseCount.onePacketActions_eq_singleton_of_no_request`
makes every excluded owner's counted callback silent. Continued exogenous
activation does not enlarge that menu.

This reconciles the two apparent claims:

* A packet already emitted with a valid token retains its time-independent
  count verdict when it is included late or its attempt is retired.
* A newly emitted obsolete or excluded-owner call has its token removed before
  that verdict is evaluated.

The former is a statement about immutable signed traffic. The latter is a
statement about the current action-to-packet interface. Neither implies that
a real signer forgets an earlier authorization. The enlarged model below adds
that capability explicitly.

## A finite retained-authorization model

Fix the original source program and its compiled phase graph, finite horizon,
bounded packet alphabet, candidate
reserve, scheduler law, actual private reception rule and initial joint law.
No object in this paragraph varies with the consistency index. Use ideal
authentication, as the current symbolic model does; this is not a computational
claim about a concrete signature or commitment scheme.

An owned physical event has address \(e=(\mathrm{attempt},\mathrm{event})\).
The public ledger state can issue a historical authorization \(A_e\) only when
all of the following facts hold in that actual state:

1. The named phase and attempt are installed.
2. The named event belongs to that phase and is ready.
3. Its owner is not excluded.
4. For an opening, the authorization identifies the accepted binding handle
   that this resolve event is to open.

The authorization is permanent evidence that this state occurred. It is not
a promise that the state is still current. A sender may retain it and construct
or broadcast an authorized body later. Its validity never depends on a claimed
broadcast time, receipt time, or the sender's assertion that a deadline was met.

Authorization must certify actual phase installation, not just a predictable
phase identifier or the completion of some native prerequisites. In the current
model a readiness token is a symbolic capability whose creation is controlled
by the emitter; `Vegas.EventGraphRuntime.ReadinessToken` itself contains only
the event. See [EventApplication](../Vegas/Pending/EventApplication.lean).
Making the same event identifier freely writable would not implement that
capability. A concrete implementation needs a genuine finalized ledger witness
or an equivalent ideal authentication primitive.

Use canonical authorized bodies. Each body fixes owner, physical event, kind,
handle, typed opening value when applicable, and exact opening evidence.
Authentication and authorization cover the whole body. There is no unvalidated
memo, nonce, padding field, alternate proof encoding, or caller-supplied phase
claim inside a free body. A backend with such fields must either normalize them
before every modeled observation or include their alternatives in its action
and evidence analysis.

The symbolic authorization identity may remain the existing event/attempt
identity. A concrete certificate serialization is an extra wire component.
To reuse the existing counted construction, show that it adds no uncontrolled
private information: for example, its canonical representation is read from
the public issuance record identified by the packet. A proof that verifies
correctly is not automatically a proof of that observation property.

The wallet of historical authorizations is a deterministic function of the
player's retained public ledger history. Signing need not be a separate hidden
strategic move: the action menu directly permits transmission of any bounded
body constructible from that wallet and the player's actual opening capability.
This gives a finite extensive game with perfect recall. It does not assume
that a signer can fabricate a future authorization or a foreign opening proof.

Two distinctions are essential:

* An authorized packet can be rejected by current application semantics and
  still reveal its plaintext. Historical authorization is about admissibility
  of its creation, not current semantic acceptance.
* An authenticated packet without the required historical authorization has
  an intrinsic defect. Showing a later ledger state does not repair the exact
  signed body if that body fixed its authorization evidence. Collection of the
  defective body is a separate audit obligation.

## Full-batch publication without changing the source

The primary calendar processes the entire pending queue at the start of every
cycle, then offers one callback to each owner in a fixed order, then executes
the existing sample, expiry and clock commands. The processing prefix has
enough capacity for every admitted occurrence. There is no inclusion, sample
or expiry between two callbacks of the same cycle.

The installed phase is constant throughout that callback block.
`Vegas.EventGraphRuntime.PhaseRuntimeState.submit` in
[PhaseApplication](../Vegas/Pending/PhaseApplication.lean) updates private
candidate state without invoking normalization. More strongly,
`Vegas.EventGraphRuntime.PhaseCount.submit_publicView` in
[PhaseCountProjection](../Vegas/Pending/PhaseCountProjection.lean) preserves the
whole public phase, attempt, readiness and exclusion projection for every
submission. `Interaction.ReactiveApplication.Execution.respond` in
[ReactiveApplication](../Interaction/ReactiveApplication.lean) performs only
submission, packet emission, network append and own-recall append. Its activation
step preserves the application, updating the network's private learned list and
ordinary environment-recall bookkeeping.

Fix any initialized counted history at a binding callback in cycle c. Every
opening submitted in an earlier cycle was already pending before cycle c's
processing prefix, or was recorded even earlier. The full prefix records all
such envelopes, including rejected and stale ones. A new counted opening
cannot have been submitted earlier in cycle c: the same binding phase was
installed at every earlier callback, and every nonsilent counted response must
name a current owned request. A binding-phase request emits an opaque binding,
not an opening. The initial network has no submitted openings.

Therefore, pointwise at every counted binding information set,

\[
 \{\text{typed proposals in all submitted openings}\}
   =\{\text{typed proposals in ledgered openings}\}.
\]

Retries do not change this argument: they occur during processing or the
post-callback application commands, never midway through the callback block.
An allowed replay repeats an existing entry. If it carries an opening, the
first admission of that entry was in an earlier cycle and is already ledgered;
repetition adds no new proposal to the set. Private reception can remain
arbitrary. Historical first openings by excluded owners belong to the later
raw extension, where this decoder identity is not asserted.

For an original source with n events, use \(N=n\) in the existing runtime
resource formulas. No fresh source cell, point-mass distribution constructor,
context embedding or source-stuttering theorem is needed. The existing complete
reference construction is instantiated directly on the unmodified source and
this deterministic reserved tape.

For a different service whose processing may skip cycles, the separately
derived [publication-padding route](se-publication-padding-mathematics.md)
remains a valid sufficient construction under its own language and resource
hypotheses. Those additional hypotheses are not part of this primary instance.

## Closed-opening classification

Consider a clean history and a genuinely authorized opening for event \(e\).
Suppose its reveal phase has closed. Then one of these cases holds.

**Successful publication.** The resolve event completed through inclusion of
its correct opening. That envelope, including the same handle and value, is
already in the ledger. An immutable accepted handle has one usable typed value,
so a later valid opening cannot introduce another value for that handle.

**Failed publication.** The resolve event completed by an expiry or a failed
publication that permanently excludes its owner. Every future base payoff of
that owner is its exclusion payoff \(F_i\), under every subsequent profile and
recovery. Automatic completion of an already excluded owner's events falls
in this case as well. The owning transition and payoff results are in
[PhaseExclusionOrigin](../Vegas/Pending/PhaseExclusionOrigin.lean) and
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean).

These cases exhaust a finished resolve event. A commitment rollback does not
reopen a reveal phase already entered: rollback is confined to the current
commitment phase, and phase advancement never returns to an earlier reveal
descriptor. The opening authorization fixes the actual accepted handle, so it
cannot be reused to certify a different binding generation.

This proves a useful first-packet corollary. If a previously authorized old
opening has not yet had its first successful protocol transmission and its
resolve phase is closed, then its owner is excluded. In the successful case,
the opening that caused completion already used that event's packet allowance.
The corollary does not say that all obsolete packets have become public. It
identifies the actor's payoff at the sites where a new obsolete disclosure can
still be a free first packet.

### The same first-packet classification for old bindings

An installed commitment phase closes or rolls back only when every event in
it has finished. If an event's owner remains unexcluded, its completion has an
actual authenticated packet for that owner and physical event. The existing
live invariant is
`Vegas.EventGraphRuntime.phase_completed_owned_message` in
[PhaseCompletionStampHistory](../Vegas/Pending/PhaseCompletionStampHistory.lean).
At the final completion step the packet is either already recorded by that
invariant or is the packet causing the step. Expiry or automatic completion
without such a packet excludes its owner. Retained inputs survive the ensuing
normalization and rollback.

Consequently a still-active survivor cannot broadcast the first packet for an
old closed binding event: it already broadcast the packet that completed that
event. It can broadcast a second, previously withheld *body*, but this is not
the first packet of the *physical event*. If the bodies differ they provide
duplicate evidence; if identical the replay rule applies. A genuinely unused
old event allowance belongs to an already excluded owner.

Thus the payoff-fixed extension below can include historical first packets of
either owned kind, not just openings. An obsolete commitment's registration
must still preserve fixed exclusion payoff; it cannot revive an owner or reset
the exclusion flag. Its possible effect on survivors is unrestricted.

### Abandoned commitments and hypothetical premature openings

Suppose a player survives a rollback of a commitment attempt. Its submitted
commitment may have a correct private value, but that failed attempt never
installed the corresponding reveal phase. It therefore never issued the
opening authorization just specified. A self-signed statement naming the
predictable future resolve event has no such provenance.

There is no escape through another attempt. A surviving later reveal
authorization identifies that attempt's accepted handle. Count-clean handle
freshness and the latest surviving binding rule prevent the old abandoned
handle from being substituted. Nor can an earlier successful reveal
authorization be reused: its physical event and accepted handle are fixed.

Hence an active survivor's opening of an abandoned commitment is outside the
free retained-authorization extension. For signed protocol traffic, its absent
or mismatching authorization is a permanent potential audit witness. This is
not a statement that an unsigned preimage, an independently verifiable proof,
or an unauthenticated private message is automatically attributable or
collectable. Such communication must appear explicitly in the backend model.

The distinction matters for incentives. Let a player privately know a fair bit
\(\theta\), and let another player later choose a guess \(g\); both receive
\(\mathbf1_{g=\theta}\). With no informative message before the guess, choosing
\(g=0\) is an SE. If the informed player can freely disclose an authentic proof
of \(\theta=1\) before that choice, the receiver must guess 1 after the proof,
and type 1 gains by disclosing. No equilibrium preserving that original
constant-guess outcome survives this extra capability. A hidden commitment
with a freely transferable authentic opening implements precisely this
information change. The authorization/evidence boundary cannot be omitted
merely because the abandoned commitment no longer changes contract storage.

### A concrete failure of the naive mask-free verdict

Keeping the existing permission predicate while making both the signed serial
and physical attempt freely sender-chosen is insufficient. Here is an exact
packet-level example. Write \(R\) for the source resolve event and use its
proper reveal-phase address in each attempt namespace.

1. At generation \(g\), player B commits fresh handle \(h\) with a privately
   chosen valid typed value, at signed serial 2. Another owner misses; the
   commitment phase rolls back and B survives.
2. B commits a fresh handle \(h'\) at generation \(g+1\), signed serial 6.
   That attempt succeeds and the real reveal phase issues the attempt-free
   token naming \(R\).
3. B opens \(h'\) properly in that real reveal phase, signed serial 7.
   The phase closes and a later binding block begins. B remains active; the
   example also survives any intervening finite publication-padding block.
4. During a later binding block, B broadcasts an old-value opening for \(h\),
   signed serial 5, with reveal namespace \((R\text{-phase},g)\), and attaches
   the genuine token naming \(R\).

In the naive extension, the last packet passes the existing
`Vegas.EventGraphRuntime.PhaseCount.Permits` checks:

* Its `Vegas.EventGraphRuntime.WitnessedPacket.tokenValid` checks the event
  named by the token, not the attempt. The stricter
  `Vegas.EventGraphRuntime.CommitAttemptPacket.tokenValid` is an application
  admission test, not this count conjunct.
* There is no earlier packet for the fake old reveal namespace, so physical
  event firstness holds.
* `Vegas.EventGraphRuntime.PhaseCount.Earlier` sees only lower signed serials.
  For serial 5 it sees binding 2 but not retry binding 6. Thus the old handle
  is the latest eligible binding in that restricted set.
* B retains the candidate meaning across rollback and can produce the genuine
  opening certificate for \(h\). The lower-serial signed binding supplies the
  corresponding binding check.

The proper opening at serial 7 also remains permitted: its namespace differs,
its latest binding is serial 6, and the new serial-5 packet is an opening rather
than a competing binding. The application's later rejection of the fake old
namespace does not undo its private disclosure.

The general append-later immutability theorem is not applicable to this
example: appending serial 5 after serial 7 violates its increasing-serial
premise. The two concrete verdicts remain true by the checks just listed.
The example is not a current-model history because its emitter fixes the
actual serial and current attempt. It refutes the naive backend adapter and
its global archive decoder, not every possible preservation construction.

Actual installed-phase/accepted-handle authorization rules it out immediately.
There is no certificate for the never-installed generation-\(g\) reveal, and
the generation-\(g+1\) certificate fixes \(h'\). Using authentic outer entry
serials also prevents omitting binding 6 by choosing an old inner nonce.

## Extending the counted game after exclusion

Let \(R\) be the original compiled counted game under the primary calendar
and actual private reception rule.
Let \(E\) additionally permit historical first owned packets whose authorization is
valid, at a site where their owner is publicly and permanently excluded. This
includes an expired request while other owners keep its containing phase open;
closure of the whole phase is not required. Keep these extra packets audit-free.
They may enter pending traffic, leak privately, consume bounded queue space,
or change survivors' behavior. The application still rejects their obsolete
semantic effect. All counts and the terminal horizon cover these extra actions.

The limit strategy in the extension will choose none of them. Its fully mixed
consistency witness need not do so. In particular, the publication archive
identity is not asserted at every \(E\)-history. An old late opening can create
genuinely new survivor information, and those sites receive a consistent
rational completion.

### Public authorization readback for the primary service

For the concrete backend, choose one fixed owner order, activate every owner
exactly once per cycle, and enable full FIFO processing in every cycle. Keep
the existing order: processing, owner callbacks, one source-sample command,
expiry commands and clock advance. This is a deterministic reserved tape;
private pending reception remains arbitrary. Its activation and processing gap
bounds are one. Use a processing capacity covering every admitted gameplay
packet using the existing resource calculation with the original event count
\(N=n\). The sample slot here executes an existing source chance instruction
when one is ready; it introduces no new source instruction.

This choice gives an explicit producer for the historical-certificate wallet.
In fact, a player's original private own recall suffices; complete pending
reception is not needed for the following public-history reconstruction.

Number cycles from zero, and fix owner i. Let \(L_c\) be the retained ledger at
i's callback in cycle c. The first callback sees the empty ledger. For c>0,
the suffix

\[
                         B_{c-1}=L_c\setminus L_{c-1}
\]

means list suffix, not set subtraction. It is exactly the sequence of envelopes
admitted during cycle c−1. The processing prefix of c−1 emptied all older
traffic before that cycle's callbacks; no processing occurred afterward until
the prefix of c; and the latter clears the entire resulting queue. FIFO order
preserves the fixed owner-slot order. With at most one packet per owner per
cycle, the batch also identifies each nonsilent owner slot. A missing owner's
packet means silence. This argument uses durable inclusion of rejected packets.

Packets of owners earlier than i in the current cycle may already be pending,
but have not been included. Their private registration/freeze operations do
not change the public application projection. They therefore do not affect
the public authorization trace being reconstructed at i's callback.

The sample slot in cycle c−1 executes at most one public source sample. Its
event identity and realized output are recoverable at callback c from the
public source-cell observations and completed-event information. A sample
field is written once. Later rollback occurs only inside a commitment block
and restores the entry after all preceding public events, so it cannot erase
an earlier sample field. If no new sample field was completed, the sample
command stuttered. Current and earlier own views retain this information even
when the player received no private pending messages.

Starting with the public initial source projection, replay the public state
machine by induction on cycles and then on each command within a cycle:

1. Replay the preceding batch in its ledger order. A counted binding publishes
   its event completion and accepted handle independently of its hidden
   preparation. In particular, an unusable accepted binding does not exclude
   its owner; see `Vegas.EventGraphRuntime.RecoveryState.inclusionResult` in
   [ExclusionApplication](../Vegas/Pending/ExclusionApplication.lean).
2. A counted opening's immutable evidence identifies its actual successful
   typed candidate value. Current phase, readiness, exclusion and accepted
   handle determine whether it is obsolete or applicable. Its publication
   guard is a function of the revealed values and public cells: the source
   language checks a guard only after all its reads have been published, and
   guards have no private-input reads. These are the definitions of
   `Vegas.SourceGuardRead` and its revealed-result interpretation in
   [Basic](../Vegas/Source/Basic.lean). Hence its public success/failure and
   any new exclusion are determined by this public replay.
3. Private preparation and passive reception during callbacks have no public
   application effect. Insert the one realized public sample outcome just
   recovered, or the determined sample stutter.
4. Execute expiry commands in their fixed order using the reconstructed
   activation times and public clock. All resulting exclusion, automatic
   completion, phase advancement and commitment rollback are public functions
   of these data. A rollback restores the previously reconstructed public
   entry checkpoint and retains the public exclusion flag and clock.
5. Advance the clock once. The resulting state is the next cycle's public
   pre-processing state.

Run these five steps for cycles j=0,...,c−1, using the empty batch at the start
of cycle zero, batch \(B_{j-1}\) thereafter, and the recovered sample outcome
from cycle j. Then perform only step 1 of cycle c, with batch \(B_{c-1}\).
This is the public state at callback c; the intervening earlier-owner callbacks
have no public application effect. For c=0 no replay is needed.

This induction reconstructs every intermediate public phase installation,
ready-event state, accepted-handle map and exclusion set up to the current
callback. It does not reconstruct hidden candidate values, and does not need
them. Initial public data are taken from the first actual own view; private
initial inputs may have any joint distribution.

Choose one canonical certificate record per physical event: the event/attempt,
the first reconstructed state at which its owner has the real ready request,
the public prerequisite evidence, and the accepted handle for an opening.
The ledger authentication primitive certifies that actual record. There is no
sender-chosen proof variant. Its contents and its availability are functions
of the reconstructed public trace. Thus at every retained counted information
set, adding the canonical certificate archive adds a deterministic observation
already determined by the original private own information.

This proves the observed-information square needed below, rather than
postulating it. The actual richer private game may expose the whole certificate
archive and remember every late packet. At new histories the restriction
extension handles its new information directly. The reconstruction claim is
needed only on retained histories. It is specific to this deterministic
primary service; a more general scheduler needs its own readback producer.

The same producer handles arbitrary reception rules that inspect certificate
bytes. Combine the reconstructed canonical authorization record with each
pending core packet's event, attempt and accepted handle. Complete fine own
recall already reconstructs the ordered pending core list, by
[the native readback](se-publication-native-adapter.md). It therefore determines
the entire enriched pending list. Sample the actual fixed reception kernel on
that list in the causal transport theorem. There is no need to assume that the
reception kernel ignores certificates or factors through their erasure.
Canonical serialization adds no fresh randomness or sender-selected metadata;
the physical core successor and the all-index effective response law are the
same ones already compared in that theorem.

### Structural embedding

Construct
`GameTheory.Protocol.InformationModel.ActionRestriction` from \(R\) to \(E\),
using the structure in
[ActionRestriction](../GameTheory/GameTheory/Protocol/ActionRestriction.lean).
Its fields have the following concrete definitions.

* The history map copies the initial draw, commands, observations and retained
  responses. Enriched packet representations use their fixed canonical
  encoding. There are no extra signing moves or clock steps on these histories.
* The information map copies actual public/private observations and literal own
  recall, and computes the deterministic historical-authorization wallet. Its
  inverse on the image erases only this derived wallet, so it is injective.
* The choice map is the ordinary retained response with the same preparation,
  evidence choice and emitted canonical packet. It is injective.
* Initial history, trace length, terminal status and active player are unchanged.
* The observed-information square commutes because the retained history has no
  extra emission and uses the same reception kernel on the same pending pool.
* The pure-choice transition square commutes because retained responses and
  environment commands have exactly their old effect. The extra wallet update
  is a deterministic public-history read, not a new random input.

The structural claim is about a restriction of one fixed enlarged model. The
preceding readback proves that its canonical certificate wallet is determined
by the original local information for the primary service. The information
embedding therefore does not split an original information set. Extra
noncanonical certificate bytes or a richer unrelated ledger log are not part
of this construction; their observation refinement would require a separate
proof.

### Exact continuation comparator

Fix any source profile \(\sigma\), any target profile \(\tau\) extending it,
an embedded source information site \(I\) of player \(i\), any added action
\(a\), and any belief \(\mu\) on the source histories in \(I\).
The quantification is over all such objects, not only equilibrium profiles.

Public exclusion holds at every hidden history \(h\in I\). Under every target
continuation following \(a\), player \(i\)'s base utility is \(F_i\).
Under every retained source continuation from \(h\), it is also \(F_i\).
Choose the source profile itself as the legal source continuation comparator.
Then

\[
 \mathbb E_{h\sim\mu}\mathbb E[u_i\mid h,a;\tau]
 =F_i
 =\mathbb E_{h\sim\mu}\mathbb E[u_i\mid h;\sigma].
\]

The same proof permits a value fixed by the initial hidden state, provided it
is fixed under every continuation and agrees on the embedded history. The
expectations then both equal \(\mathbb E_\mu F_i(h)\); a globally constant number
is not needed for the abstract comparator.

Instantiate
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`
in [LocalizedEnforcement](../GameTheoryExtensions/Analysis/Protocol/LocalizedEnforcement.lean)
with base equal to the target base utility, charge and deposit zero, and the
enforced-action predicate false. Matching is the retained utility equation;
all collection obligations are vacuous. The displayed equality proves its
direct-comparison premise. Finiteness supplies a fully mixed target reference;
retained own recall supplies decision recall.

The existing theorem therefore gives, for every SE of \(R\), an SE of \(E\)
whose profile agrees at retained sites, whose retained beliefs are the pushed
source beliefs, and whose initialized terminal-history and payoff laws are
exactly the embedded laws of \(R\). It completes all new information sites
jointly. No independent choice of off-path beliefs or separate perturbation
sequence for each survivor is used.

The proof does not require late disclosures to be uninformative to survivors.
Their new information can be arbitrarily valuable. It uses the absence of a
gain for their already excluded sender and the general consistent completion
theorem.

This is a valid two-stage construction: first use the fixed-base-payoff lemma,
then add an audit that charges no retained \(E\)-history and supplies the
required collection/funding comparison. It is not necessary to construct
\(E\). The combined construction below starts directly with the smaller clean
game and compares a possibly charged excluded-owner continuation with that
clean source continuation. A charge makes this comparison easier; equality of
the target net payoff with \(F_i\) is unnecessary.

### One localized extension to the full raw game

For the primary construction let \(R\) include the counted reference and the
controlled replay actions already justified by the replay transport. Let
\(G\) be the entire bounded authenticated-session game with its final audit.
Supply the retained history/information/action embedding, the matched base
payoffs, and audit cleanliness of every retained \(R\)-history. At a copied
information site of player i, define the enforcement gate to be

\[
             \operatorname{enforced}(i,I,a)
             \quad\Longleftrightarrow\quad i\notin X(I),
\]

where \(X(I)\) is the public permanent excluded set. This gate is meaningful
only for an extra action; retained actions need no comparator. "Unexcluded"
here is distinct from being the owner of the current callback: an excluded
player can still receive a callback.

For an unexcluded actor, the authorization and first-departure classification
shows that every extra action creates a persistent intrinsic or pair witness.
The registered-broadcast drain and deterministic audit collect it with
probability one under every continuation. For global base bounds
\(L_i\le u_i\le U_i\) and nonnegative deposit \(D_i\ge U_i-L_i\),

\[
       \mathbb E[u_i-D_i\,\mathrm{charge}_i]
                \le U_i-D_i\le L_i.
\]

Any clean retained source continuation has payoff at least \(L_i\). This is
the collection-enforced branch of
`GameTheory.Protocol.InformationModel.ActionRestriction.sequential_equilibrium_extends_of_local_collection`.

For an excluded actor, do not assert that every extra action produces evidence.
Fix an arbitrary extending target profile, an arbitrary extra action and an
arbitrary belief at the copied site. Exclusion persists under every raw
continuation, and the terminal base payoff is \(F_i\). The existing owning
surface is `Vegas.phase_excluded_terminal_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean), whose premise
does not restrict subsequent play to counted responses. Nonnegative charges
and deposit give the pointwise bound

\[
          u_i(z)-D_i\,\mathrm{charge}_i(z)\le F_i.
\]

The clean \(R\)-continuation from the same hidden history has payoff exactly
\(F_i\). Averaging gives the required direct-comparison inequality for every
belief. The comparator is a whole continuation of the **source** game, as the
existing theorem requires; it is not an unsupported claim that the prescribed
target continuation remains audit-free after the extra action.

Both cases therefore instantiate one application of the localized extension
theorem from \(R\) directly to \(G\). It supplies a single consistent rational
completion at all new information sites and preserves the initialized retained
history and net-payoff law. Historical first packets by excluded owners need
not be a separately constructed intermediate game or be declared audit-free:
if they are uncharged the direct comparison is equality, and if charged it is
only stronger. Only retained \(R\)-histories must have zero audit charge.

## Exact replay and metadata are separate actions

A value's presence in the ledger does not make a later packet occurrence
strategically irrelevant. A new nonce, alternate encoding, selective duplicate
delivery, or its timing can signal other private information or change service.
There are two clean finite interfaces.

**Canonical ingress deduplication.** Identify a unique canonical signed body
by content and suppress retransmission before it changes any modeled pending
queue, receipt, observation, application state, charge, or service clock.
Replaying it consumes only the callback that silence would consume. All
noncanonical signed variants are separate protocol bodies and need their own
permission/evidence rule. This is stronger than refusing a second contract
state update after still exposing the replay to private observers.

**A larger communication game.** Keep every duplicate occurrence, metadata
choice and private receipt in the game. Then their legality and incentives need
an additional theorem. The excluded-owner extension covers occurrences emitted
after the sender's utility is fixed, but supplies no such conclusion for an
active sender. A ledger-only duplicate check is not a substitute for that
analysis.

Even strong deduplication must respect the sender's own recall. A participant
remembers choosing REPLAY instead of WAIT. This extra private memory can be
handled by a direct continuation comparison rather than deleting it.

Fix an extending target profile and force an inert replay at an embedded
source site. Other players receive exactly the same observations as after
silence. For the replaying player, store the virtual replay in a private shadow
record. A deterministic target continuation can be simulated by a legal source
continuation: feed it the source observations plus that shadow, map each inert
replay to silence, and update the shadow. Physical transitions and all foreign
views agree by induction. Thus target and source payoffs agree for that pure
continuation. With fixed opponents and the site belief, a finite perfect-recall
game has a pure continuation attaining at least the value of any specified
mixed continuation: maximize the finite multi-affine payoff over its behavioral
simplexes. Translate that pure maximizer by the shadow construction. This
supplies the whole-continuation comparator required by the same restriction
theorem. It does not require every arbitrary target policy to ignore replay
memory.

This comparator requires the strong physical and foreign-observation identity
just stated. It fails as an argument as soon as replay metadata is exposed to
another participant or affects queue service. Whether a deployed network
implements that boundary must be stated explicitly.

## Receipt-free evidence and composition

Arbitrarily retained signed packets can be broadcast in a different order from
their nonce order. The current proof that each new packet has a larger own
serial cannot be imported into that model unchanged.

Use immutable evidence appropriate to the new body format. For example, two
distinct authenticated bodies for the same physical event form duplicate
evidence; two binding bodies reusing one prepared handle form handle-reuse
evidence. These pairs do not need a claim about which arrived first. Absence
of an actual phase-installation authorization and an invalid opening proof
are intrinsic body defects. Identical canonical-byte replay is governed by
the preceding replay interface, not by inventing two signatures where there
is only one.

Evidence validity and evidence collection are different properties. A signature
does not prove that an auditor will see it. An off-network authentic disclosure
may lack a uniform collection probability. The concrete admission, publication,
audit-tail and settlement protocol must establish that bound on its actual
communication alphabet. See [the audit implementation](se-publication-audit-implementation.md)
for that separate construction and its boundary.

In a closed authenticated-session model, every modeled visible occurrence can
instead carry an outer entry record. Admission authenticates the submitting
principal, assigns the next actual-entry serial and persistently registers the
entire submitted body before exposing it to the modeled private reception
channel. This outer serial has the chronology used by the current count proof;
a pre-signed inner nonce need not have that property. The outer record must
bind the body and attributable admission, not merely certify that somebody
possessed the inner signature. Otherwise a third party's replay could create
a false charge against the original signer.

With that interface, two registered occurrences of the same inner body are
two attributable submissions. The audit may charge the second occurrence
without needing a new inner signature or a sender-claimed timestamp. Strong
deduplication is then an optional free-retransmission policy, not the only way
to handle replay. This specialization excludes a private observation that
occurs before registration: such an observation belongs to a larger
communication game and needs a different evidence producer.

The primary composition first constructs the private counted/replay SE for the
unmodified source compiler, then applies the single localized raw extension: unexcluded
extra actions use persistent evidence and the funded bound; excluded extra
actions use the direct clean-source comparator. The optional fixed-payoff
intermediate extension and strongly inert replay lemma remain useful separate
corollaries, but are not mandatory stages of this composition.

Only the retained counted construction uses the pointwise publication archive
identity. The raw extension preserves its selected initialized equilibrium law
while allowing new off-path information and supplying one common consistent
completion. It does not assert that all physically possible private
communication is already part of the current `WitnessedSubmission` interface.
