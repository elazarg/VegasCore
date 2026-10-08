# Information and release interfaces for finite commit–reveal games

This is a mathematical research note by Codex. The interfaces below are
candidate games and services, **not changes to VegasCore's runtime model**.
Results marked “paper theorem” have the proofs given here; this note adds no
Lean theorem or checked runtime adapter. The existing
[public scheduling analysis](../public-scheduling-se-preservation.md) is the
baseline positive construction. This note asks which message interfaces can
actually realize its premises, and which additional actions defeat them.

An opening has three distinct effects: it authenticates a committed value, it
discloses that value to observers, and it changes the ledger's logical state.
Their times can differ. Rejection or expiry affects the third effect; it does
not retract the second. Encryption can postpone the second effect without
making a pending packet's existence disappear. A causal prerequisite can
postpone the third effect without postponing the second.

The preservation question here is existential: for a specified source SE, is
there a target SE with the same designated logical terminal law? This differs
from requiring every target SE to have a source outcome, or requiring an
assessment to retain every off-path source belief. A counterexample below
rules out the existential outcome claim for a complete finite target game.

## Four candidate interfaces

Each interface is a family parametrized by a finite source game, a finite
public calendar where used, a fixed advertised scheduler/delivery kernel,
and an explicit fee/forfeit table. These parameters are fixed before play.
An instantiation must list every allowed extra transmission channel and its
observation law. The scheduler is chance, not an additional strategic player,
unless its utility and actions are separately introduced.

The following interfaces distinguish source withholding from transport loss.
“Withhold” is a legal source choice with its source payoff and source
observation. “Lose” is a backend outcome after some other source choice.
Identifying them requires both payoff and information correspondence.

### Public plaintext transport with explicit observation cutoffs

The owner knows its immutable committed value and can publish an authenticated
opening. A finite public calendar supplies transmission slots, application
deadlines, and later decision slots. At each eligible slot the owner can send,
wait, or use the source withholding action. A chosen send includes its payload,
event identifier and public fee. Retries or replacements are additional actions
if the interface permits them; they cannot be silently erased from its game.

A public scheduler kernel determines inclusion, expiry and observer delivery.
For example, inclusion by the application deadline can have probability q,
while every relevant observer receives a broadcast plaintext packet within a
known observation bound L. These are separate bounds. Decisions before the
observation bound may use incomplete pending information; decisions after it
use all delivered packets, including packets later dropped or rejected.
Observation histories retain those contents permanently. An expired opening
can still be authentic evidence of the immutable value.

The scheduler may adapt to earlier public traffic and fees. If it also reads
payload contents, that dependence is part of the model. Delivery probabilities
and latencies must be stated for all observer actions, including late sends.
There is no assumption that every observer instantly sees every physical send.
Conversely, a proof cannot hide a send from an observer who has already had the
specified time to receive it.

Fees are charged as explicitly specified. A source forfeit D is charged on
logical withholding or failure only when that is the game's settlement rule.
An additional compiler penalty E needs its own evidence, reporting and
collection mechanism. It is not implied by marking a packet forbidden.
Authenticity and the stated network/scheduler law are the trust assumptions;
there is no payload secrecy assumption.

**Assessment.** This is an ordinary, physically intelligible public-message
interface. It admits useful game-specific SE results. It does not generally
realize an information-preserving scheduling expansion: an unaccepted send
can disclose a value that the source failure branch keeps private, and an owner
can choose a timing signal. A closed observation window removes uncertainty
about which already-sent packets are known; it does not remove those choices.

### Owner-held ciphertexts with selective release after admission

The owner still knows its value. It submits a fixed-length encrypted packet
whose public envelope reveals the owner, event, submission slot and any fee.
The owner can submit, abstain, retry, or voluntarily publish a plaintext opening
through any additional channel explicitly included in the target game.

A sequencer or validator service first makes an irrevocable admission/order
decision. Only then does a decryption service authorize the selected ciphertext
at the source's permitted disclosure stage. “Irrevocable” means final under the
candidate model's fault assumptions; a revocable proposed block is not enough.
Excluded ciphertexts remain sealed indefinitely if the corresponding source
branch never discloses the value. A single eventual public epoch key is
insufficient for that requirement when it also decrypts excluded ciphertexts.

This is a *selective authorization* requirement, not merely threshold secrecy.
The Shutter research documentation explicitly distinguishes epoch encryption,
which exposes excluded transactions when its key is released, from batched
encryption intended to release selected transactions only. The same document
also describes a relay design where decryption can precede proposer acceptance,
so rejection or reorganization can leave plaintext exposed. These distinctions
matter more for this question than the label “encrypted mempool”.
[Primary design discussion](https://docs.shutter.network/docs/shutter/research/the_road_towards_an_encrypted_mempool_on_ethereum).

The service needs sufficient honest key holders for secrecy and sufficient
available key holders for authorized release. Admission finality and delivery
liveness are separate assumptions. Service publication is funded independently
of the owner's later willingness to send; otherwise a new withholding choice
remains. Ordinary per-message fees are included in payoffs, or a fixed service
charge is already part of the source game.

**Assessment.** This can protect an authentic dropped ciphertext's contents
from other participants. It does not hide sender-controlled metadata and does
not prevent the owner from sending its known plaintext or an opening proof.
It also does not guarantee admission before a deadline. A threshold condition
alone establishes none of these additional properties. No deployment of this
entire interface is asserted here.

### Logical causal barriers over an ordinary public transport

The source has an explicit dependency, such as “the receiver commits its guess
before the sender's opening is accepted”. The ledger requires a readiness
credential derived from that predecessor. A premature call has no logical
effect; the predecessor and its consequences are immutable once finalized.
Owners may still broadcast premature packets, and recipients see their
plaintexts according to the observation rule in the first interface.

The scheduler uses a finite public slot schedule. After the predecessor,
an honest protected call has a specified delivery/inclusion guarantee before
the opening deadline. The owner can instead wait, withhold, or take any listed
late or premature raw action. Source failure forfeits and raw penalties are
distinct settlement entries. Any penalty for premature disclosure requires an
authentic observable offence and actual incremental collection.

Trust is in ledger authenticity, finality and the stated protected service
bound. The barrier does not require a builder to keep plaintext secrets.
Pending traffic and its metadata remain physically observable.

**Assessment.** This controls the order of *accepted application effects*.
It realizes an information barrier only if the premature value is also opaque,
is strategically harmless for the particular game, or is deterred by a separate
argument. A receiving player can change a later on-chain action after reading
an off-chain proof; the application need not accept the premature opening for
that proof to matter. The negative theorem below makes this exact.

### Private source-action intake with padded, nonstrategic dispatch

This is an ideal mediated interface, useful for specifying a compiler's
retained game. It is not claimed to describe every action physically available
to a blockchain participant.

At each logical source decision the actor chooses exactly one source action
through an authenticated private intake. A trusted service receives it. The
service, rather than the actor, dispatches one fixed-size public envelope for
that stage, including when the chosen action is source withholding. Sender
identity and event identity are already public source structure. Envelope
labels, times and any other public auxiliary fields are drawn by the public
kernel described in the positive theorem below. There is no owner choice of
additional fee, packet count, retry or transmission time in this retained game.

The service stores any undisclosed content privately. It releases precisely
the source observation increment to each intended observer when the source
step occurs. A source withholding branch releases no extra value if the source
keeps it private. If the source itself has a chance failure branch, that branch
and its prescribed observations are reproduced. Otherwise source actions have
sure service completion, after a bounded random wait. Service charges are
fixed at setup and already included in source payoffs; there is no discounting
or action-dependent runtime cost.

Public envelopes can be modelled exactly as fresh opaque handles backed by
private service state. They are visible objects, not invisible pending packets.
Their public labels carry no hidden payload information. A real encrypted
implementation instead needs a computational secrecy and simulation argument;
the ideal exact-information model does not prove such a cryptographic theorem.
Service privacy, correct output authorization, bounded funded dispatch and
authenticated private intake are explicit trust assumptions.

The intake's action set includes source withholding, but excludes extra-channel
plaintext publications and selective absence of the padded service envelope.
An owner who knows its value can physically create those extra channels in a
larger real-world game. Consequently a raw-runtime theorem needs either a
separate incentive proof for those actions or a source model that already
includes them. Merely installing an honest client does not restrict its user's
strategic menu.

**Assessment.** This interface can realize the positive theorem mechanically,
including with retained private cells across many phases. It exposes exactly
which assumptions an implementation must establish. It is a restricted
mediated-game positive, not a conclusion that ordinary encrypted transactions
preserve arbitrary source SE.

## Paper theorem: source-preserving dispatch and public random delay

**Model for this result.** Let G be a finite extensive game with perfect recall.
All chance edges in its legal tree have positive probability; zero-probability
edges have been removed. Its source observations include own action recall.
Logical stage and the sequence of public source observations up to each
decision are recoverable from that player's current source information. This
requires that the source really makes the relevant stage, actor and event
structure public. Retained private state need not reset between phases.

Use the fourth interface, with no extra raw actions. Before each logical step,
the dispatch service draws public tokens from a finite kernel

\[
K_k(P(h),\tau,r).
\]

Here h is the current source history, P(h) its public projection, tau the
entire public dispatch transcript, and r a finite remaining wait budget. A
wait reduces r and leaves the source state unchanged. At zero, proceed is
mandatory. The next source action or source chance transition then executes
with its original transition law. A fresh wait budget begins for the next
logical step. Kernels can depend on every earlier public token and public
source observation; independent delays are unnecessary.

Every observation made by a strategic player is one of: its original source
observation increments, its original own-choice recall, or these public tokens.
There are no additional observable fees, omitted envelopes, private receipts,
key-share patterns or content-dependent packet lengths. Terminal utility is
the original source utility after erasing dispatch steps. The finite bound
precludes nontermination.

**Theorem, paper proof.** Every source SE has a dispatch-game SE with exactly
the same erased terminal-history distribution and source payoff distribution.
Its strategy ignores the public dispatch tokens. It reproduces the source
belief at every cloned information set, including off-path sets. This is an
existence theorem; public randomness can support other equilibria.

**Information is derived from the mechanics.** Induct over physical steps.
A wait changes only the public transcript. A source step appends exactly the
original source observation increment and own recall, plus the prescribed
public tokens. Thus an actor's accumulated observations determine precisely
(I,tau), where I is its source information. Conversely those two coordinates
determine all its observations. This is the game's constructed information
partition, not a hypothesized posterior-equivalence premise. Public-prefix
recoverability ensures that no source-hidden actor or event history is exposed
by dispatch structure.

**Consistency.** Take a source SE (sigma,mu) and its single fully mixed
consistency sequence sigma_n with Bayes beliefs mu_n. At every physical copy
of I use sigma_n(I); this is fully mixed on exactly the source action menu.
For a compatible source history h and public transcript tau, multiplying the
primitive transition probabilities gives

\[
w'_n(h,\tau)=w_n(h)L(h,\tau),
\]

where L is the explicit product of K's probabilities. This equality follows
by induction: a wait multiplies only L; a source step multiplies w_n by the
unchanged action or chance probability. For histories h,h' in one I and fixed
tau, every K input is identical by public-prefix recoverability. Therefore
their compatibility with tau is the same and

\[
L(h,\tau)=L(h',\tau)=L_I(\tau)>0.
\]

Bayes cancellation at the fully mixed index gives

\[
\mu'_n(h,\tau\mid I,\tau)
=\frac{w_n(h)L_I(\tau)}{\sum_{g\in I}w_n(g)L_I(\tau)}
=\mu_n(h\mid I).
\]

The target strategy and belief sequence converge to the copied strategy and
belief. No conditioning on a limiting zero reach probability is performed.
The same sequence works at all target sites; off-path assessments are not
chosen separately.

**Sequential rationality.** Fix one target site (I,tau) and any local action
lottery beta there. Use beta once and the copied sigma at all later sites.
For each compatible source history, erase the physical continuation. Its law
is the original source continuation with beta at I and sigma afterward:
bounded waits terminate with total probability one, and each succeeding
logical step has the original chance or chosen-action law. This is an
induction on remaining logical steps, independently of the reach-weight proof.
The target belief averages these conditional laws using exactly mu(I), so its
local payoff comparison is the source comparison. Source sequential
rationality makes every such comparison nonpositive. The constructed target
has perfect recall; finite-game one-shot-deviation equivalence gives whole
continuation optimality, including policies reacting to later public tokens.

Finally, the same execution induction from initialization, without a
deviation, gives the exact erased terminal law. Equivalently, the total L
weight of compatible terminating transcripts for each source terminal history
is one. This completes the proof.

**Scope relative to VegasCore.** This instantiates the paper construction in
[public scheduling](../public-scheduling-se-preservation.md) with explicit
message/observation mechanics. It is not a new checked general AsyncServiceSpec
adapter. It admits random adaptive public delay and retained hidden bindings.
It does not admit an owner-controlled metadata signal, unrequested source
failure, plaintext leakage on a hidden withholding branch, or an extra early
disclosure action. Those require additional arguments, not changes in this
proof's terminology.

## Paper theorem: free authentic early disclosure destroys preservation

**Source model for this result.** Nature samples a fair bit b. The sender
learns b; the receiver sees a perfectly opaque binding commitment to it, with
fixed public metadata independent of b. The receiver chooses a guess g in
{0,1}; that chosen guess is public. The sender then chooses Open or Withhold.
Open publicly authenticates
the immutable b. Withhold keeps b concealed and costs the sender D>1. Both
players have base payoff [g=b]; only the sender pays D on Withhold. All
decisions have perfect recall. There is no scheduler risk or fee.

At the sender's last decision, Open strictly dominates Withhold for every
history and belief. The receiver acts before any bit disclosure, so every
source SE has probability 1/2 of g=b. For concreteness select the source SE
where g=0 and the sender always opens. Put epsilon_n=1/(n+3) in the
consistency witnesses below. It is consistent: tremble the receiver
to g=1 with epsilon_n, and each sender continuation to Withhold with epsilon_n.
The receiver's Bayes prior stays fair. At all sender sites its known b and g
fix the relevant history; opening is optimal. This is a fully mixed common
witness as epsilon_n decreases to zero.

**Complete target model for this result.** Insert one sender decision before
the receiver's guess: Early or Wait. Early broadcasts a valid opening proof
of the same immutable b, which the receiver obtains before its decision. Wait
sends no early proof. At the public cutoff, the receiver observes either the
proof and b or the absence of a proof. It then chooses g. After either Early
or Wait, the sender has the original final Open/Withhold choice. Early changes
no application publication state: a ledger can reject its premature state
update while the proof remains readable and authentic. Only final Open records
the logical publication. Early is free and carries no penalty.
There are no other sends, retries, choices, channels or hidden scheduler draws
in this finite target. Its erasure retains (b,g,Open/Withhold), ignoring the
physical Early/Wait label. The receiver really sees no-early metadata; no
pending message is made invisible.

This opening can be a certified premature mailbox message rejected by the
application, or an authenticated off-chain proof delivered before the cutoff.
Both provide the same information in this target. Later logical rejection
does not remove its authentication or disclosure effect.

**Theorem, paper proof.** Every target SE has g=b and Open with probability
one. Therefore no target SE preserves the designated source equilibrium law,
even after erasing b and retaining only whether the guess is correct. The
statement also holds for any weak PBE requiring sequential rationality at all
information sets and beliefs supported on compatible histories.

**Proof.** On either continuation Open still strictly dominates Withhold.
After Early the receiver's information set contains only histories with the
disclosed b. Its unique best guess is b, reached or not. Consequently each
sender type can obtain payoff 1 by choosing Early. The sender's payoff cannot
exceed 1 on any terminal history. Sequential rationality at that type's
initial choice therefore forces conditional expected payoff 1. No rational
final withholding occurs, so payoff 1 forces g=b almost surely for each type.
Averaging over the fair prior proves the claim. In the source, correctness
has probability 1/2. Its Bernoulli correctness law and the target's have total
variation distance 1/2. This rules out a preserving SE, rather than just
showing that one copied assessment is not rational. QED.

The target has an SE: both types choose Early; the receiver guesses the bit
after a proof and chooses 0 after Wait; the sender opens after either route. For a
consistency witness, both types choose Wait with epsilon_n, the receiver
chooses the wrong bit after a proof with epsilon_n and chooses 1 after Wait
with epsilon_n, and the sender withholds at every final site with epsilon_n. Every
legal action has positive probability. The Bayes belief after Wait is fair;
all other relevant beliefs are determined by known b, g and own recall.
The limiting choices are sequentially rational. Thus nonpreservation is not
explained by target equilibrium nonexistence.

**Scope relative to VegasCore.** This is a complete finite comparison game
with ordinary immutable commitments, intrinsic source withholding cost and
an extra authentic disclosure channel. It is not an embedding theorem for
the repository's raw actions, audit or readiness credential. A protected causal
barrier removes Early from faithful application execution, but a full raw game
must still account for the information in a physically available early proof.
The example does not imply that every public mempool changes every source SE.

## Paper contrast: an incremental disclosure charge repairs this game

**Model for this result.** Use exactly the preceding source and target trees,
but charge a fixed incremental amount C on Early and no added charge on Wait.
The charge is collected with certainty on every permitted Early route,
regardless of past infractions, later inclusion or reporting choices. Original
Open/Withhold settlement is unchanged. No uncharged off-chain copy is included
in this finite game.

**Theorem, paper proof.** If C>=1, every source SE has a preserving target SE.
If C>1, every target SE uses Wait, opens finally, and has the law of a source
SE. This is a game-specific sufficient interface, not a universal penalty
bound for commit–reveal games.

For a *selected* source receiver policy choosing guess 1 with probability p,
the exact condition for the all-Wait copied assessment is

\[
C\geq 1-f_{\mathrm{match}},\qquad
f_{\mathrm{match}}=\min\{p,1-p\}.
\]

Indeed its two sender types get p and 1-p from waiting, respectively, and
1-C from Early. Equality is sufficient for existence of that copied SE;
strict inequality makes both early deviations strictly worse. If C consists
of publication fee kappa plus additional incremental penalty E, substitute
C=kappa+E. Uniformly over all source receiver policies, f_match can be zero,
so the before-selection bound remains C>=1. The weaker C>=1/2 works for
copying the fair mixed-guess policy, not for arbitrary specified source SE.
It also does not imply that every target SE preserves a source law.

**Proof.** After Early the receiver still guesses b, giving its sender type
payoff 1-C<=0. After Wait and final Open a type receives a probability of
matching, hence a payoff at least zero. Copy any source receiver strategy,
choose Wait and finally Open, and require truthful guessing at each Early
site. Wait is optimal for both types, and the receiver is optimal after Wait
under its fair prior. For an explicit fully mixed witness, use sender Early
probability epsilon_n at both types, final withholding probability epsilon_n
at every route, receiver guess-1 probability (1-2*epsilon_n)*p+epsilon_n
after Wait, and wrong-guess probability epsilon_n after Early. The Wait
posterior stays fair, while all other beliefs are determined by known bit and
own recall. This proves consistency and preservation. When C>1,
Early is strictly dominated, so every target SE chooses Wait. Bayes at the
reached receiver site gives the fair source prior; final Open is forced. The
remaining target assessment is a source SE. QED.

Collection on an early *on-chain* mailbox transaction can be defined as an
automatic debit. Collection on any off-chain transmission of a valid proof is
a much stronger condition and is not supplied by ordinary ledger execution.
If the owner can send an uncharged copy, the previous negative proof applies
again. A one-time owner penalty already charged earlier is not an incremental
C for this result. A funded honest client, or an offence label without an
actual charge, does not discharge the premise.

For the same target with an ordinary early-publication fee 0<=f<1/2 and no
penalty, sequential rationality gives each type expected utility at least
1-f. Since utility is correctness minus the nonnegative publication fee,
every target SE has correctness probability at least 1-f>1/2. Hence even a
positive small physical publication cost does not restore preservation of
the source correctness law. This bound does not claim correctness is exactly
one when f>0.

## Paper theorem: forced informative observations obstruct a universal claim

**Model for this result.** Nature draws a finite hidden state theta with fixed
prior lambda. A single receiver chooses Safe or Guess. Safe pays t; Guess pays
[theta in A] for a specified subset A. In the source the receiver gets no
signal before choosing. In the target, before that same choice, a fixed finite
chance channel W(y|theta) emits an observed signal Y. There are no other
players, actions, fees or utility changes. Retain the receiver's chosen action
in the logical outcome. Impossible signal outcomes are removed from the tree.

Assume the channel is informative: some posterior distribution of theta given
Y differs from lambda. There is then a subset A such that
q(y)=Pr(theta in A|Y=y) is nonconstant on positive-probability signals. Its
mean is p=lambda(A), so max q(y)>p. Choose p<t<max q(y). All payoffs remain
in [0,1].

**Theorem, paper proof.** The source has a unique equilibrium action Safe.
No target SE preserves its action law. Every target SE has total variation
distance at least Pr(q(Y)>t)>0 from the source action law.

**Proof.** In the source, Safe's expected payoff t strictly exceeds Guess's
payoff p. In the target, the receiver's information set following each y has
the unique Bayes posterior from the fixed chance channel, because no player
action precedes it. At every y with q(y)>t, sequential rationality strictly
requires Guess. That set of signals has positive probability. Hence the
target chooses Guess with probability at least Pr(q(Y)>t), whereas the source
never does. The total variation distance on the action coordinate equals the
target probability of Guess. Best responses at the remaining signal sites
exist, and fully mixed receiver trembles leave the chance-generated beliefs
unchanged, so the target has SE. QED.

**Scope relative to ledger interfaces.** This is a necessary-condition test
for preservation *over all bounded utility specifications*: a forced observable
that distinguishes a source-hidden state can change a finite decision problem.
The same test applies within a fixed source information set using its
conditional prior. A content-dependent delay, length, status or key-release
pattern may provide such a Y even when the payload is sealed. It does not
prove that every informative signal changes every fixed game's equilibrium,
and it is not a general compiled-runtime impossibility. Voluntary publication
is a strategic action rather than this theorem's forced channel; the preceding
early-opening theorem analyzes that distinction separately.

## Timed commitments and ownership of the plaintext

Boneh–Naor timed commitments provide a forced-opening procedure through which
a receiver can recover the commitment without the committer's later help.
That is useful for removing a later *strategic cooperation requirement*.
It does not make all publication transport disappear, authorize release only
on final inclusion, or prevent a committer who knows the value from voluntarily
opening sooner. Those are separate properties, and none follows from the
forced-opening definition.
[Original paper](https://www.iacr.org/archive/crypto2000/18800237/18800237.pdf),
[author's description](https://crypto.stanford.edu/~dabo/pubs/abstracts/timedcommit.html).

A service holding decryption shares can autonomously release a ciphertext,
but its threshold does not control a plaintext already known by its owner.
Removing that owner's early-publication ability by giving it no knowledge of
the value changes the source information whenever the source player is meant
to know that value. Such service-generated or dealer-held inputs can be useful
in their own source games; they are not implementations of arbitrary
owner-known private choices.

For realistic cryptographic implementations, exact mathematical SE in a game
with perfect opacity should not be confused with unrestricted exact SE over
actual ciphertext bytes and unbounded adversaries. A computational equilibrium
notion, adversary resource bounds and an information simulation are needed.
Off-path sequential incentives require particular care: small unconditional
distinguishing advantage is not by itself a uniform bound on every rare-site
posterior or conditional regret. This note proves no such cryptographic
refinement and makes no claim about a deployment realizing all four interfaces.

## Summary cards for the research catalog

| Candidate or result | Main primitive conditions | Conclusion and status | Missing for an ordinary raw runtime |
| --- | --- | --- | --- |
| Public plaintext with closed observation windows | Explicit inclusion and observer latency; all delivered stale contents retained; timing/fees listed as actions | Physically ordinary candidate interface; no generic preservation theorem here | Legitimate withholding and dropped plaintext may have different source information; owner signals and extra early disclosures remain |
| Selective sealed release after irrevocable admission | Visible envelopes; excluded ciphertext keys never authorized; funded release; separate admission finality and key-holder assumptions | Candidate mechanism for protecting excluded payloads | Owner-held plaintext, metadata, failures, and irrevocable admission still need analysis |
| Logical causal barrier | Immutable predecessor and readiness credential; premature packets physically visible | Accepted effects follow logical order | Information already delivered by a premature proof is not undone |
| Padded private-intake dispatch | Exactly source actions/observation increments; chance-only finite public waits; source-public prefix recoverable; source payoffs | Paper theorem: every source SE has an exact preserving SE, including retained private state and off-path consistency | Actual private intake, padding/dispatch, cryptographic secrecy, and extension to additional raw actions |
| Free authentic early opening | Fair owner-known committed bit; receiver guesses before lawful final opening; D>1; optional early proof visible before guess | Paper theorem: no target SE/PBE preserves the source correctness law; all target SE correctness is 1 rather than 1/2 | Native embedding would need exact menus, credentials, physical observations and collection law |
| Certain incremental Early charge | Same finite tree; every Early route costs C>=1 | Paper theorem: every source SE preserves; C>1 also forces every target SE to be a source outcome | An uncharged off-chain proof or previously spent one-time charge invalidates this premise |
| Forced informative observable | A finite chance signal about a source-hidden state before one payoff-relevant choice | Paper theorem: some bounded utility specification has no preserving target SE; explicit positive total variation bound | Does not refute preservation for each fixed game or establish a native channel embedding |

The useful general separation is between *release authorization*, *what each
player can learn before its choices*, and *which extra transmissions players
can choose*. These interfaces permit finite-game rationality analysis without
requiring hidden pending existence. They do not support the claim that sealing
payloads, adding a logical dependency, or replacing a later opening by forced
recovery alone is a universal SE-preserving compiler construction.
