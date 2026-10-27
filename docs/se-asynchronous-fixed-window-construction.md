# A finite asynchronous service with source-preserving timing

This note constructs a service and a joint timing policy, rather than assuming
that a suitable timing policy exists. It proves a mathematical preservation
result for the proper-entry game described below. The construction has
unobserved individual sending decisions, partial network reception, partial
ledger batches and contract
deadlines. It does not make the order of senders public and does not flush an
unrelated mempool.

The result is narrower than the arbitrary-builder target. In particular, it
uses a full-support delayed-delivery service with enough reserved capacity to
hide a first qualifying entry until the last protected block. A bounded
inclusion inequality alone does not imply this support property. The source
program must also admit the phase grouping specified below. These are explicit
model choices, not conclusions about an unchanged blockchain or the current
phase implementation. None of the new results in this note is Lean-checked.

The complementary probability and incentive argument is in
[the pre-exit construction](se-asynchronous-pre-exit-construction.md). The
[authenticated audit construction](se-asynchronous-authenticated-construction.md)
addresses the larger raw-message game separately. The
[combined finite theorem](se-asynchronous-preservation-theorem.md) states
the complete model and composes these components.

## The semantic and utility interface

Start with a finite perfect-recall source game. At a private-choice phase,
each participating player chooses one finite legal vector. Its information is
its original phase-entry information and its earlier private choices. No
external source information arrives during that vector choice. Later public
phases reveal the designated values, and the next private choice has the same
source information as before compilation.

Sequential source choices can be grouped in this way when their menus depend
only on phase-entry information and the player's own earlier choices. The
mathematical batching theorem is in
[the source batching analysis](se-private-mempool-compilation.md#a-language-level-batched-source-semantics).
One fully mixed behavioral witness induces the vector law by multiplying its
successive own-action probabilities. A vector deviation is a legal source
continuation deviation. Consequently every selected source SE has a vector
SE with the same initialized law. Grouping across a new public sample,
external private signal or intervening public observation is not justified by
this theorem.

The intended Vegas source supplies relevant parts of this interface.
`Vegas.SourceGuardRead` in [Basic](../Vegas/Source/Basic.lean) permits public
data, existing publications and the guard author's own commitments. It does
not read a foreign private commitment or a private input directly. In
[IntendedGame](../Vegas/Source/IntendedGame.lean),
`Vegas.SourceProgram.GuardsSatisfiableFrom` and
`Vegas.SourceProgram.Setup.WellFormed` ensure that an intended continuation
always has a predicted valid choice.
`Vegas.SourceProgram.mem_intendedValues_self` identifies those choices with
the intended menu when that menu is satisfiable. Thus private-type-dependent
value menus need not change the number, size or type of operational entries.
The particular grouping of an actual program still has to respect its public
information boundaries.

Each player i has a fixed exclusion utility F_i, at most every source terminal
utility of that player. Once i is excluded, its base utility is F_i under
every continuation. Surviving players' handler utilities may be arbitrary
bounded values; they need not be at least F_i.
All utilities lie in a fixed finite interval; let B bound the difference
between any two base utilities of a player. Proper execution has no extra
time-dependent utility, message fee or unrefunded charge. A different cost
model requires including those costs in the comparisons.

The fixed-floor property has an existing runtime surface:
`Vegas.phase_excluded_terminal_payoff` in
[PhaseExclusionPayoff](../Vegas/Game/PhaseExclusionPayoff.lean) quantifies over
arbitrary subsequent menus and profiles. Here the same property is part of
the specified controller. Audit charges are outside this base-utility theorem.

## Fixed public windows and asynchronous broadcasts

Time is a finite sequence of block indices. A window starts at public time r.
There is at most one required first entry per participating player in that
window. Fix positive integers Gamma and Delta, and put

    A = r + Gamma,             D = A + Delta.

Every player can broadcast at each time r+1,...,D-1. This finite time grid
models simultaneous availability to act, not exclusive public sender turns.
Everybody can know that other players have this ability. Individual WAITs
and the order of individual broadcasts are not automatically observed; only
the actual network receipts and ledger records are observations. A is the
last protected admission time. A correct first entry admitted by A is
guaranteed to be recorded by D.

There is one broadcast action, with potentially different receipt times for
different recipients. The sender does not choose a confidential destination.
The kernel described below can leave a broadcast unexposed to the observer
for some time. That is a possible delivery outcome, not a private channel.

Ledger processing at time t precedes that block's individual broadcast choices.
A first entry sent at time a can first be recorded after a and must be recorded
no later than a+Delta. The choice Delta>=1 makes this order consistent.
At time D the ledger is processed first, then the controller publishes the
window's success and exclusion results. There is no further current-window
proper first-send opportunity after this settlement. Observable retransmission
of an already known entry remains a separate transport action.

Inclusion does not enable a later strategic window early. Its readiness time
is fixed by the public controller. Thus sending sooner cannot select an
earlier retry clock or give another player an extra source decision before
the current boundary.

For commitment phases, one entry may carry the player's whole legal vector
as a fixed tuple of distinct opaque handles, one per source component. The
public accepted-binding record names the physical block, owner and component
index. No new cryptographic commitment-to-vector primitive is needed.
An opening packet discloses only components designated by the current original
source reveal block, using each component's own ordinary opening certificate.
It does not publish all components of the binding packet at its first resolve.
The distinct component handles are distinct physical bindings, so legitimate
component openings do not count as handle reuse. This retains the original
disclosure order when later components survive across a new source sample
or commitment block.

On a missed commitment-window deadline, the current commitment block
is rolled back and missing owners are permanently excluded. All current
private vector choices are then discarded from the live source state. The
alternative is to use smaller fixed windows and publish the first exclusion
and roll back the block immediately at a failed window boundary. The proof
does not cover a controller which silently accumulates missed earlier-window
deadlines while continuing to offer later private choices before any public
exclusion.

Resolve windows can batch each owner's components from one original
consecutive reveal block into one entry. Smaller layers are also possible
when they retain the original public source boundaries; no resolve moves
across an intervening source sample or commitment merely to make a guard
check earlier. A missing resolve publishes that owner's exclusion at the
window boundary. No source choice is offered between that failure and its
public announcement. A guard can be checked when its last required input
becomes public, as in the source semantics. Guard failures caused by an
unintended value are not called network delays; the present proper-entry game
contains only intended values and their truthful certified openings.

After a closed window, a Delta-long recording interval can precede the next
window. Every proper entry emitted before closure is then recorded, including
an entry that missed its semantic deadline. After a reveal block this interval
is required before the next binding window. It yields actual ledger
publication of previous proposals, not a new assumption that private receipt
is common knowledge. Taking such an interval after every window is a simple
finite implementation which also bounds the number of outstanding entries.

## A causal partial-batch inclusion kernel

Fix M as an upper bound on proper entries simultaneously covered by one
window and its recording interval. More generally fix B_raw as the finite
bound on distinct qualifying authenticated bodies in the raw domain, and
reserve capacity for that full bound when composing the raw extension.
This is application capacity, not a promise
to process all unrelated transactions.

The channel state retains every distinct qualifying authenticated body e and
its first broadcast time a_e. This is an irreversible in-flight obligation,
not a public registration oracle and not a selection of the first body for
each slot. Conflicting bodies can reach a relay in either order; neither can
cancel the other's publication promise. Exact repetitions of the same body
do not create another inclusion job. At block t, let P_t be the unrecorded
qualifying bodies and let

    U_t = {e in P_t : a_e + Delta = t}.

The inclusion kernel chooses a subset J_t with

    U_t subseteq J_t subseteq P_t.

Every such subset has strictly positive probability. For example, independently
include each nonurgent pending entry with probability 1/2 and include every
urgent entry. The finite traffic bound ensures the reserved capacity can
always process J_t. The actual ledger batch may be empty or a proper subset
of the queue. At a deadline it processes the entries whose individual promises
are due, not an unrelated queue.

This gives a causal finite process. An entry not included earlier becomes
urgent at a_e+Delta and is included then. It follows by induction that every
qualifying body is recorded within Delta. The promise survives later
replacement attempts, game rejection and sender exclusion: those actions
cannot delete or change an earlier retained body or its deadline. Exact
retransmission does not add a service job. Extra raw traffic must not consume
this reserved capacity; that is a requirement of the raw extension, rather
than a fact about application-level idempotence.

One concrete interpretation is a joint network/block service: a selected
body reaches an evidence-retaining execution ingress in time for that block
and is recorded there. Partial gossip to other recipients can precede this
event. The bound Delta is on broadcast-to-recording, not merely on inclusion
after an unbounded relay-arrival delay. Channel state can carry an undelivered
body without any player seeing it or knowing its global emission order.

This joint support condition must not be replaced silently by two unrelated
upper bounds. A strict propagation bound P followed by a chain bound I may
force a packet to become observable before P+I; retiming it while preserving
a later first exposure may then be impossible. Adding P+I proves a deadline,
but not the history-repair support used below.

No monotonicity of an individual sampled inclusion time in its submission
time is claimed. Submitting earlier may lead to a different random queue
history. The proof below optimizes actual timing instead of using such a
monotonicity assertion.

The capacity bound matters. If only one qualifying entry can be processed in
the last block but two still-hidden entries would become due together, the
repair below may be impossible. A service which distributes a weaker capacity
guarantee across several earlier blocks may make late absence informative.
The condition here permits all currently protected entries to remain hidden
until their last protected block. It is stronger than merely stating that
some fixed builder meets all honest-path deadlines.

## Partial delivery and canonical identities

At a block decision a player chooses one broadcast batch. For each known
canonical body it chooses a multiplicity in {0,...,L_copy}, for a fixed finite
L_copy.
If its current owned slot is unsent, it may also introduce one fresh proper
body with a multiplicity in {1,...,L_copy}. The choice zero for every coordinate
is silence. L_copy=1 gives arbitrary subsets of known bodies plus an optional
new own entry. Larger L_copy retains visible same-block duplicate counts.

There is no smaller aggregate packet cap which might prevent adding the new
own body while keeping the old replay coordinates. The finite alphabet,
number of blocks and per-body multiplicity bound already give a finite total
traffic and funding bound. This is one broadcast action, not a confidential
outbox or a tagged second channel. Splitting its new-body and replay parts is
only a unique description of the chosen batch. A one-packet-per-block menu
would not support the repair: an observed foreign replay at A could then
prevent the same player from adding its own first broadcast there.

Each broadcast occurrence can be delivered to different subsets of players
at different times before its entry's ledger inclusion. Delivery reveals the
full authenticated envelope to that recipient. Conditional on the physical
prefix, every allowed delivery subset, including no new delivery, has positive
probability. Fresh delivery coins are independent of the source secrets and
do not inspect payload values when choosing recipients or times. An included
entry becomes public through the ledger. Recipients may also observe later
duplicate occurrences; the observer is not forced to deduplicate its memory.

This is a concrete, content-blind partial-reception model. It allows different
players to see different pending packets and to remember them. It does not
allow an unseen offending payload to alter the probability of an innocent
marker reaching a bystander. That broader observation rule would require a
different argument and, for the audit extension, a different accountability
analysis.

Proper commitments have fixed public metadata for their physical slot and are
opaque. Proper openings carry the value and the canonical certificate of the
actual accepted binding. Slot identities or content identities are used for
entries. An envelope does not authenticate its original private send time,
nor a global rank among all unobserved submissions. Such a field would defeat
retiming while preserving the envelope seen by a recipient. Inclusion times
and the order in the public ledger remain genuine public observations.

The transport can assign a receipt or registration identifier when an entry
first reaches the corresponding receiver or relay. The proof preserves those
exposures and identifiers. It must not reinterpret such an identifier as a
certificate of an earlier, invisible sender opportunity. Ordinary private
signing and choice of a preimage are local computations, not additional
communication channels.

In the operational quotient, identify the unique proper entry by its physical
slot. If its concrete content hash depends on the opening value, that hash
is part of the payload component, not an independent operational signal.
The service and timing policy do not branch on that hash. This avoids silently
calling a value-dependent identifier source-independent metadata.

Within a proper window, packet sizes, service eligibility, opportunity menus
and selection probabilities depend on its public syntax and operational
history, not on the secret value. This is enforced by fixed-size encodings and
the service rule above. The chance kernels are fixed once for the game; none
is changed with a perturbation index or after a deviation.

## Why a late foreign packet has an early-send explanation

Consider any actual information set of player i at time t<D before the first
public exclusion. Keep i's entire private observation and action history,
the public ledger prefix, and the initial source realization fixed.

For each other participant j whose current first entry was sent after A,
retime its first admission to A. Preserve every earlier opportunity and WAIT,
the same proper semantic choice, and the same envelope. Keep the original
late broadcast batch, whose copies of that body are now retransmissions.
At A keep every original replay coordinate and add one occurrence of the
fresh own body; that coordinate was zero because this is an abnormal history.
Hide the additional A occurrence throughout the observed prefix.
Keep all already-observed receipt occurrences, including duplicates, and all
ledger inclusions unchanged. If no entry has yet been sent, add a first send
at A and hide its occurrence; when t<A this send can still be in the future.
Existing admissions at or before A keep their times and occurrences.

For a retimed late entry, the repaired deadline is exactly D. Therefore no
extra inclusion was compulsory before t. For an unchanged early entry the
original service promise already supplies all compulsory inclusions. Every
observed ledger subset remains legal in the repaired prefix: additional hidden
entries need not be selected yet, and the reserved capacity makes their later
deadline completion feasible. The required delivery choices and inclusion
choices have positive probability. Other actors'
receipts can also be preserved by hiding the added pending entry until its
original exposure.

The changed sender's own action history is different. This is allowed:
the repaired history is required to remain in i's actual information set,
not in every player's original information set. No later strategic source
choice occurs in that same window. Every original retransmission remains
available: the repaired sender knows the same received bodies and additionally
knows its own earlier entry. The original late first-send action is now an
available same-body replay with the original multiplicity. At all other
choices the repaired sender repeats the original broadcast batch. Per-body
coordinate bounds are unchanged. Its first admission is the only
extra service job, and it replaces rather than supplements the old late job.

The repair never changes a source secret or a value visible to i. During a
commitment window the payload is opaque. During a resolve window the same
already-fixed truthful value is used. At a binding window every earlier
qualifying opening is already public by the recording interval. Thus this is
an actual information-fibre repair; it does not give i a fictitious complete
pending-packet archive.

There are two important limits. First, it applies before the deadline result
is public. After D, an absent entry is a real exclusion and is not repaired
into a successful history. Second, an authenticated original-send timestamp
or an observable ordinal counting every broadcast would invalidate this
particular repair. Knowing merely that j could have acted at earlier times
does not invalidate it: those earlier WAITs are preserved, and the changed
decision at A is not automatically observed.

### A finite timing example

Take r=0, Gamma=2 and Delta=3, so A=2 and D=5. A foreign owner broadcasts
its first correct entry at time 3; the focal player receives it at time 4,
and at that focal decision it is still absent from the ledger. In a repaired
history the owner first broadcasts the same entry at time 2, that occurrence
is not delivered to the focal player, and the time-3 broadcast is its replay.
The focal player receives exactly the same body at exactly the same time.
The repaired entry must record at 5; its earlier absence is legal. The
original late entry could instead remain absent until 6, so the two
histories have different future failure risks despite the same present
observation. The epsilon-weight comparison selects the former explanation
in the consistency limit.

With two qualifying entries, a capacity of two at block 5 permits both
protected entries to remain absent through block 4. No previous block has
to flush them. With capacity one and two such missing protected entries,
that prefix has no all-normal completion by 5. At least one late admission
can then be known before settlement. This is a concrete reason the capacity
and support hypotheses cannot be omitted.

### A uniform conditional probability bound

Before A, prescribe fixed positive probabilities of first SEND and of the
other available operations. They depend on the public window/time and the
known canonical entries, not on source values or hidden timing history. At A,
an unsent participant chooses its first SEND with probability 1-epsilon;
all alternatives have total probability epsilon. After a protected first
admission, prescribe a fixed full-support law on every available canonical
replay batch, including silence. Since the finite message domain is fixed,
each available batch has probability at least a constant d>0 independent of
epsilon. Conditional on a protected fresh SEND, use fixed positive laws for its copy
multiplicity and for the accompanying known-body replay batch; include these
factors in the same lower bound d. Only the timing laws after an unprotected
late admission, or while
still unsent after A, will need equilibrium optimization.

Call a foreign participant abnormal if it has not admitted its first entry
by A. A history with this defect contains an A decision of total probability
at most epsilon. The repair replaces that decision by a first SEND of
probability 1-epsilon. The proper source-choice factor moves to A unchanged.
The focal player's behavioral factors are unchanged because its full own
history is unchanged. Every changed operation of the repaired sender after A
is now governed by the fixed protected-sender replay law, with probability
at least d; the corresponding original late-policy factor was at most one.
Thus retaining observed duplicates costs a fixed finite factor, not an inverse
power of a vanishing late-action perturbation.

The game has finitely many chance prefixes, and every repaired chance prefix
has positive probability under the fixed kernel. Hence there is a finite
constant C, independent of the source witness and of epsilon, such that at
every such actual information set I,

    Pr(some foreign participant is abnormal | I)
        <= C epsilon / (1-epsilon)^M.                         (1)

One elementary choice of C is a bound on repair multiplicity times the
reciprocal of the smallest positive chance-prefix mass and of d to the maximum
number of changed replay choices. The exact constant
is not needed for the limiting result. No lower bound on Pr(I) is used:
the repaired probability is charged to histories in the same information
fibre. Focal past WAITs are preserved, so (1) also covers information sets
reached only after the focal player's own operational mistakes.

Source choices can be presampled from the reference behavioral kernels when
constructing this comparison. This is only a probability representation; an
unsent latent value is not disclosed to its owner or added to the actual
game. It makes explicit that retiming one proper send retains exactly the
same source factor. When a literal response encoding has extra aliases, their
conditional probabilities and repair multiplicities must be included; the
canonical model here has none.

A normal foreign participant is guaranteed to finish by D under every focal
proper continuation. This follows from its admission by A and its
individual inclusion promise, which is not revoked by another player's
actions. Before A, the future probability of failing to send at A is at most
epsilon per foreign participant, even after any focal continuation.
Consequently

    Pr(foreign current-window failure | I, any focal continuation)
       <= C epsilon/(1-epsilon)^M + M epsilon.                 (2)

The conditioning in (2) uses the reference Bayesian belief at I and then
allows the focal continuation to change. It does not recompute that belief
from a newly selected deviation. This is the conditional comparison required
for sequential rationality.

## Constructing a joint timing policy

Erase payload values while retaining all actual operational observations:
own opportunities and actions, slot identities, private receipt metadata,
the public ledger, and the public clock. Stop this finite operational process
at the first public exclusion. At an unsent slot a broadcast batch may contain
a first SEND as well as known-body retransmissions. After first SEND only
known-body batches remain. A replay may forward another author's known
entry; the occurrence records its actual broadcaster without pretending that
the broadcaster authored the signed body.
Give each information set K its own agent. If it belongs to player i, that
agent's auxiliary terminal payoff is

    Q_K = 1{K is reached} * 1{i's entry in K's window records by its D}.

For an agent whose player has no required entry in the current window, take
the completion indicator to be one. The window's completion is determined
at or before the stopping boundary.
Different agents can have different auxiliary objectives. Their underlying
history law is shared, so their conditional beliefs are jointly generated.
This game may have interacting inclusion decisions and correlated chance;
it is not a collection of independently optimized one-player problems or
independently chosen window priors.

Fix 0<eta<epsilon<1/2. Before A fix the positive early-send hazards and the
full-support silence/replay laws above. At A fix first SEND probability
1-epsilon and distribute epsilon positively over the remaining operations.
After a protected admission, and for a player without a current required
entry, fix the full-support silence/replay law. At the remaining post-A
information sets impose positive action floors with total mass at most eta.
A finite agent game with these compact
convex strategy sets has a Nash equilibrium. Choose one such equilibrium.

At an optimized late operational information set K, the reach probability is
positive and independent of the current agent's action. Dividing the exact
agent Nash inequality by that reach probability gives conditional optimality
among the floor-feasible distributions. Moving the residual mass to a pure
action loses at most the total floor mass, since completion lies in [0,1].
Thus the pure one-step completion regret at K is at most eta.

At or before A, the prescribed continuation admits by A with probability at
least 1-epsilon. Every such admission completes regardless of opponents'
subsequent proper actions. Thus the reference completion probability is at
least 1-epsilon and every alternative has probability at most one. Its
completion regret is at most epsilon even though the agent was fixed. After
a protected admission its completion is already certain, so every silence or
replay action has completion regret zero. The same holds for an actor without
a required entry under its constant auxiliary objective.

This gives a single joint profile alpha_(epsilon,eta) whose completion regret
is uniformly at most epsilon at every operational information set. It also
has the protected-cutoff mass and replay floors needed in (1). The construction allows a late
WAIT to be preferable to a late SEND. It chooses the actual optimal late
response instead of asserting prompt-send dominance after every history.

The usual finite-game existence theorem is used only for this explicitly
defined auxiliary payoff and for the post-exclusion completion below. It is
not an assumption that the desired source-preserving equilibrium already
exists.

## Payload observations do not invalidate that timing equilibrium

Let X contain the source realization and semantic random choices. Let Z
contain the operational chance and timing randomization in the current window.
Under the prescribed proper profile, these have a product law conditional
on the relevant public semantic history. The metadata is K(Z). During a
reveal, the actor can additionally receive values V_K(X).

At an actual information set (K=k,V_k=v), the conditional law is proportional
to

    mu(X) 1{V_k(X)=v} * nu(Z) 1{K(Z)=k}.                        (3)

Thus the operational posterior is the same as at K=k in the auxiliary game.
Receiving an opening can change the conditional source payoff, but it does
not change the optimal completion policy. The source surplus is always
nonnegative because F_i is a pointwise floor.

At a binding decision, current wire contents are opaque and all earlier
opening proposals are public. The same factorization gives the original
source posterior at its information set J. Arbitrarily correlated private
source inputs are allowed: only the operational randomization is independent
of the whole source realization.

These identities would fail if fee, size, routing, eligibility or deadline
probabilities depended on the hidden value, or if the selected timing policy
were itself allowed to depend on that value in the reference profile. The
constructed alpha ignores semantic payloads. Deviations remain free to use
their entire actual information; (3) proves that this extra information does
not improve the completion comparison.

## One common sequence and the local gain bound

Let beta_n be a fully mixed consistency witness for the selected source SE,
after any justified vector grouping. Write R_n for the largest nonnegative
source one-step gain under its Bayesian assessment. Since the source game
is finite, R_n tends to zero.

Choose epsilon_n tending to zero and 0<eta_n<epsilon_n. Throughout the proper
pre-exclusion game use the single joint timing equilibrium just constructed.
When it sends a commitment, sample its semantic action from beta_n at the
actual source information set. Use the truthful fixed opening at a resolve.
All pure proper responses have positive probability. The same kernels are
used at every private copy of the same operational/source information.

After the first public exclusion, fix the pre-exclusion profile and choose
a joint tremble-constrained agent equilibrium for all remaining actual
information sets, with floors xi_n tending to zero. This is one completion
under the actual induced prior, not an independently optimized policy in
each hidden state. Public, permanent exclusion separates these sites from
the pre-exclusion sites. Positive-reach cancellation gives local regret at
most B times the total local floor mass. No choice of handler equilibrium
is assumed to ignore old timing records.

At a pre-exclusion site, replacing the foreign current-window completion by
certainty changes any bounded continuation value by at most B times (2).
This remains true for a focal pure alternative. At a fresh later window,
failure under the prescribed profile requires a protected-cutoff miss;
a finite union bound supplies at most H epsilon_n for all later windows,
where H bounds their required entries. This is a conditional future bound
and does not divide by the reach probability of the current site.

On the remaining branch, all other entries complete, the controller follows
the original source semantics, and the only current operational risk is the
focal player's own completion. Its failure gives F_i. Therefore, up to an
error bounded uniformly by

    E_n = B [C epsilon_n/(1-epsilon_n)^M + (M+H) epsilon_n],     (4)

the value of a source action a and operational alternative b at a binding
site is

    F_i + q_b E[u_i(X,a)-F_i | J].                              (5)

Here q_b is the actual auxiliary-game completion probability after the
current alternative and its prescribed continuation. It is independent of
a and the hidden source state conditional on J. WAIT uses the eventual
beta_n source choice; because no new source information arrives in this
binding window, that has the same mixed source surplus as an immediate
reference SEND.

Let g_a be the surplus in (5), and let g_n be its beta_n average. They lie
in [0,B]. If q_n is the prescribed completion probability, then

    q_b g_a - q_n g_n
      = q_b(g_a-g_n) + (q_b-q_n)g_n
      <= R_n + B epsilon_n.                                   (6)

The same comparison at a resolve has no new semantic action, so only the
second term is needed. Equation (3) justifies it even after private receipt
of another player's opening. Mixed alternatives follow by averaging.
Restoring the two continuation errors gives the uniform bound

    actual pure one-step gain <= R_n + B epsilon_n + 2 E_n.     (7)

Together with the post-exclusion floor error, this tends to zero everywhere
on one fully mixed sequence. Finiteness supplies one subsequence on which
strategies and their Bayesian beliefs converge simultaneously. Perfect
recall and vanishing local one-step gains make its limit a sequential
equilibrium of this proper-entry game.

On the event that every required entry is sent by its protected cutoff, all
proper windows succeed
and the source terminal law is exactly the beta_n law. Its complement has
probability at most the finite total number of required entries times
epsilon_n. Consequently the limiting equilibrium preserves the joint law
of initial source parameters, public source results and base utilities.
There is no exclusion on that limiting law. Operational transcripts need
not have the same law as a source game which has no such transcripts.

## What the construction establishes

For the specified finite service, phase grouping and proper-entry menus,
every selected source SE has an actual-private-information SE with the same
initialized source outcome and base-utility law. The proof includes a joint
timing-policy producer, a conditional foreign-delay bound at off-path native
information sets, arbitrary joint completion after public exclusion, and
one common positive consistency sequence.

It is not a theorem that every bounded-inclusion builder has this property.
The substantive service specialization is the support needed to hide an early
entry until the last protected block, together with capacity which makes that
support feasible. The specialization is asynchronous and permits partial
batches; it is still a real restriction on network/service behavior. Likewise,
arbitrary content-dependent private observation rules are outside (3).

The theorem in this note includes observable exact retransmissions of known
canonical entries, including forwarding by another broadcaster. Its scope excludes
unusable commitment preparations, conflicting first bodies, noncanonical
encodings, raw evidence requests or retransmissions that change the inclusion
jobs or consume another entry's reserved service. Those need the counted-menu
repair and authenticated restriction-extension arguments. An immutable
body-level service protects existing proper admissions against later raw
traffic; physical retransmission still needs either genuine service
deduplication or its own comparison. The independent
[audit construction](se-asynchronous-authenticated-construction.md) states
those comparisons and their boundaries explicitly. The combined theorem
uses that separate argument; a proper-entry timing theorem alone would not
establish an arbitrary raw-channel SE.

If that extension adds nonnegative audit charges, the exact own-failure
identity used in (5) concerns base utility only. In a fully mixed audited
handler an already excluded player may still make a charged mistake. At a
clean handler entry, quiet continuation obtains F_i, and any raw continuation
has net utility at most F_i. If all later own local regrets are at most
B xi_n and at most H_h own decisions remain, the finite continuation-deviation
telescope gives

    F_i - H_h B xi_n <= reference net value <= F_i.

Thus an audited composition adds H_h B xi_n to the relevant value error,
rather than replacing its finite-index net value by F_i exactly. The clean
quiet comparator must be legal, and its retained prefix must not already
owe a charge. A hidden-invalid-candidate comparison may also need the
stronger bound that every retained comparator continuation has base value
at least F_i; the proper-core proof above did not assume that for survivors.

## A simpler stronger service specialization

For comparison, one can assign a hidden delay D_e in [1,Delta] to each physical
slot and record its first admission at a+D_e. Reuse the same D_e when coupling
two possible admission times. Earlier admission then finishes no later
pathwise. With independent per-owner service, fixed endpoints and fresh
future service, focal timing does not change a foreign failure set.

That model admits direct pathwise timing comparisons. It is stronger than
the partial-batch construction above and stronger than bounded inclusion.
Ordinary FIFO does not imply it: an earlier focal insertion can delay another
entry, and a service's realized delay can depend on its admission time.
The main proof deliberately avoids relying on this isolation model.
