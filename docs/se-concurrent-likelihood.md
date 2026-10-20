# Concurrent initialized likelihood

This is a paper-level derivation of the qualified initialized likelihood and
causal payoff comparison, independently reviewed by agents in
[the likelihood review](se-concurrent-likelihood-review.md) and
[the replay analysis](se-concurrent-replay-analysis.md), with a root-agent
model audit. These are not human reviews or Lean verification. Its Lean theorem
is **not proved**, and concurrent SE preservation is not claimed here.
The preservation target remains the actual concurrent raw game with arbitrary
finite-support correlated initial inputs, finite binding types, the original
reserved tape mixture, and the joint initial-state, terminal-state,
public-result and realized-payoff law.

## Actual probabilities and the initialization issue

Fix the focal owner i, one positive native binding information set I, the finite
source table D, positive source omission/delivery/bad rates, and native reference
rates, with the construction's strict rate bounds between zero and one.
D has its fullValues property: every legal domain
atom is positive, supplied by its positive domain floor. Native waiting, slot
and bad rates are positive too. These finite-index construction properties
make the real ReferencePolicy class support complete, so its uniform fallback
is inactive. An arbitrary table with zero legal atoms would not justify the
reference-policy D factors below. Full I includes every focal raw action and
its before-view. Work first
with counted responses; the raw alias and audit extensions are separate.
The typed comparison below is the ready, UNSENT case with neither saved own
debt nor current own debt. These are the actual observable case classifiers,
not new model assumptions. In particular noCurrent rules out every unresolved
earlier own BAD, not just the selected row. An all-TRUE binding receipt word
alone does not rule out BAD. Own debt has the separate floor/reset comparison;
accepted BAD in an earlier canceled attempt is still allowed here.
No separate all-history sameExcluded premise is imposed. The entry exclusion
set is reconstructed from the public retired-failure union and rank-truncated
failures before the saved block rank; current E is public. If these differ,
the current attempt already has a new miss, so the all-entry-active-TRUE gate
below is impossible and the pointwise forced-reset comparison applies. In
particular positive beta derives no new current exclusion; it is not inferred
from an unexplained chosen source witness. Equality of those two public
readouts, when needed, is a property of I itself.

Write theta for the COMPLETE initial source state and mu(theta) for its original
atom. Let t be the original reserved tape, sampled once from one unconditional
joint prior pi independently of theta for the whole execution. Coordinates may
be correlated across owners and time. No new block or observed public prefix
selects a replacement prior; public-prefix-adaptive block laws are not covered.
The scheduler posterior conditions this same prior on environment recall.
Conditioning on t is only a calculation: t is not revealed to players.
For an actual finite native path h from theta, its unnormalized tagged weight is

    w_N(theta,t,h) = mu(theta) pi(t)
                    * product_callbacks q_j(past_j,view_j)(raw_action)
                    * product_environment p_t(actual_primitive_successor).

Here q is the actual reference policy, including class splitting over its
actual local raw preimages. The last product is the original realized service
kernel: command selection, pending observation, public samples and deterministic
include/expiry/restore transitions. Impossible native paths have weight zero.
Summing t gives the original implementation scheduler law, not a new fixed-tape
game. At a decision antichain the sum over first hits of I is the actual reach
of I; terminal nonhits contribute zero to that occupation measure.

For an enriched source history g write s(g) for its actual initialized reach.
Let O_i(g) be its ENTIRE focal own-reach product, including accepted canceled
BAD actions and all actual earlier source information. Let D_-(g) be the
product of foreign nonmissing proper binding atoms at their ORIGINAL full
normalized source keys. Let R_-(g) be the product of the individual conditional
foreign publication-cause atoms described below. The actual source trace
factorization is

    s(g) = mu(theta(g)) P(g) O_i(g) C_-(g) D_-(g) R_-(g).             (1)

Initialization is excluded from P. On the regular foreign-good slice, full
source information J fixes P(g) and C_-(g). Public Nature reads only public
source cells; J retains their ordered outcomes and controls. Completed guards
read public cells and published results, never hidden private inputs or raw
commitments. Thus write f(J)=P(g)C_-(g), keeping mu literal. Source perfect recall
also makes O_i(g) a function O_i(J) of the full J. This statement concerns full
information, not merely the smaller normalized action-pool key.
Historical focal lookups after an accepted BAD need not equal the raw source
lookups: N_i(I) and O_i(J) are separately fixed products, not identified.
The foreign getter argument uses foreign-good; only the current clean focal
site needs the typed native/source lookup identification.

For example, even if theta_1=theta_2 almost surely, every comparison at literal
theta retains the SAME mu(theta). Foreign lost-value summation is performed
conditional on theta. It does not replace mu by a product of marginal priors.
Subsequent finite sums preserve that original joint law. Independence of the
initial private cells is therefore unnecessary for (1), the local calculations
below, and the conditional source word argument. It would not prove the missing
initialized coverage theorem either. No independent-private-input hypothesis is needed for the
[preservation contract](../Vegas/Game/ConcurrentRawSequentialPreservation.lean).

## A source-only conditional independence that does hold

Fix the literal full g at a COMMIT row and the remaining static commitment
window, of length k. This fixes theta, old source histories, registry, archive,
exclusions E, generation and saved control. Under the original zero-flag table
q0, an inherited excluded owner's row is automatic NONE; an active row draws
a proper nonmissing value. There is no new omission or BAD in this window.

At static row r, the full information of its owner j is a deterministic
function of g, r and j's preceding ordinary draws in this window. Proof is by
source syntax: a foreign COMMIT adds neither a visible private cell, an owned
action, a public value nor a revelation to j. The appended registry code and
references are static. Cursor positions and E are fixed by the same static
prefix, independently of the proper values. Hence all intermediate observed
signals and own actions, not only the current store view, agree when j's own
preceding draws agree. Applying the deterministic normalized-query map preserves
that equality, including the old archive and canceled history retained by g.

Realize each owner's successive behavioral draws by its own independent finite
random innovations. The preceding locality statement shows that each owner's
whole chain is a function only of those innovations and fixed g. Thus these
chains are independent CONDITIONAL ON g. This is a process construction proof;
it is not independence of the posterior initial types or of arbitrary histories.
The last close may save, retry or exhaust according to the existing failure
mask. Its decision is independent of the new proper meanings. The chronological
attempt word is retained even if the endpoint restores an old store.

Let F be the word masking focal coordinates to NONE, retaining their rows and
all automatic NONE rows. Its law H_g is exactly the original q0 continuation
from g followed by this readout. It is the product of the foreign owner-chain
marginals. Inserting an arbitrary current typed focal value v resamples that
owner's remaining chain at its updated own queries; it leaves H_g unchanged.
After advancing one row, the original F is NONE-head :: residual-F, not the
shorter residual word. No baseline sampled focal future is conditioned on v.

This proves a SOURCE word fact. It does not make an arbitrary g an actual
native cursor or identify the native posterior over g.

## Local source and physical row factors

The following equalities explain the candidate likelihood calculation. They
retain zero atoms and are not by themselves an initialized replay theorem.

* **Foreign proper SEND.** At a genuine ready, UNSENT callback, after summing
  raw aliases of one actual proper class, the atom at fresh serial a and value
  v is B_m(a)(1-b_N)D_j(K,v). Here B_m includes waiting and the actual
  uniform/canonical fresh-slot mixture. The eligible slots depend on prior
  signed headers, not hidden slot meanings. For a retained target occurrence
  the literal namespace/rank and actual getter must identify K with that
  source occurrence's key. If R_before is the outstanding target product,

      D_j(K,v) R_after = R_before.

  There is no division by D. Incompatible values have zero target-lock score.
  The factual getter identification is needed only for an active retained
  nonmissing target, not for an already excluded or missing source row.
* **Finished lost foreign SEND.** A never-admitted declaration can be summed
  only after showing no accepted cell, proposal or later same-owner action
  uses its meaning. Owned readiness and permanent exclusion make it the last
  such active leaf. On THAT entire lost continuation slice its value sum is

      sum_v B_m(a)(1-b_N)D_j(K_native,v) = B_m(a)(1-b_N).

  An actual SOME native getter exists at the ready callback; its key need not
  match an inactive target. A pending current value is a lock, not a lost
  leaf. Accepted canceled values stay indexed by their original generation.
  A nonmissing source failure has domain factor one but STILL imposes a
  failure lookup lock; a proper typed SEND against it has score zero.

The focal pre-I raw probability is N_i(I); its source counterpart is O_i(J).
Both retain WAIT and canceled BAD. Earlier consumed focal publications at this
surviving BIND site must all be truthful successes: their failure would exclude
permanently without rollback. Opening/service/sample/restore legality and mass
are derived in the primitive recursion below; they are not inferred merely
from this scalar cancellation.

For an active regular foreign publication with stored v the source causes have weights
T=1-o (truthful), F=o*d (failed disclosure), W=o*(1-d) (no proposal). The
observable class and its normalizer are

| Observed actual source row | Allowed causes | Class mass |
| --- | --- | --- |
| No proposal, public failure | W | o*(1-d) |
| Proposal v, public success | T, accepting guard | 1-o |
| Proposal v, public failure, accepting completed guard | F | o*d |
| Proposal v, public failure, rejecting completed guard | T or F | (1-o)+o*d |

Each allowed cause l keeps its individual conditional atom r_l=w_l/C.
Accept/reject means the conjunction of obligations completedBy THIS reveal;
an empty conjunction accepts. Obligations still pending are not evaluated or
replaced by their eventual verdict. For a completed
obligation all subject/input publications are available, so actual public
registry/revelations and v determine its verdict. Physical receipt bits are
not the statistical source causes. A source-label annotation must draw r_l,
and must prove this conditional fiber positive on every retained regular
parent. Commitment/Nature rows keep their literal joint/result and have no
such ambiguous publication-label mixture.
An inherited excluded owner's automatic publication is deterministic NONE
with class mass one; the table is not applied to that row.

## Qualified initialized likelihood

The needed initialized identity is the following qualified coverage and
weighting statement about the ACTUAL process. Its construction below supplies
the global step that conditional source laws alone do not give.

Use the original posterior of native histories/tapes at I, conditioned on no
foreign generated BAD. Run a literal legal typed current SEND, then the existing
unflagged BASE/prompt continuation. This is the actual unflagged policy, not
ReferencePolicy instantiated at zero rates (which could select its fallback).
Let beta be the physical event that the
commitment block's ENTRY-ACTIVE rows are all admitted (the all-TRUE binding
gate; inherited excluded rows are automatic), on the
same tape and source-neutral future timing/slot coins. It is not guard acceptance
or successful publication. A typed current insertion changes the focal owned
future causally; it must not redraw past source coordinates or condition a
baseline complete G. All legal proper current encodings must share the same
gate experiment, or an explicitly justified equivalent gate coupling.

The desired result must CONSTRUCT an auxiliary X=(g,F) on this actual qualified
experiment. It retains theta, the complete enriched source past/archive and
the actual remaining foreign word. Its continuation after v must be the actual
causal q0 payoff kernel Phi_v(g,F), on the SAME selected source/graph joint.
If the qualified mass is positive, it must also construct one genuine full J
from I. Let nu_J be actual source Bayes reach on foreign-good g at that J,
followed by H_g(F). The minimum likelihood identity needed for clean gains is

    Q_I^v(beta=1, X=x) = t(I) nu_J(x)       for EVERY x and typed v,             (2)

with ONE t(I)=Q_I^v(beta=1), independent of v and its legal proper encoding.
The sum includes all actual native raw preimages and the ORIGINAL hidden tape
posterior. Neither nu_J nor a matching cursor may be supplied as a hypothesis
for arbitrary targets x. If t(I)=0, no source correspondence is required for
that branch. Zero source atoms must have zero left side. If t(I)>0, every
positive nu_J atom must have actual qualified preimages with exactly (2)'s
weight. This is aggregate qualified coverage, not coverage for every mechanical
record.

### Finite chronological reconstruction

Work after the exact foreign-alias projection: only foreign syntax is
normalized; focal raw actions, focal full information and the initialized law
are retained. Its history marginal already sums the original local preimages,
so an inverse for each evidence-request spelling is unnecessary.

A skeleton records the original tape/commands, clock and callback order,
namespaces, signed headers and fresh serials, emitted envelopes with opaque
binding meanings erased, receipts, current/saved/retired accepted HANDLE
tables, and all public samples and proposed opening plaintexts. Up to I it also
retains focal raw actions and before-views. AFTER I only mechanical headers/times
are fixed: focal future values/views are causal chain auxiliaries, not a retained
baseline sample. It does not erase a binding handle or
confuse its original generation with a later occurrence of the same event.
STOP the skeleton at the CURRENT commitment block's first close, when beta is
decided, before any subsequent publication or sample. Historical publications
and samples before I are included; future ones are NOT. This stopping scope is
essential: future plaintexts/sample paths can depend on inserted v and F.
The skeleton set is DEFINED as projections of actual positive qualified
normalized paths, before selecting a source target. It is not defined by
target-relative compatibility. Reconstruction below must work for every
regular source target at the J obtained from such a path.

The source mask is recoverable from FULL J, not just its final E:

| COMMIT owner j at the recorded rank | Actual source row |
| --- | --- |
| j in E_before | automatic NONE |
| j not in E_before, j in E_after | missing |
| j not in E_after | nonmissing |

Every source signal retains the rank and E, so adjacent signals give this
table. The source COMMIT transition immediately inserts exactly a missing
active owner. close_excluded retains that insertion at the last row even if
the same transition restores, increments generation or exhausts. Regularity
makes a nonmissing foreign row proper; the focal labeled word fixes its BAD
or proper result. Thus differing first-miss positions cannot hide in the same
full J. A normalized action-pool key would not establish this fact.

If the qualified measure is zero there is nothing to construct. Otherwise fix
ONE actual positive qualified path. Replay its source instructions in static
order, retaining the original input and public samples, each admitted binding
meaning (including canceled focal BAD), each miss and restored checkpoint,
and the complete proposal archive. Supply not-yet-emitted current binding
coordinates by their original owner chains. Earlier blocks have closed: their
decoded masks and words are literal. The current block has all admissions TRUE
on this path, so its added ordinary coordinates are nonmissing proper values.
At publication choose an allowed T/F/W label from the displayed table. This
constructs a genuine source prefix at the selected focal static rank; call its
full focal information J. Positive ordinary support supplies its unobserved
coordinates, so J has positive regular source reach with that original input.
The current block's prefix has E=entryE: all current admissions on this
qualified path are TRUE, and new proper ordinary choices add no exclusion.
Full J retains E at both the matching saved entry and the selected rank.
Every other target at this J therefore has the SAME E=entryE; it is derived
from the qualified construction, not an extra target-cursor hypothesis.

J is independent of these choices. Its initial focal observation is fixed by
I. Its entire public word is fixed by the public address/record scan and the
archive. Its entire owned coordinate word is fixed by focal raw preparations,
accepted receipts and retired attempt masks in I. A surviving focal owner has
no consumed missing binding or failed publication. Unobserved foreign private
coordinates affect none of these components. Full source information is fixed
by this initial observation/public-word/owned-word data. In particular its
focal source observation agrees at EVERY earlier static position, not just at
the selected row. This uses full recall, not a normalized action-pool key.
There is no unobserved historical focal choice canceled by an early foreign
miss: settle tests Finished for EVERY phase event only after drain, and drain
can complete an automatic event only for an already excluded owner. By
drainFuel_completed_survivor an unsubmitted surviving focal event remains
unfinished. It must be physically admitted or expire before retry; expiry
excludes the focal owner permanently. At this later active I, therefore,
every historical focal commitment was actually admitted, even when canceled.

For a target (g,F), associate values with SOURCE OCCURRENCES, not physical
times. The occurrence is (generation, saved rank, static event rank). Give
every accepted historical handle its target occurrence's value, and each
current emitted handle its coordinate in the target current block word.
Restore a persistent handle with its original occurrence's SAME value.
Unsubmitted coordinates are auxiliary ordinary draws. A finished lost
declaration has its own unconstrained draw, not the value of a later event.
Focal future values after the literal current insertion are newly sampled
from the original table at updated focal queries.

The reconstruction retains the following state invariant at EVERY actual
primitive transition, including before a foreign callback after restore:

1. Cut, clocks, accepted handles, signed-header occupancy, failure masks and
   selected checkpoint/generation are the skeleton's literal data.
2. Current and saved graph cells, separately, have the target source meanings
   at their respective source occurrences. Initial cells use the target
   theta. Retired cells retain the attempted meanings before restore. Dead
   catalogue entries are not identified with current/saved cells.
3. All source-public values, ordered numeric source addresses and proposal
   archive agree with the target public word. The focal initial observation,
   complete owned coordinate word and current/saved own observations agree;
   hence its full source observation at every earlier source position agrees.
   The WHOLE focal private catalogue also agrees: initial own entries are fixed
   by its initial observation in J, its registrations are the literal raw
   actions in I, and foreign registration changes only the foreign catalogue.
   This includes dead/unused focal preparations. Together with the same network
   and receipt record this gives every literal focal raw before-view.
4. A foreign callback's actual normalized getter is the target owner's
   normalized source getter at that occurrence, even if foreign private
   events have been interleaved differently.

Item 4 follows component by component from items 1--3, rather than from equal
complete latent histories. The native query is literally

    (Erase(NoMiss(ErasedRead(typedView, controls, addressWord))), Z).

typedView reads the actor's original own inputs, currently live own binding
cells and public cells at the selected static rank; item 2 supplies them.
Unrelated foreign private cells are absent. controls consists of the inherited
failure footprint plus failures STRICTLY BEFORE THE SAVED BLOCK RANK low,
generation and low. Its E is entryE, not the current total exclusion set.
addressWord scans old/retired footprints; its current range uses the CONSTANT
(entryE,generation,low) at every intermediate rank. Items 1 and 3 supply
its ENTIRE list. Z is the complete typed address-keyed submitted-proposal
archive (a finite set), from item 3. The full source public chronology is
retained separately; Z alone does not assert a physical arrival order.
Erase discards recalled private action tags. NoMiss applies the same explicit
normalization to both readouts. In particular no canceled private value is
reintroduced after restore. For restore, item 2 copies the target SAVED cells,
not the pre-restore current cells; masks/generation and retained address/archive
are updated by the same source restore rule. This accounts for every argument
of the getter, without requiring equality of latent trace labels.
The footprint cutoff here is the SAVED BLOCK RANK, not the queried event rank.
For example, in an old failed attempt, static-earlier foreign j' can miss while
static-later j physically SENDs BEFORE j' expires. At j's source row the source
already sees j' excluded; at the earlier physical callback the runtime does
not. NoMiss resets EVERY exclusion signal from the current attempt's entry
cut onward, including its own-play tags, to entryE. The subsequent Erase drops
past private observations and action tags. Foreign binding failure is hidden
from j's current typed view, and no publication occurs inside the commitment
block. Hence the normalized getters still agree. This is not justified by
truncating only currently known failures. Old RETIRED attempt words lie before
the cut, remain unchanged, and agree from the already closed mask/archive.

Propagate the invariant by the ACTUAL primitive transition:

* Initialization encodes the target theta in both current and saved stores.
  Public and focal projections agree by J; foreign private components may
  differ. Initial accepted handles are the fixed input identities.
* At a proper foreign binding callback, getter equality gives D at the target
  coordinate. Freshness uses the same signed headers/handles. Canonical
  preparation is legal at that serial and changes only the foreign catalogue
  at its new slot. The opaque envelope is unchanged. A lost declaration uses
  its own original D draw. Focal callbacks keep the literal raw action and
  entire catalogue. WAIT/SENT/disabled cases register no new value/envelope.
  Token/readiness and response class use the retained cut/header data.
* Binding INCLUDE tests the same namespace, owner, token, clock, vacancy and
  unused handle, not the binding meaning. Its accepted handle, receipt and
  completion cut agree; its store write uses the assigned target value.
  Expiry writes failure at the same coordinate. Both refresh the same
  event-relative activation clocks.
* At opening, source legality equates the proposed value in Z with the stored
  target value. A generated handle was registered immutably at its original
  occurrence; an initial handle has the target theta value. The canonical
  evidence request therefore materializes an ACTUAL accepted-handle
  certificate. Its plaintext/envelope match the skeleton. No equality of
  foreign whole catalogues is needed.
* Opening INCLUDE evaluates exactly the obligations completed by that reveal.
  Their subject/input publications agree by item 3, hence the actual check
  conjunction and output agree. Pending obligations are not evaluated early.
  Failed inclusion or expiry inserts the owner into E BEFORE normalization.
  Same-owner reveal dependencies prevent a later own proposal from already
  being ready/pending; excluded rows then drain as automatic NONE. Thus archive,
  result and later opportunities agree even at the first publication failure.
* Public Nature uses the same public operands and actual sampled value; its
  atom is retained, and the full public word fixes its intrinsic product.
  ACTIVATE, WAIT and clock commands see the same public readiness/time data.
* Clean save copies the assigned CURRENT store and accepted table to saved.
  Retry retains the pre-restore word in its retired generation, then copies
  the assigned SAVED store/table to current. This literal field copy preserves
  item 2 without identifying independently chosen checkpoints. The mask table
  determines the matching source close/generation. Private catalogues persist;
  fresh slots cannot overwrite a prior signed occurrence. Old public sample,
  proposal and numeric address data are retained.

Each case preserves the listed fields and the next literal focal before-view.
For a historical publication callback, the physical interleaving may already
expose a rank-later public result. Its value is in the complete public word of
J; the skeleton's actual completion/arrival order determines whether it is in
that before-view. Equality is not inferred from only a same-rank source prefix.
Consequently targets with different foreign meanings give actual normalized
paths at the same skeleton. This derives legality from the primitive tests,
rather than from equal residual scores.

For the inverse retain lost draws and future focal draws as auxiliary
coordinates until summation. Source owner order makes emitted coordinates an
initial OWNED prefix: no later own SEND is ready before an unresolved owned
predecessor. If that prefix is v_1,...,v_l, its actual value factor is
the product of D_jk(v_<k) for k<=l. Sample the unobserved tail with factors
D_jk(v_<k) for k>l. Their product is the FULL owner-chain law, with no extra
normalizer. This remains true under adaptive physical interleaving, since the
next queried coordinate has exactly that conditional law. Thus ordinary chains
may equivalently be sampled at entry. Unused continuations sum to one.

The augmented normalized path determines its skeleton, theta, historical source
word and all current chains by inspection. Conversely the primitive recursion
reconstructs that path from those coordinates. This is a bijection BEFORE
forgetting lost draws and focal future draws, not on bare (g,F,m). The exact
alias marginal and conditional-chain sums forget the extra coordinates with
their actual weights. Every original preparation belongs to an accepted
occurrence, a retained current prefix or a finished lost leaf. A lost leaf
has no later own binding choice because its predecessor did not complete;
its eventual miss excludes the owner. The publication barrier prevents an
intervening new value choice. Its actual D therefore sums to one; its native
bad-rate complement remains. Accepted canceled prefixes stay in g. Auxiliary
publication labels have exactly their displayed r_l law. This accounts for
every original preimage and its multiplicity.

The resulting unnormalized weight is

    mu(theta) P(J) N_i(I) A_I(m) D_-(g,F) R_-(g),

where A_I(m) contains all physical timing/slot/service and retained bad-rate
complements, including complements of integrated lost preparations. The source
weight is mu(theta)P(J)O_i(J)C_-(J)D_-(g,F)R_-(g). Multiply the local factors:
every accepted foreign value contributes exactly one D; a lost value sums to
one; each ambiguous source label contributes one r_l. Timing/slot/admission
tests use value-blind fields, and opening/public-data coefficients are fixed
by J. Therefore A_I(m) is independent of target g,F. The current all-TRUE gate
also ignores inserted typed meaning: it tests binding admission, not later
guard success. Future focal values are resampled after v and sum to one.

At a fixed proper serial, changing v keeps the opaque packet unchanged.
For different legal fresh serials a and b, fix old occupied handles, send a
to b, and pair the kth remaining fresh serial after a with the kth remaining
fresh serial after b. This order-rank bijection, unlike an arbitrary permutation,
pairs each subsequent least-fresh canonical choice. Initial handles are fixed.
Retain event, message ID, token and time.
Reserved service eligibility uses pending coordinate/order, not serial meaning;
vacancy and HandleUnused are unchanged under this injective renaming. Thus
admission/completion times and the all-TRUE gate agree. This naming argument
is distinct from fixing headers while retargeting a value.

Sum the product identity over skeletons with the gate and over the ORIGINAL
tape prior. Its common coefficient cancels when normalizing: the source sum
is actual regular source reach of J; the native sum is actual qualified gate
mass. This yields (2) with t its actual probability. Zero prior, incompatible
path/lock or disallowed-cause atoms stay zero in the product identity; no
individual D atom is divided out. Legal D atoms in this actual finite-index
construction are positive by the stated domain floor.
For positive t the construction explicitly gives preimages of every positive
source target. At zero t every qualified mass is zero.

This gives the paper-level initialized identity. It supplies current/saved
meanings by construction rather than assuming a target cursor. The existing
conditional cursor law can then identify Phi on this SAME completed word/joint;
commit-window history uniqueness retains the full source history. An advanced
after-v cursor is not treated as a fresh whole block.
Specifically, first take the actual full source prefix at the CURRENT BLOCK'S
FRESH ENTRY inside the target g. The fieldwise reconstruction produces the
retargeted native entry configuration with those same typed cells and source
references. Instantiate the chosen source/graph block joint there, retaining
that original full source prefix (not a decoded replacement history). Deferred
owner-chain sampling and the actual emitted-prefix cylinder give its SAME
conditional completion. At the selected source rank insert the literal v,
use the actual advanced cursor for only the residual suffix, and resample its
focal future at the updated original queries. Foreign F is unchanged, with the
required NONE head/tail bookkeeping. Commit-window history uniqueness lifts
the complete semantic word to the literal enriched source G. The actual clean
closing/terminal comparison applies to that same G, giving Phi_v. This never
conditions a previously sampled baseline focal future on v, nor asserts
fresh-entry geometry for an advanced cursor.
After the binding stop, apply the existing actual fresh terminal coupling
separately for EACH supported residual tape and this constructed source state.
Protected prompt q0 continuation has the same source terminal payoff law on
each such tape. Hence integrating the original conditional tape posterior
gives Phi_v. This is a per-tape law calculation, not independence of the
residual tape from the source state. No future Nature mass is silently omitted
from a path factor: all postclose randomness is inside that continuation law.

## Signed gain and quantitative errors

For a literal current lottery r let p be its proper-typed mass and L its typed
pushforward; use identity/source baseline on the complementary source mass.
Let Delta_v(x) be the signed causal payoff difference Phi_v(x)-Phi_D(x).
From (2), finite linearity gives exactly

    sum_v r_TYPED(v) E[beta Delta_v(X) | I,native-good]
      = p*t(I) E_{x~nu_J}[Phi_L(x)-Phi_D(x)].                              (3)

Let q=P(native-good | I). Returning to the ORIGINAL native posterior multiplies
the right side of (3) by q; q cannot be discarded for a signed gain.
The unqualified current branches have their separate pointwise floor/reset
comparison. BAD never receives the typed Phi attachment. Thus they do not
require an unweighted posterior theorem. Foreign-bad posterior bounds and
future flag bounds add their bounded-payoff errors. With absolute payoff bound B,
the native-bad contribution is at most 2B(1-q). Removing source-good conditioning
costs at most 4Bs, where s is the source-bad posterior at J: the signed regret
lies in [-2B,2B], and q*p*t is at most one. The source comparison is
applied to the LEGAL lottery (1-q*p*t)D+q*p*t*L, chosen at J from the current
observable native lottery; it does not observe hidden g or F. No sign of the
source gain is assumed or discarded. At q*p*t=0 the comparison is the baseline
ordinary lottery; one can use the ACTUAL source identity deviation and the
error-only branch. D is the ordinary baseline, not exactly the fully perturbed
prescribed current law. At t=0 (3) is zero without a positive normalizer.
If legal encodings had value-dependent gate weights, replacing them
by their mean would be invalid; that uniformity remains part of (2).

More explicitly, let e_N be the available bound on the native current/future
flag error in a gain comparison. Let e_S bound TV between each ordinary
source payoff experiment and its actual prescribed-source counterpart,
including any current flag change. Then for the ordinary legal lottery lambda
just constructed,

    nativeGain(I,r) <= sourceGain(J,lambda)
                       + 2B(1-q) + 4Bs + e_N + 4B e_S.

The term sourceGain is SIGNED. No nonnegativity premise is used. One may bound
it above by the actual source assessment's local regret. For uniform one-step
source flag bound a_S and remaining horizon H_S, the elementary coupled union
bound gives e_S <= H_S*a_S. The existing native bound gives
e_N <= 2B*(2*card(Player)*(2*H_N+1)+1)*nativeFlagBound. These are finite-index
error bounds; their vanishing is supplied by the shared constructed sequence,
not by conditioning on an unknown limiting reach. If q=0 or the qualified
gate has zero mass, the corresponding typed contribution is zero and no J
normalizer is required.

The mathematical argument uses aggregate qualified coverage, not a terminal
product law for every mechanical record. Lean must still establish this
initialized reconstruction/weight identity and connect its actual causal
completion to the local comparison. Existing conditional results do not by
themselves check those interfaces. Final consistency/limit/raw-audit assembly
and the full preservation theorem remain unproved. No Lean proof authoring,
reader or build is part of this mathematical review.
