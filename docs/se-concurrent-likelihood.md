# Concurrent initialized likelihood

This is a proposed derivation of the qualified initialized likelihood and
causal payoff comparison, reviewed by agents in
[the likelihood review](se-concurrent-likelihood-review.md) and
[the replay analysis](se-concurrent-replay-analysis.md), with a root-agent
model audit. The partial-ledger reconstruction and its explicit reach-level
weight identity have passed these mathematical reviews for the frozen
`.concurrent` contract with complete pending observation. These are not human
reviews or Lean verification. Its Lean theorem is
**not proved**, and concurrent SE preservation is not claimed here.
The preservation target remains the actual concurrent raw game with arbitrary
finite-support correlated initial inputs, finite binding types, the original
reserved tape mixture, and the joint initial-state, terminal-state,
public-result and realized-payoff law.

The execution mode is the contract's literal `.concurrent`. The compiled
graph retains `barrierOrder`: different owners' private commitments can
overlap, but each public event waits for every earlier event and every later
event waits for earlier public results. A ready public event therefore has
exactly its source prefix completed. Activations and deliveries are still
asynchronous. The separate `.concurrentReveals` mode is outside this contract;
out-of-order publication reconstruction is not required here. These facts are
the existing `barrierOrder_ready_public_completed_iff` and
`barrierOrder_ready_public_field_iff` laws, not additional hypotheses.

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
of I; terminal nonhits contribute zero to that first-hit measure.

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

This argument concerns the reserved implementation in mode `.concurrent`
under its `Operational` assumptions. In particular, observation is exactly
`completePendingObservation`, and the compiled order is barrier order.
Different-owner bindings can overlap; a public event requires its exact
preceding source prefix complete. No relaxed-reveal extension is asserted.
The original correlated input law and unconditional whole-execution tape
prior are retained. The argument below is mathematical, not a Lean theorem.

First apply the exact foreign raw-history normalization. It sums the original
proper foreign alias fibers while retaining the initializer and full focal
raw recall. Choose the existing source witness fold on this normalized
history and pull its annotation back. No separate witness-equivariance
assumption on raw aliases is needed. The enriched canonical trace is the
actual checkpoint trace lifted with `nativeArchiveLabels` of the submitted
proposal archive, including failed-but-submitted proposals.

#### Exposed prefixes

At physical depth k retain only data already exposed:

- commands, actor, clocks, activation clocks, cuts, receipts, pending order,
  packet addresses, accepted handles, candidate occupancy and submission counts;
- the currently exposed public store and public opening plaintexts;
- the focal raw actions, before-views and entire catalogue before I;
- the closed source past at the installed phase entry, separate current and
  saved typed-state correspondences, and indexed retired attempted words;
- a partial ledger of issued declarations, indexed by full generation,
  phase-low and event, with owner, slot, typed meaning and actual receipt;
- the entire chronological cause-read word and conditional label mass of
  source rows already emitted by the checkpoint fold.

An unresolved declaration is not classified by its eventual admission.
Unissued events have no ledger entry, source action or probability factor.
The source word of a live commitment phase is decoded only when it closes.
For example, if native B acts before statically earlier A has issued anything,
reach to B contains no A-domain atom. A's coordinate may be attached later;
it cannot be inserted into the initializer or an earlier prefix weight.

Full source J fixes the historical per-row masks, not merely final exclusion.
At a binding row with owner j, membership in E_before gives automatic NONE;
otherwise new membership in E_after gives omission; otherwise it is admitted.
The final-row close preserves E even across retry or exhaustion. Historical
focal admitted BAD is retained literally. A surviving focal owner has no
unsubmitted historical commitment synthesized by a foreign retry: phase close
requires every event finished after drain, and an unfinished surviving focal
event must be admitted or expire. Expiry would exclude it permanently.

#### Response and application steps

At a genuine ready UNSENT foreign binding, the eligible slots are exactly
the bounded fresh slots F. This follows from
`phaseBindingSlots_eq_fresh_of_history`; the test has no hidden value guard.
`reactiveFreshSlot_congr` shows that the canonical slot s0 depends on freshness,
not catalogue meanings. With waiting w, BAD rate b and slot rate z, a proper
class with typed value v and slot s has mass

    (1-w)(1-b) [z/|F| + (1-z) 1[s=s0]] D_j(actualKey)(v).

The native getter equals the corresponding owner-chain query componentwise.
Its typed projection reads that owner's original input, saved cells below
saved-low and earlier own live cells. Its controls and ordered address word
use the saved entry exclusions, generation and low; its proposal component
is the actual submitted archive. NoMiss removes EVERY exclusion difference
inside the current attempt, including an earlier-static miss whose physical
expiry happens after this SEND. It does not erase retired attempts.
Same-owner readiness ensures earlier own values needed by this query have
already been exposed. Unissued foreign values do not enter the query.

Registration adds the value to its exact fresh handle without completing the
source row. Acceptance then records that handle at the event and writes the
same typed result. The invariant retains BOTH catalogue lookup=openable(v)
and binding-field value=success(v). Initial handles obtain these facts from
encoding the literal target input. A proposed opening is attached to its
issued occurrence using actual count/certificate and accepted-handle facts,
not an assumption that all reference proposals are truthful.

Public store equality is propagated at each physical completion. In this
mode public readiness gives the complete earlier source prefix. Guard code
is fixed, and `GuardCheck.eval?_publicStore` reads that public store and the
literal proposal. The two handle/value facts above permit opening transport;
equal proposal plaintext alone would not. Public results, exclusion, cuts
and subsequent readiness consequently agree. Nature likewise uses the actual
public distribution operands and keeps its original atom.

Reserved service commands depend on the original tape, command cursor and
pending/public data. Complete-pending observation reveals all pending IDs
deterministically. Future fresh-handle occurrence renaming transports the
emitted packets and their observations. Old focal raw syntax, including an
evidence request mentioning a future-unallocated handle, stays LITERAL.
This argument does not cover an arbitrary handle-sensitive observation rule.

Every focal before-view is preserved inductively. Its public phase/native
views come from the retained public store, cut, accepted handles, clocks,
exclusions and retired records. Its own typed cells come from its original
input and chronological admitted/canceled word fixed by full J. Its entire
private catalogue comes from that input and its literal raw preparations in
I, including wrong-typed BAD preparations. Its network observations and
receipts come from the retained packets and receipt record. Appending the
next literal raw action with this computed view gives the next before-view
in I; final-I equality is not an unexplained successor filter.

#### Close, restore and hidden causes

At commitment close, `decodeCommitAttempt` reads the known masks and accepted
meanings in static order. Per owner, admitted values form an ordinary-chain
prefix. A sent-but-missed proper value is a terminal auxiliary draw: owned
readiness prevents a later own event already being ready, and expiry excludes
its owner permanently. The draw product is therefore

    product_j D_j(admitted prefix) * product_lost D_j(auxiliary | prefix).

Only the lost factors sum to one. Their meanings affect no accepted cell,
proposal or later active own choice; occupancy is retained separately.
Admitted-but-canceled values remain in the chronological source history.
Native restore copies entry config and accepted handles while retaining
catalogue, clock and exclusions, and archives the attempted word. Source
restore copies saved typed state with attempted history. Saved accepted
handles keep their immutable meanings; later fresh slots cannot overwrite
them. Retry changes generation; exhaustion consumes its automatic suffix.

Attach source causes only when their source rows are actually emitted.
At a foreign rejected-guard failure with a submitted proposal, put
u=1-omission, f=omission*delivery and Z=u+f>0. The legal truthful and failed
disclosure rows have source masses u and f and conditional masses u/Z,f/Z.
For the summed normalized native class mass B, including B=0,

    Z sum_h mass(h) K(T) = u B,    Z sum_h mass(h) K(F) = f B.

These are the exact `proposalRecoveryFailureDisclosureLaw_rows` identities.
Keep the previous label prefix on BOTH sides. The conditional fiber is
positive because the retained target row is a supported member. Other
publication classes use their permitted singleton or corresponding rows;
automatic excluded rows have factor one. The existing arbitrary-same-J
source class theorem makes their normalizers J-common. Commitment values
stay literal; latest-read equality alone does not determine the label law.

#### Fixed-choice domain, weights and inverse

Fix one literal proper current choice c encoding v. Let M_c be the finite
image of actual positive qualified normalized paths, retaining their original
tape and the following projection of EVERY native prefix through first close:
remaining fuel, actor, application public view, network public view, receipts,
prepared-slot freshness, environment recall, and focal raw recall truncated
at its pre-I length. This coordinate contains NO source history or witness,
source cause-read word, conditional label weight, foreign private meanings,
or post-I focal private meanings. Those belong to the annotation/invariant,
not to M_c. Retaining the source cause-read word would retain unrevealed foreign
commitment values and invalidate target-independent weights. No common fine
coordinate across different current encodings is required.

For a target g at the resulting J, its initializer and admitted occurrence
values, together with m, leave precisely two kinds of free draws: historical
proper-but-lost foreign values and current post-I causal focal draws. The
former range over their FULL actual conditional D law. Permanent exclusion
makes their meanings irrelevant to all later callbacks, so only these laws
sum to one. Accepted canceled values remain in g. Current focal draws keep
their actual updated-query weights inside the causal payoff kernel.

Reconstruct prefixes using m's commands/slots, literal pre-I focal actions,
the target's admitted values, and those free draws. Immutable registration
links each accepted handle to its meaning; restore copies saved config and
accepted handles while retaining the catalogue. Own issued prefixes determine
foreign queries, without unissued foreign values. Focal before-views follow
from its own input/admitted word fixed by J, raw catalogue/actions fixed by I,
and m's public traffic. They are derived, not extra filters. At close the
static word and deterministic COMMIT steps determine the linked source child;
automatic normalization adds only excluded NONE rows. Deleting the last
native constructor recovers its predecessor and exposed draw. These give the
exhaustive finite pushforward with its actual multiplicities.

The current block's partition is by STATIC focal rank, not exposure time.
Statically later foreign values issued before I belong to the source q0
suffix F. Earlier unissued foreign values enter sourceReach(g) retrospectively
at close. Finite-source reach stops immediately BEFORE forced current v;
there is no D_current(v) factor. F covers only the current binding block.

Write

    rho_J(g,F) = 1[info(g)=J, foreignGood(g)] sourceReach(g) H_g(F),
    Z_J = sum_(g,F) rho_J(g,F),
    Z_N(I) = sum_[h at I] nativeReach(h).

Let O_i(J) and C_-(J) be the checked source focal own-reach and foreign class
factors, ending before the forced current row. Let N_i(I) be the product of
literal native focal pre-I raw response atoms. Define c_N(m) directly as the
original tape atom times native FOREIGN mechanical response factors: WAIT,
proper BIND SEND/slot/BAD-absence coefficients, historical PUB wait/send
coefficients, forced WAIT, and their post-I zero-rate specializations. PUB
has no ordinary-value or preparation draw. Normalized raw alias fibers sum
to one. These factors contain neither private D atoms nor source labels.

For actual annotated reach-level qualified payoff submeasure U_c, the
zero-safe finite product identity is

    (O_i(J) C_-(J)) U_c(g,F,m)
      = N_i(I) c_N(m) rho_J(g,F) Phi_c(g,F).

Literal mu, public Nature atoms and ordinary foreign-chain atoms agree
coordinatewise. K is ALREADY the source conditional fiber factor R; the
source class factor C contains its normalizer. There is no second division
by that normalizer. Hidden cause alternatives have equal erased typed state,
public controls and proposal delta, hence equal later normalized queries and
class transitions. They change annotation weights, never mechanical factors.
Zero target atoms have zero native weight by the same forward/inverse
construction; no target atom, mu or D is divided out.

Phi is identified before averaging. Keep the m-specific terminal kernel until
the endpoint transport identifies it. Preserve the actual causal current-block
suffix after v, including focal draws at UPDATED queries. The shared completed
word from the same old source prefix identifies the selected source extension
by the clean checkpoint word formula and commit-window uniqueness. The exact
archive/lift and fixed-tape fresh-payoff transport then identify the actual
terminal payoff law with this source q0 continuation. Later publication and
Nature remain causal. Only genuinely lost leaves integrate to one; focal
causal tails are pushed forward, never replaced by one. Original tapes are
disintegrated before the comparison, without refreshing a stop-time posterior.

Bayes normalization uses exact history reach weights. Z_N(I) is the native
information-site mass, and native belief assigns nativeReach(h)/Z_N(I).
Conditioning source belief at J on foreign-good gives s(g)/Z_J; the foreign
suffix H has total mass one. No occupation scaling factor enters these
formulas. On the positive branch, full mixing and foreign-good class
positivity give O_i(J) C_-(J)>0. Set

    B_c(m)=N_i(I)c_N(m)/(O_i(J)C_-(J)),
    nu_J=rho_J/Z_J,    A_c(m)=B_c(m)Z_J/Z_N(I),    a_c=sum_m A_c(m).

Then the actual qualified payoff law on `some` is

    a_c sum_(g,F) nu_J(g,F) Phi_c(g,F),

with remaining mass 1-a_c on `none`. The checked actual admission-word symmetry
makes a_c common across all proper current values and encodings, after this
aggregation. Full source information uniqueness fixes the same J from I.
It does not require a common fine M_c. Positive qualification supplies Z_J>0;
otherwise every proper qualified law is pure `none`, with no source site
needed. Write a for this common mass. It uses the original native posterior, including the foreign-good
gate. If (2) first conditions on foreign-good with probability q>0, then
a=q*t(I); these are two normalizations of the same measure. This proves the
common-a qualified identity and its causal payoff
attachment at the stated mathematical scope. It does not assert a checked
Lean transport theorem or the final preservation theorem.

The sufficient aggregate Lean obligation has a simpler form. Let Ubar_c(z)
be the actual native reach-weighted stopped/terminal payoff submeasure,
filtered by foreign-good and the original first-close admission gate. Let
T_c be its total mass. Let S_J be the foreign-good source reach at J, and
V_J,c(z) that same reach followed by the genuine zero-flag causal insertion
and terminal continuation. The required zero-safe identity is

    S_J Ubar_c(z) = T_c V_J,c(z).

The positive branch must also establish S_J>0, one source J and faithful typed
encoding chosen before all current choices and utilities, the native/source
query equality, the exact source-zero D pushforward, and one common T_c across
proper encodings. Then a=T_c/Z_N(I); the zero branch gives pure `none`.
This aggregate statement is sufficient for `QualifiedBindingLaw`. Its global
weighted reconstruction remains unproved in Lean.

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
