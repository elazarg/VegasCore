# Two small asynchronous-service calculations

These calculations support the [generalization plan](se-schedule-generalization.md):
one restricted finite-tree SE and a conditional publication bound, not full-raw preservation.

## A. Resolution followed by a guess

Alice privately knows H (probability 1/4) or L (3/4). Both owners have constant
TRUE context binding candidates, with no prior signed binding envelope. Alice
publishes T or F; Bob observes it and guesses H or L. Alice's base payoff is:

| Type / publication | Bob H | Bob L |
| --- | ---: | ---: |
| H / T | 2 | 2 |
| H / F | 0 | 0 |
| L / T | 2 | 1/2 |
| L / F | 0 | 1 |

Bob receives 1 iff correct. The source assessment plays T at both types, L after
T and H after F. F trembles t at H and t² at L give H posteriors tending to 1/4
after T and 1 after F; positive Bob trembles complete one fully mixed family.
Alice's T values 2 and 1/2 exceed F's 0, and Bob is optimal: this is a source SE.

### Native actions, timing and information

Alice is ready at 0 with deadline 2 and inclusion bound 1: her first activation
is protected, her sole later activation at 1 after WAIT unsafe. Bob is activated
at her completion (0, 1 or 2), with deadline duration 3 and bound 0. These modeled branches
are not an all-RAW [ReactiveAsyncContract](../Vegas/Pending/ReactiveAsyncContract.lean) instance.

Alice has T (authentic TRUE opening), W (no packet), and R (raw withholding).
First T/R is certainly included at clock 0. Late T is included at clock 1 with
p=3/4, the same kernel for both types. Otherwise no inclusion is attempted: T
stays pending and expiry at clock 2 executes F. Late R is certainly included;
late W expires without a packet. R executes F but is forbidden even with a TRUE
receipt, by [the settled verdict](../Vegas/Pending/ReactiveSettledVerdict.lean).
Canonical source F uses packet-free expiry, consistent with
[canonical emission](../Vegas/Pending/ReactiveCanonicalDecision.lean).

Alice remembers [T], [R], [W,T], [W,W] or [W,R], retaining censored T.
Bob has empty own recall and no pending leak. His full input
retains public application state, clock/activation metadata, exact ledger and
receipts, and his constant private candidate. Its variable components are:

| Bob site | Clock / activation | Publication | Alice ledger / receipt |
| --- | ---: | --- | --- |
| firstT | 0 | T | T at (Alice,0), TRUE |
| firstR | 0 | F | R at (Alice,0), TRUE |
| lateT | 1 | T | T at (Alice,0), TRUE |
| lateR | 1 | F | R at (Alice,0), TRUE |
| E | 2 | F | neither ledger entry nor receipt |

E pools censored [W,T] with packet-free [W,W]: Bob sees neither pending packets
nor Alice's recall. Rejected inclusion would publish a body and FALSE receipt,
creating a different, omitted input.
Bob's choices are H (authentic opening, certainly included), L (no packet until
FALSE expiry), and R (accepted raw withholding, effective guess L but forbidden).
In this three-action tree each owner has one resolution decision.

### Authentic audit and one common consistency family

One independent final fair coin selects all actually present forbidden signed
envelopes, including pending censored T, or none. Each owner pays one capped D=4
iff their envelope is selected. Charges share the coin; q=1/2 and qD=2. Attribution
uses the original author. Accepted authentic T and packet-free expiry are lawful;
R and unaccepted T after completion are forbidden. This abstract authentic backend
is not a live watcher; see [ReactiveServiceAudit](../Vegas/Pending/ReactiveServiceAudit.lean).

For 0<t≤1/20, Alice's probabilities have columns (T,W,R):

| Input | T | W | R |
| --- | --- | --- | --- |
| first H | 1−3t−t² | 3t | t² |
| first L | 1−t−t³ | t | t³ |
| late H after W | 1−2t² | t² | t² |
| late L after W | 1−t²−t³ | t² | t³ |

Bob's columns are (H,L,R):

| Input | H | L | R |
| --- | --- | --- | --- |
| firstT | t | 1−2t | t |
| firstR | 1−2t | t | t |
| lateT | 1/3 | 2/3−t | t |
| lateR | 1−2t | t | t |
| E | 1−2t | t | t |

All actions and sites have positive probability. Use Bayes beliefs and
tₙ=1/[20(n+1)]. The exact H posteriors are:

| Site | Posterior | Limit |
| --- | --- | ---: |
| firstT | (1−3t−t²)/(4−6t−t²−3t³) | 1/4 |
| firstR | 1/(1+3t) | 1 |
| lateT | (1−2t²)/(2−3t²−t³) | 1/2 |
| lateR | 1/(1+t) | 1 |
| E | (1+2t²)/(2+5t²−t³) | 1/2 |

Summing the specified paths gives these fractions. E's limiting full belief is
half H/[W,T] censored and half L/[W,T] censored; [W,W] has order t³ versus E's t.
Other Bob sites have one Alice past per type. Alice knows her type and first action.
The family specifies full beliefs, retaining rather than canceling foreign WAIT.

### Whole-policy comparisons and preserved law

At posterior μ, Bob's (H,L,R) values are (μ,1−μ,1−μ−2). Hence the limiting
choices are L at firstT, H at firstR/lateR, H with probability 1/3 at lateT,
and H at E. The last two sites have μ=1/2, so these choices are optimal.
This covers all 3⁵=243 pure Bob policies; only one Bob site is played.

| Alice type | Late T | Late W | Late R | First T | First W, best later policy | First R |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| H | 1 | 0 | −2 | 2 | 1 | −2 |
| L | 1/4 | 0 | −2 | 1/2 | 1/4 | −2 |

Late T has expected deduction (1−p)qD=1/2. Its values are
(3/4)·2−1/2=1 and (3/4)[(1/3)·2+(2/3)·(1/2)]−1/2=1/4;
failure has base 0 because E plays H. Backward comparison covers all nine pure
plans per Alice type, hence all 81 type-contingent plans. Mixed deviations are
convex combinations. The limit is rational and the common family gives
consistency; finite-t strategies themselves need not be exact optimizers.
If lateT instead pinned Bob to source LOW, L's T value would be −1/8<WAIT0.
The rational H-probability 1/3 changes it to 1/4, still below immediate T's 1/2.

Its initialized joint law (parameter, publication, guess, net Alice, net Bob)
is (H,T,L,2,0) with mass 1/4 and (L,T,L,1/2,1) with mass 3/4, exactly the source
law. Limit play incurs no charge. Rational lateT play differs from source play;
preservation does not require source beliefs or actions at every new native input.

**The three-action calculation omits:** prior binding traffic, competing IDs,
malformed or extra evidence, stale credentials, guard failures, rejection receipts,
extra activations, nonempty leaks and raw foreign traffic. The next result treats
copies and RAW tails at fixed prefix inputs; arbitrary RAW prefixes, later source
economic moves and service/backend certification remain excluded. Copies retain
the original author and cannot be classified as newly authored R.

### Copies and a rational RAW continuation

For p=3/4, q=1/2, D=4, keep Alice's two-opportunity {T,W,R} prefix. Starting
BEFORE Bob's first response at the five listed inputs, allow full bounded RAW
menus and a finite public adaptive tail, including reactivation of either owner.
No extra activation or omitted Alice RAW action before these inputs is included.
Require complete play and prompt protected Bob H acceptance (bound 0, deadline
duration 3, sole ID followed by silence/copies), stable completed outputs and
verdicts of EXISTING envelopes, and the same unobserved final audit coin.
These are explicit service premises, not a certified AsyncContract instance.

The resource shape is source-expressible: θ is Alice's separate privateInput Bool;
both initial commitments contain TRUE, a constant sample precedes the reveals,
and their guards are empty. FALSE leaves Bob's decision available. `ret []` omits
built-in payoff expressions, not terminal publications; [parameterGame](../Vegas/Source/InitialState.lean)
supports utilities of θ and both public outcomes. θ has no opening certificate.
Same raw requests pair all prepared candidates, genuine known IDs and emitted
certificates, by [candidate updates](../Vegas/Pending/EventPlayerAction.lean) and
`WitnessedSubmission.emit_local` in [OpeningEvidence](../Vegas/Pending/OpeningEvidence.lean).
Pair the entire public scheduler past as well as its current view.

With a common θ-erased Alice tail at EVERY n, any Bob whole policy has equal
future observation kernels across matched types. In one class its gross value
is μr+(1−μ)(1−r)≤max(μ,1−μ). At E, the two paired-class H/L reach ratios are
(1−2t²)/(1−t²−t³) and 1; their posterior mixture tends uniformly to 1/2,
including at rare copied/leaked/receipt fibers. [Provenance](../Interaction/ReactiveProvenance.lean)
prevents Alice creating a Bob-authored opening under his all-W policy: initial
bindings are not signed envelopes. Complete expiry then gives lawful L. Prompt H
attains μ. His first [recall entry](../Interaction/ReactiveRecall.lean) preserves the input, preventing later class merges.

Construct the common tail using a positive reference root law λref and terminal
utility weights λn/λref, where λn is the actual prefix law. Alice's erased recall
fixes H/L odds, so proxy comparisons equal actual L's. Use the finite
[pinned best-response chooser](../GameTheory/GameTheory/Analysis/PerturbedEquilibrium.lean)
with paired full-support RAW references, then one subsequence of ACTUAL Bayes
assessments. After clear T/F, L's possible gain is at most 3/2 or 1, below the
first-new-forbidden cost 2; silence supplies the zero-charge comparator. H's base
is constant, so the H type optimally mimics this clear proxy. After R/censored T its old
forbidden witness and expected capped charge 2 persist; his net value is constant.
No further fine is counted. Lawful copies preserve the original author and verdict.

Keep the original Bob limiting laws. After original W/copy at firstT/lateT/E
with no own pending HIGH, select LOW expiry; after protected H select silence.
Optimize remaining tail sites in that SAME family. The whole-policy bounds give
rational completion and preserve the two atoms above, with distinct RAW histories. This paper
result excludes arbitrary Alice RAW prefixes, changed guards/candidates, later
source economic moves and live watcher/runtime certification. Copy is not a
scheduler-independent quotient of silence; its continuation is optimized.

### Inclusion and audit parameters

In the same three-action tree, take 0<p<1, q∈[0,1], D≥0, c=qD and b=(1−p)c.
Keep the same information partition and shared all-or-none audit coin of weight q.
If b≤2p, both types send late T; choose Bob's lateT HIGH probability α in
max{0,(2b−p)/(3p)}≤α≤min{1,(2b+1−p)/(3p)}.
The interval is nonempty. Late T values are H:2p−b and L:p(1/2+3α/2)−b,
respectively in [0,2) and [0,1/2]; W=0 and R=−c. Hence first WAIT cannot improve.
If b>2p, both types choose late W and α=0; both T values are negative, so
first WAIT gives 0. At b=2p, sending uses α=1 and ties W at 0.
Use the original Alice first family. In the sending regime retain her late
family; in the waiting regime swap its T/W columns. At each Bob site with
limiting HIGH probability a use ((1−3t)a+t,(1−3t)(1−a)+t,t).
Here a=0 at firstT, 1 at firstR/lateR/E, α at lateT. All probabilities are positive.
The five type posteriors still tend to (1/4,1,1/2,1,1/2). E's full belief is
half H and half L with censored [W,T] when sending, [W,W] when waiting.
Bob's values are (μ,1−μ,1−μ−c); the stated choices are optimal, including ties.
These backward inequalities cover all modeled whole policies. The initialized
joint law remains exactly the two atoms above, with zero realized charges.
Thus the restricted preservation result holds for every such p,q,D, including c=0;
it does not certify omitted raw actions, adaptive continuations or the runtime contract.

## B. Publishing a known forbidden witness

Fix a genuine initialized RAW snapshot with completed source gameplay. Source
readout, cut and accepted bindings, and existing-envelope verdicts stay fixed
through the challenge; clocks and receipts may change. Let m be a retained authentic
forbidden envelope authored by a, with an observer distinct from a. At a promised activation,
availability must be ≥p conditional on every supported preceding history: known or
public m is available certainly; unknown foreign pending IDs use actual sampling.
[ReactiveRecall](../Interaction/ReactiveRecall.lean)'s `known_from_recall`
reconstructs replay eligibility from own outputs, leaks and ledger, not hidden inputs.

After observation choose an owner uniformly from K≥1 owners. For a selected owner
with a known forbidden witness, replay one such exact envelope's ID, or do nothing
if it is already public. [MessageNetwork](../Interaction/MessageNetwork.lean)
preserves its author, ID and body. [ReactiveApplication](../Interaction/ReactiveApplication.lean)
publishes before handler evaluation; even a FALSE receipt publishes authentic
evidence. For this retained m, initialized identity and
[receipt invariants](../Interaction/ReactiveReceipts.lean) equate ledger membership
with some Boolean receipt for its ID. [UniqueIds](../Interaction/MessageNetworkIdentity.lean)
ensures the same body. No new report constructor or TRUE receipt is needed;
the audit charges m's author, not its copier.

Require conditional publication probability ≥r on every supported selected-witness
branch, uniformly over later RAW traffic, with 0≤p,r≤1. For settlement collecting
published forbidden evidence, let A be m's availability, J the selected owner and Cₐ owner a's OR charge;
the tower rule gives P(Cₐ)≥r·P(A and J=a)=r·P(A)/K≥pr/K, without independence
of observation and delivery. This is total owner OR collection, not another fine.
For fixed m paired with each run's actual final R, uniform selection among at most
M≥1 distinct known forbidden IDs of a yields pr/(KM). First-witness selection
need not cover m. Existing single-ID replay is not batch forwarding.

Reuse `sampling_delivery_lower` in [MessageMonitoringProbability](../Interaction/MessageMonitoringProbability.lean)
and `GameTheory.Math.Probability.expect_bind_of_finite` in [Expectation](../GameTheoryExtensions/Math/Probability/Expectation.lean).
They compose supported conditional bounds; they do not supply the service promises.
Current AsyncContract has no postterminal activation/publication guarantee.
[SourceServiceAudit](../Vegas/Game/SourceServiceAudit.lean) samples authentic
(final record, original envelope) pairs; any receipt can identify published material.
But [SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean)'s
coverage premise is pointwise for each actual evidence list and each forbidden
record. A physical challenge can fail on a supported final history, where a
published-only sampler has zero coverage. Its history-integrated pr/K bound
does not establish that premise. A faithful settlement/backend refinement and
its actual evidence accessibility remain open; ledger publication alone is not it.
