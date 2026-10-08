# What equilibrium preservation can support

Analysis by Codex, informed by independent mathematical investigations of
belief consistency, runtime services, and the negative examples. This document
records mathematical conclusions and candidate theorems. It does not change
the target, semantics, or boxes in the
[async checklist](se-async-checklist.md). **Checked** means a Lean theorem;
**paper proof** means an argument supplied here but not mechanized;
**conjecture** identifies work still needed.

The [general preservation analysis](general-se-preservation.md) states the
checked finite-deposit theorem for all source SEs, the public stochastic
scheduling paper theorem, and the remaining source-to-runtime adapters.

An abstract language remains viable. The strongest supported design is an
abstract game compiled through a specified information and execution service.
The negative result limits particular service contracts; it does not say that
sequential equilibrium is incompatible with public blockchains. Weak PBE is a
promising additional target, but it changes the requirement on off-path beliefs
and has not yet been proved for the general asynchronous runtime.

## The claims have different quantifiers

For a source equilibrium and a fixed runtime, ask separately whether:

1. Its prescribed client strategy is an equilibrium against all raw deviations.
2. Some runtime equilibrium has its joint law of initial parameters, public
   results, and realized net payoffs.
3. Every source equilibrium has such a runtime realization.
4. Every runtime equilibrium corresponds to a source equilibrium.
5. Some different protocol or compiler can implement the same source game.

The late-leak theorem refutes the second claim for a particular source outcome
and late-turn protocol, hence the third for any compilation class containing
that example. It is stronger than failure of one strategy translation. It does
not refute the fifth. Realizing this finite example inside the complete bounded
raw runtime remains a separate unproved obligation.

Finite perfect-recall games still have SE. The library's
[existence theorem](../GameTheory/GameTheory/Analysis/Protocol/SequentialExistence.lean)
and the late-leak obstruction are compatible: the target has equilibria, but
their outcomes differ from the specified source outcome.

## Results in the current model

| Claim | Assessment | Scope |
| --- | --- | --- |
| Exact Nash preservation against all bounded raw deviations | Checked | First-turn clients, every contract builder, barrier-ordered modes |
| Nash preservation with concurrent reveals | Checked | Opening clients in every dependency mode; timing error is quantified |
| Intended SE preservation by the calendar service | Checked | The specified finite calendar, observations, enforcement and well-formedness assumptions |
| Finite penalties preserve every late-leak SE outcome | Checked | R>=0, D>R/2 and (1-q)(D+c)>R/2; visible dropped disclosures remain |
| These penalties also force every weak-PBE outcome | Checked | Sequential rationality and on-path Bayes consistency suffice in the same finite game |
| Whole-run conditional survival bound | Checked | Pointwise survival floors multiply over bounded adaptive opportunities |
| Late-leak full-state approximation gap | Checked | Every exact target SE is at least 267/2000 away at the sample parameters |
| Late-leak approximation gap after erasing timing | Checked | At least 3/2000 for the joint initial-type, success/failure and answer law |
| Intended outcome preservation by arbitrary late-leak protocols | False, checked | The finite late-leak family under the two deferral margins |
| Weak PBE preserves the late-leak intended outcome | Paper proof | Explicit assessment below |
| Bonanno PBE or common-CPS PBE repairs that example | False, paper proof | Their coherent plausibility conditions retain the obstruction |
| Every intended SE has a weak PBE realization in the general async runtime | Conjecture | Belief-support and credible-completion adapters remain open |
| Sealed pending payloads repair the isolated late-turn family | Paper proof | Identical content-independent inclusion coins, suitable penalties, no other bit leakage |
| Sealed pending payloads preserve arbitrary source SE | Open | Metadata, scheduling, admission and continuation obligations remain |
| Timed recovery alone preserves arbitrary source SE | Unsupported | The same mechanism can occur at commitment admission |

The exact Nash statements are pinned as `async_first_turn_nash_iff` and
`intended_async_first_turn_nash` in [Paper](../Paper.lean). The comparison is
against the full bounded raw deviation space, rather than just other clients.
The equivalence concerns the specified compiled profiles; it does not classify
all native Nash equilibria. `intended_opening_client_nash` covers all dependency
modes, including concurrent reveals: a source epsilon-Nash profile produces
error at most epsilon plus `2 delta R`, with joint-law error at most delta.
First-turn timing has delta zero. These hypotheses should accompany any
headline about Nash preservation on an arbitrary builder.

The checked SE result is
[`SourceServiceSpec.audited_raw_sequentialEquilibrium_preserved`](../Vegas/Game/SourceServiceCompilation.lean).
Physical implementation of its service assumptions is an additional task.
The calendar does not require finite support of its unused network policy;
its reserved scheduler never invokes that policy. The checked refinements and
their limitations are detailed in [runtime refinements](se-runtime-refinements.md).

## The negative family and finite penalties

Write R for the sender's base payoff range, D for the failure forfeit, c for
the drop charge, and q for late inclusion probability. The
[checked theorem](../Vegas/Examples/LateLeak/Preservation.lean) excludes the
intended outcome when

\[
q(D-R)>(1-q)c,\qquad qR-(1-q)(D+c)>R/2.
\]

For every R > 0, D > R and c >= 0, both hold for every q above

\[
\max\left\{\frac{c}{D-R+c},\frac{D+c+R/2}{D+c+R}\right\}<1.
\]

Thus no fixed finite margins work uniformly across this family of builders.
This is **not** a statement that one fixed q defeats every possible deposit.
The builder in this example uses a content-independent coin. Its failure is
caused by pending disclosure combined with strategic timing and consistent
off-path responses; selective censorship is unnecessary.

There is also a positive result for fixed bounded q. Suppose every late send in
this isolated family has q <= qbar < 1. Any deferred continuation pays at most

\[
\max\{R-D,\ R-(1-\bar q)(D+c)\}.
\]

The first term covers never sending, the second a late attempt. A dropped send
ends the attempt; this is not a model allowing arbitrarily many retries.
Consequently

\[
D>R/2,\qquad (1-\bar q)(D+c)>R/2
\]

suffice for a preserving SE in G*, even with leaks. In fact, with R>=0 these
costs force **every** target SE to have the intended outcome; existence follows
from the finite perfect-recall SE theorem. Both statements are checked in
[CalibratedPenaltyPreservation](../Vegas/Examples/LateLeak/CalibratedPenaltyPreservation.lean).
Labels A/B always obtain at least R/2 from protected opening and strictly less
from deferring. Label C obtains at least zero protected, but strictly negative
payoff from every deferred policy. Bayes consistency then forces the safe
protected reply. The checked finite-charge corollary uses c=R/[2(1-q)] for
any fixed q<1 and D>R/2. This remains a theorem for the isolated finite game,
rather than a general asynchronous compiler capstone. Its outcome conclusion
uses only sequential rationality and on-path Bayes consistency, so it also
holds for every weak PBE under these cost bounds. This is checked as
`lateLeak_outcome_preserved_of_rational_bayes`; the separate weak-PBE
construction below covers weaker costs and remains a paper proof.

For a more general isolated terminal-response family with base payoffs in
[0,R], c >= 0, and distinguishable protected and late response sites, the
analogous sufficient inequalities are D > R and `(1-qbar)(D+c) > R`.
A general runtime theorem would need these bounds
conditionally at relevant information sets, with the actual additional
collectible cost. A per-packet q cap does not automatically bound a whole retry
policy's probability of success.

A concrete-chain corollary needs a realization of the protocol, a leak
schedule, attainable inclusion probabilities, and fees included in utilities.
In an IID-slot toy model, a fixed finite number j of slots and fixed p < 1 give
`q = 1-(1-p)^j < 1`. This formula alone supplies no arbitrarily-high-q result.
If an attempted late send costs an extra f, sufficient negative margins become
`q(D-R) > (1-q)c+f` and `qR-(1-q)(D+c)-f > R/2`.
Higher priority fees encourage inclusion; the official documentation does not
give the bounded-window probability claim needed here.
[Ethereum gas documentation](https://ethereum.org/developers/docs/gas/)

## Weak PBE is a real alternative, with a weaker promise

Use **weak PBE** to mean sequential rationality at every information set and
Bayesian beliefs at every information set reached with positive probability.
At a zero-probability information set, beliefs must be supported on its
possible histories but need not fit one global perturbation or plausibility
system. The name PBE alone is ambiguous. Watson surveys the definitions and
the consequences of strengthening belief updating.
[Watson, *Perfect Bayesian Equilibrium: Consistency Conditions for Practical Definitions*](https://economics.ucsd.edu/~jwatson/PAPERS/WatsonPC.pdf)

For G*, a preserving weak PBE exists whenever R > 0, D > R/2, c >= 0 and
0 < q < 1:

- Every sender type opens protected.
- The listener chooses the safe answer after every success. At each off-path
  success it believes the three hidden labels equally likely, independently
  of beliefs at the other success sites.
- After a leaked failure it guesses the disclosed bit. After a silent failure,
  assign probability one to bit zero and guess zero.
- Choose optimal off-path sender timing by backward induction, separately for
  each fully observed sender type.

The safe answer gives the listener 2/5 versus at most 1/3 from a label guess.
The sender receives R/2 on every successful branch and at most R-D < R/2 on
every failed branch. Every late attempt has positive failure probability;
never sending also gives less than R/2. Protected play is therefore optimal.
All on-path beliefs are Bayesian, and all off-path decisions are credible
under their assigned beliefs. Under the checked negative margins, this
assessment cannot be SE-consistent.

The selective-censorship example in
[`censored_disclosure_probe.py`](../scripts/experiments/censored_disclosure_probe.py)
also admits preserving weak PBE: its off-path silent information sets can each
use the deterring uniform posterior and equal mixture of the two designated
responses. Hence neither existing negative example refutes weak-PBE
preservation.

Nevertheless, Nash preservation does not imply a PBE preservation theorem.
For the general barrier-ordered intended runtime, the proposed proof must:

1. Lift source posteriors to histories compatible with each actual runtime
   observation. Off-path beliefs cannot deny a fact that the observation proves.
2. Supply one strategy and belief at information sets shared by clean and
   broken histories.
3. Complete broken histories rationally without destroying whole-continuation
   optimality at the sites where source play is prescribed.

These are concrete, unresolved adapter obligations. Concurrency needs its own
analysis. Weak PBE may be easier to preserve because independent timing copies
can receive independent off-path posteriors; it also permits beliefs about
surprises that a coherent common explanation of execution would exclude.

Additional payoff-relevant information on the honest path can defeat even
Nash and weak PBE. For example, if a runtime reveals a fair private bit before
a receiver's guessing decision, whose source observation hides it, the receiver
can improve from success probability 1/2 to one. On-path Bayesian updating
leaves no freedom to ignore that bit. This is an information-leaking runtime
counterexample, not a claim about the checked opaque-binding compiler.

## Some stronger PBE notions still fail

The G* obstruction extends beyond independent Kreps-Wilson trembles. The
following is an own paper proof for beliefs admitting a common qualitative
plausibility ranking compatible with strategies and positive chance moves.

Sequential rationality under the deferral margins makes every type send at
the second late turn. Whatever the listener's success replies, the leaked
failure creates a bit class with two labels S and H that strictly prefer
opposite turns. This is the existing
[opposite-preferences argument](../Vegas/Examples/LateLeak/Impossibility.lean).
S sends first and H waits for the second turn.

Let a and b be their first-late history ranks, with smaller ranks more
plausible. A positive-probability action preserves rank; a zero-probability
action strictly raises it. Positive-probability inclusion preserves rank too.
Thus the first-success ranks satisfy `F_S = a`, `F_H > b`, while the
second-success ranks satisfy `T_S > a`, `T_H = b`.
If H has positive first-success posterior, `F_H <= F_S`, so b < a.
If S has positive second-success posterior, `T_S <= T_H`, so a < b.
Both cannot hold.

One success posterior therefore omits a label. Its largest label probability
is at least 1/2, which beats the safe answer's 2/5. The listener must guess.
Any such guess rewards sender type (v,A) by R, so it can defer to that turn
and obtain at least `qR-(1-q)(D+c) > R/2`. Protected safe play cannot be
optimal.

Bonanno's AGM-consistent PBE supplies these ranking rules, including the
restriction on chance moves. Common-CPS PBE supplies them as well for this
game's singleton sender and chance sites. Thus these two precisely defined
PBE notions inherit the negative result. This conclusion is derived here;
the cited papers provide the definitions, rather than a theorem about G*.
[Bonanno, *AGM-consistency and perfect Bayesian equilibrium*, Definition 6](https://faculty.econ.ucdavis.edu/faculty/bonanno/PDF/PBE-1.pdf),
[Merotto and Wolitzky, *Conditional Probability Perfect Bayesian Equilibrium*, Definition 4 and Theorem 1](https://economics.mit.edu/sites/default/files/inline-files/CPPBE%20March%203%202026.pdf)

## Approximation does not automatically escape the obstruction

There is a quantitative strengthening of the checked negative result.
Assume R > 0, D > R and c >= 0, and set `g = qR-(1-q)(D+c)` and
`alpha = 2(1-g/R)`. Under the negative margins,
g > R/2 and 0 < alpha < 1. The existing face argument applies to every target SE,
not just a candidate preserving one. At some bit v, type (v,A) can earn at
least g by deferring. If it opens protected with positive probability,
support optimality bounds the protected safe probability by alpha. Deferred
success has probability at most q.

Let pi_min be the smallest prior mass of a type (v,A). Then total variation
distance from the intended joint law is at least

\[
\pi_{\min}[1-\max(\alpha,q)]>0
\]

even when timing is erased and the readout retains only initial type,
success/failure, and answer. The full timing-sensitive law has the stronger
bound `pi_min(1-alpha)`. At the checked sample these are respectively
3/2000 and 267/2000. Both bounds are checked in
[ObservableOutcomeSeparation](../Vegas/Examples/LateLeak/ObservableOutcomeSeparation.lean)
and [OutcomeSeparation](../Vegas/Examples/LateLeak/OutcomeSeparation.lean), respectively.
The coarser readout retains initial type; this is not a bound on only the
marginal answer law.

More generally, in a fixed finite game, consistent assessments form a compact
set, and continuation regret is continuous. An excluded outcome law is a
positive distance from the compact image of the exact SE set. A sequence of
consistent epsilon-SE with epsilon tending to zero and outcome laws approaching
the intended law would have a limit that is an exact preserving SE. Therefore
some positive rationality and outcome tolerances are jointly unattainable.
This uses exact SE consistency and fixed game parameters. It does not exclude
coarser approximation, weak-PBE beliefs, or a different computational game.

## Positive runtime designs worth proving

**A broader ordered service.** The calendar theorem is the checked reference.
A service may use observable physical traffic while offering private admission,
irrevocable order, and public logical release points. A sequencer or replicated
committee is a plausible implementation. The mathematical task is to prove
that its timing and observations refine the source information structure,
including deviations and off-path continuations. Having a sequencer alone does
not establish that theorem.

**Sealed admission in the isolated late-turn family.** Consider its finite
perfect-recall terminal-response game, with R > 0, 0 < q < 1, D >= 2R and
c >= 0. If pending traffic does not disclose v, even after dropping, k
identical content-independent late coins admit a preserving SE. Success and
failure continuation games and payoffs are identical across late times, apart
from observable timing metadata; there are no interim strategic choices or
time-dependent fees. Split the proof:

- If `q(D-R) <= (1-q)c`, the upper bound on every late attempt is
  `R-(1-q)(D+c) <= (1+q)R-D < 0`. Complete the off-path game sequentially;
  protected play remains better regardless of its replies.
- Otherwise, every type strictly prefers a late send to never sending, even
  under the worst difference between success and failure base payoffs.
  Choose sending at all late sites and type-independent timing trembles.
  Success posteriors retain the intended label distribution, and failure
  posteriors do not vary by sending turn. Turns are indifferent off path,
  while protected play is strictly preferable at the root.

This is a paper proof for the terminal-response family. The exact timed-release
probe's sealed variants also support preserving assessments at all 60 tested
parameter points; the two points missed by its uniform candidate have other
explicit consistent assessments. Finite probing is corroboration, not proof
of a general language theorem.

**Encryption with an explicit metadata and ordering contract.** Encryption
alone does not supply the preceding hypothesis. If ciphertext length or a
public header discloses v, the same negative game survives with the header
replacing the plaintext leak. Sender-controlled timing, fees, packet count,
selective key release, reordering and observations after failure all need
accounting. `BlindToLatePackets` allows a content-dependent inclusion-mixture
coefficient; it does not establish a content-independent scheduler.
The proposed universal sealed-until-ordered theorem remains open. It requires
a decryption/finality contract too. Shutter's research documentation explicitly
distinguishes per-epoch key release, which exposes excluded transactions, from
batch-selective release, which can leave them sealed. Threshold encryption by
itself therefore does not establish that excluded packets stay confidential.
[Shutter, *The Road Towards an Encrypted Mempool on Ethereum*](https://docs.shutter.network/docs/shutter/research/the_road_towards_an_encrypted_mempool_on_ethereum)

**Recoverable admission and autonomous release.** Removing the owner's reveal
decision can help, but a pending commitment that is later recoverable can
recreate the same leak after failed admission. Counting recovery delay from
initial transmission protects earlier choices, not necessarily the later
failure-branch response. The current timed-release probes exhibit precisely
this problem, even with zero additional drop charge. Boneh-Naor recovery is
neither necessary nor sufficient for SE preservation; it is a building block
for an owner-independent release service. See the fuller
[runtime-alternatives analysis](se-preservation-runtime-alternatives.md).

**Enforcement that applies to successful departures.** An additional
conditionally collectible penalty exceeding the largest continuation gain
can deter a first strategic departure regardless of its inclusion success.
The checked
[restriction-extension machinery](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
and [audit machinery](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
provide reusable proof consumers. A backend still needs attributable evidence
and collection under arbitrary continuations. An already-certain charge has
zero incremental deterrent effect; it cannot be counted again to forbid a
later disclosure. Dirty histories need rational completion under remaining
utility.

**A source fragment with protected choice admission.** A promising fragment
admits private choices with source-sufficient observations and padded,
type-independent traffic, fixes all relevant choices before release, and
uses autonomous output. The first-departure enforcement and off-path
completion adapters still need proof. Merely saying all values are committed
before revelation does not settle the incentives during admission. If choices
are already irrevocable at the start of a pure release suffix, and every later
player action leaves its output and utility law unchanged at every admitted
history, including off-path histories, preservation for
that suffix is immediate: rationality is vacuous and consistency can be
constructed with arbitrary fully mixed strategies.

**A mediator or computational refinement.** Positive SE implementation results
exist in other standard communication models. Geffner and Halpern implement
mediated Bayesian/normal-form communication outcomes with SE under reliable
private communication and participant thresholds n > 3k synchronously and
n > 4k asynchronously. They explicitly construct consistent off-path beliefs.
This is evidence for a mediator backend, rather than a theorem for arbitrary
dynamic Vegas programs, finite deadlines, public settlement or net fees.
[Geffner and Halpern, *Communication games, sequential equilibrium, and mediators*](https://arxiv.org/html/2309.14618)

Concrete cryptography also calls for a computational equilibrium formulation.
Halpern, Pass and Seeman prove a computational SE transfer result under an
explicit representation relation. That includes matching history lengths,
so a multistep runtime needs an additional adapter. Secure computation or
negligible cryptographic leakage alone does not establish sequential
optimality at rare information sets.
[Halpern, Pass and Seeman, *Computational Extensive-Form Games*, Theorem 4.6](https://arxiv.org/html/1506.03030)

## Proposed research priorities

Further useful theorem candidates are the explicit weak-PBE construction, the
qualitative-plausibility negative, and the isolated sealed-admission positive.
Together with the checked penalty and approximation results they distinguish
the solution concepts and test the backend's information contract before a
universal claim.

In parallel, the highest-value general theorem candidates are weak-PBE
preservation with concrete belief-support/completion adapters, and exact SE
preservation by a broader ordered private-admission service. Recoverable
commitments can implement part of that service. The general theorem must
derive the needed information and incentive properties from operational
rules, while keeping those rules in the backend contract rather than in every
source program.

The [blockchain target analysis](blockchain-se-preservation-target.md) identifies
concrete confidential-ledger candidates, explains what the fixed program
horizon contributes to conditional inclusion bounds, and states a more precise
sharpness goal than necessity of every service component.
