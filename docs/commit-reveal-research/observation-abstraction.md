# Keeping ancillary runtime observations out of the source game

This is Codex's mathematical analysis of candidate interfaces. It proposes no
new adopted VegasCore model, runtime semantics, or checklist change. The general
result below is a paper theorem. The checked public scheduling reference and
the private-view extension awaiting its own verification are identified explicitly.

Packet observations need not disappear for an abstract source language to be
useful. Some observations are additional randomness whose conditional law is
the same across every source history a player cannot distinguish. Players can
remember these observations, learn about runtime conditions from them, and
still have an SE implementing the original source policy. That conclusion
requires a separate execution condition: the learned conditions must not
change logical menus, source transitions, or utility.

This gives an operational way to omit details from the source: retain them in
the implementation game, prove a channel condition and an execution condition,
and construct an assessment that ignores the extra data. It does not require
players to forget observations or assert that they never use those data in
other equilibria.

## The finite interface and what it omits

**Source model.** Let G be a finite extensive game with perfect recall. All
chance edges in its legal tree have positive probability. Source information
I_i(h) includes the player's remembered observations and own choices. Logical
stage is recoverable at each player decision; its earlier own decision stages
are recoverable through perfect recall. Private source values may remain hidden
across arbitrary numbers of phases and may be correlated between players.

**Runtime model.** Expand each source transition by finite chance-only runtime
processing. Runtime state can be hidden and persistent. Processing can emit
public packet records, private receipts, observed clock ticks, or no new datum.
There is a fixed finite bound on the number of physical steps before the next
logical transition, under every compatible runtime state. A wait offers no
player action and cannot prevent eventual progress within that bound.

At a logical decision the actor has exactly its source action menu. Given any
complete current runtime record, the next logical transition has exactly the
source chance law for the selected source action. Runtime processing before or
after that transition can depend on the realized source transition, but cannot
change its marginal logical law. Terminal payoff is the source payoff of the
erased logical history. There is no extra action-dependent fee, discounting,
locked-capital utility, outside trading reward, or runtime-dependent ability to
take an action.

Each player receives exactly its original source observation increments plus
the emitted auxiliary observations it can physically obtain. It remembers
all of them, with enough logical-stage labels to recover its earlier auxiliary
records at its own decisions. Own source actions retain their original recall.
Thus its target information is constructed as

\[
J_i=(I_i,Z_i),
\]

where Z_i is its *entire remembered auxiliary record*, including any physically
public packet existence, length, sender, fee, contents and timing fields.
The information formula follows by accumulating these primitive observations;
it is not a restriction to what the honest client decides to inspect.

The scheduler is a nonstrategic chance service. Miner/builder utilities and
strategic fee bidding, participation, packet fabrication, retries, selective
omission, denial of service, and voluntary off-chain disclosure are not extra
actions in this interface. They require a larger source game, an enforcement
extension, or a separate game-specific comparison. The theorem does not
discharge those obligations.

## An operational channel test

For every source history h ending just before a logical decision, replay the
runtime mechanics with the source actions and source chance outcomes externally
fixed to that history. Sample only the runtime chance kernels. Let Q_h be the
resulting probability law of the complete finite runtime record omega.

The replay stops at the ready copy of that decision at h. Only the actions
and chance outcomes in the *prefix h* are fixed. It neither conditions on
future source outcomes nor samples until a favorable future event occurs.

This is an *open-loop replay law*. It is computed by multiplying or iterating
the advertised physical kernels. It is not the conditional law under a
selected equilibrium, and does not require a prior or any player's strategy.
For example, after fixing an edge h to h', its normalized runtime kernel C
gives the recursion

\[
Q_{h'}(\omega')
 =\sum_\omega Q_h(\omega)C_{h,h'}(\omega,\omega').
\]

C incorporates post-transition processing and the next bounded wait phase.
All prior runtime records are retained in omega', so it also represents the
actual physical history. The independent source transition probability is
deliberately not part of C or Q. The execution condition makes every row of C
a probability law for each legal source edge.

Let Z_i(h,omega) be the observation decoder supplied by the physical model.
Require the following finite channel equality:

\[
 I_i(h)=I_i(h')\quad\Longrightarrow\quad
 (Q_h\circ Z_i(h,\cdot)^{-1})
   =(Q_{h'}\circ Z_i(h',\cdot)^{-1}).                 \tag{A}
\]

Only histories in the same source decision information set are compared.
The equality is of the laws of the *full* auxiliary records, not just the most
recent receipt. It includes their support, not only a mean or a distinguishing
bound. Different players can have different decoders and records. Their
auxiliary observations can be correlated across players and across time.

This condition says which physical experiments must be compared: hold each
possible source history fixed, run the same backend, then inspect one player's
observable record. It can be checked by finite dynamic programming or proved
from an observation-local state machine. It contains no posterior equality,
equilibrium belief, optimal action or selected-equilibrium reach probability.
It is stronger evidence than declaring that desired posteriors transfer.

The condition need not hold for arbitrary erroneous or extra raw actions not
in the declared game. Extending the result to those actions is a different
obligation. Conversely, testing only the selected source equilibrium's honest
histories is insufficient: the test covers every legal source history.

## Paper theorem: ancillary observations preserve selected SE

**Model for this result.** Use the complete finite source and runtime
construction just described, with unchanged logical transition laws, menus and
payoffs, bounded chance-only processing, original source observations, full
auxiliary recall, and channel condition (A) on all source decision fibers.

**Theorem, paper proof.** For every source SE (sigma,mu), the runtime has an SE
whose policy at (I_i,z_i) is sigma_i(I_i), and whose belief projects to mu_i(I_i)
at every target decision, including off-path decisions. Its erased terminal
history law and source payoff law equal those of the source SE. The same
statement permits correlated private runtime observations and retained private
source values across phases. It asserts forward preservation, not reflection
of all target equilibria.

The copied behavioral policy is the same for every service satisfying this
interface: it uses only the recovered source information and ignores the
runtime channel. Its full consistent beliefs depend on that channel. Thus the
theorem gives a common preserving policy across the service class, rather than
only unrelated pointwise policies. A hidden-service Bayesian application still
requires a specified prior and a proof that its resulting channel and execution
laws satisfy the same conditions.

### One common consistency sequence

Choose a source SE consistency sequence sigma_n, fully mixed on every legal
source player menu, with Bayes beliefs mu_n converging to mu. Copy sigma_n at
every runtime copy of each source information set, ignoring all auxiliary
records. Every target player action has positive probability. Waiting and
runtime emissions are chance moves.

For a complete runtime prefix x above a source decision history h, let omega
be its runtime record. Direct multiplication of transition probabilities gives

\[
w'_n(h,\omega)=w_n(h)Q_h(\omega).                   \tag{B}
\]

This identity is proved by induction through the physical history. Runtime
chance steps contribute their actual kernel probabilities to Q. Logical
choices contribute the copied sigma_n probabilities; logical chance steps
contribute the unchanged source probabilities. Consequently neither Q nor
the factorization depends on n. No conclusion about target beliefs has been
assumed.

Write q_{i,I}(z) for the common auxiliary marginal in (A). For a legal target
decision J=(I,z), q_{i,I}(z)>0, and every source history in I has at least one
compatible runtime realization of that observation. Sum (B) over those
realizations and use Bayes' rule at the fully mixed index:

\[
\Pr_n(h\mid I,z)
 =\frac{w_n(h)q_{i,I}(z)}
        {\sum_{g\in I}w_n(g)q_{i,I}(z)}
 =\mu_{n,i}(h\mid I).                              \tag{C}
\]

The full belief on target histories is also explicit. On compatible omega,

\[
\Pr_n(h,\omega\mid I,z)
 =\mu_{n,i}(h\mid I)
   \frac{Q_h(\omega)[Z_i(h,\omega)=z]}{q_{i,I}(z)}. \tag{D}
\]

The second factor is a fixed probability kernel for each h. Therefore the full
target beliefs converge, not merely their projected marginal. Equations (C)
and (D) work before taking a limit; they never condition on a limiting
zero-probability information set. One lifted fully mixed sequence supplies
all target beliefs simultaneously. This proves consistency and constructs
the assessment.

### Whole continuation rationality

Fix a target site (I,z) and a local action lottery beta there. From each full
compatible target history, use beta once and the copied source policy afterward.
The erased continuation law is exactly the source continuation from h using
beta at I and sigma later. Bounded physical processing sums to one; the next
logical transition has its source law at every runtime state; future copied
actions ignore runtime data. Induction on the remaining logical tree proves
this conditional equality. It does not require future runtime observations
to be independent of their past.

Average over the constructed target belief (D). Payoff depends only on the
erased history, so (C) makes this the original source continuation comparison
under mu(I). Source sequential rationality bounds beta's gain by zero.

The target has perfect recall: source recall recovers earlier own source
information and actions, while the labelled auxiliary record recovers the
extra information held at those decisions. Finite perfect-recall
one-shot-deviation equivalence then implies optimality against *entire*
continuation policies. Such a policy may react to many future receipts, learn
the runtime state, and coordinate its own future actions using those receipts;
the proof has not limited deviations to policies that ignore them.

Explicitly, backward induction first removes a profitable deviation at a last
changed decision, if one exists, because the future there is prescribed play.
Repeat toward the present. Perfect recall keeps a player's earlier information
and action probabilities constant over each of its later information fibers,
so changing its own earlier randomizations does not introduce a different
conditional hidden-state weighting at such a comparison. Consistency supplies
these conditional comparisons, including limits at unreached sites. Equivalently,
replace the last changed actions one information set at a time using the
finite perfect-recall one-shot principle. This is why a contingent plan that
reacts to several future receipts is covered, even though its raw physical
description need not be a source policy that ignores receipts.

Finally, execution erasure from initialization, without a deviation, gives
the source terminal law. All runtime branches terminate and have total mass
one for each fixed source continuation. Source utility is the same function
of that terminal history. This establishes the theorem.

The continuation argument and the prefix likelihood argument are independent
requirements. Ancillary observations alone do not justify changed service
opportunities or costs; an initialized outcome coupling alone does not justify
the off-path Bayes cancellation.

## A simpler sufficient constructor with hidden runtime state

**Model for this corollary.** Start with the preceding finite execution
conditions. The service has a finite internal state R and samples a joint
token stream. A token can contain a public part and separately encrypted
private receipts for each player. Every player's decoder retains every
physically public field. Initial runtime state and all state/token transition
kernels depend on the source history only through its sequence of public
source projections P, and can otherwise depend arbitrarily on past runtime
state and tokens. Each source decision information set recovers that sequence
of P values, including the relevant public structural data.

**Corollary, paper proof.** Every source SE has an exact preserving runtime SE
ignoring those observations, even with stochastic garblings correlated across
players and time, and even when recipients learn about a persistent runtime
state that predicts later delays.

**Proof.** Replay two source histories in one decision information set using
the same runtime random draws. The public source projection sequences are
identical. Induction through the finite service machine gives identical laws
of the complete runtime token/state records. Each player's decoder is the
same function of that record and its known source-public history, so its
full-record marginal is also identical. This proves (A) from primitive
kernels, and the theorem applies. A randomized decoder is included by drawing
its coins in the joint token kernel. No independence between different
players' decoders, different phases, or different receipt times is needed. QED.

The runtime state need not be unconditionally independent of a source secret:
legitimate public source observations may depend on that secret. The relevant
condition is that the service accesses it only through the public history
already recoverable by the deciding player. Recipients can update a posterior
over R. This is harmless for the constructed SE because R changes only
bounded chance processing, not logical transitions, menus or utilities.

Full tokens need not be public. They are the analyst's joint runtime record.
If a transaction or clock field is physically public, its actual observed
value must be included in every appropriate decoder; a “private garbling”
cannot hide it from someone who can read it. Private receipts can obscure
their bodies from other players only under the candidate interface's explicit
private-channel or cryptographic assumption. Public ciphertext existence and
metadata remain part of the observation test.

The general theorem is more permissive than this constructor. It only needs
each player's marginal observation channel to satisfy (A). A joint runtime
record could vary with a hidden state while each player's marginal stays
ancillary. For example, one player receives a uniform bit U and another U xor
theta: each marginal is uniform conditional on hidden theta, though pooling
their records reveals it. This is not a coalition guarantee. If record-sharing
is an additional action, or an existing source action is used to convey such
data in other target equilibria, a separate analysis is needed; forward
preservation does not claim that all target equilibria ignore the receipts.

## Minimal complete failures of the simplification

### A private receipt reveals a source-hidden state

**Model for this result.** Nature draws a fair bit theta unknown to one deciding
player. Safe pays 3/4. Guess pays one if theta=1 and zero otherwise. The source
has only this decision. The target keeps exactly these actions and payoffs but
provides a free private receipt equal to theta before the decision. All
decisions have perfect recall; no transport fails or has a cost.

**Negative paper result.** The unique source equilibrium chooses Safe. Every
target SE chooses Guess when theta=1 and Safe when theta=0. Its action law is
at total variation distance 1/2 from the source law; no preserving SE exists.

**Proof.** Source Guess has expected payoff 1/2<3/4. A target receipt gives
the compatible singleton-state belief, so the stated actions are strict best
responses. Their information sets have positive chance reach and fixed Bayes
beliefs. Fully mixed action trembles supply consistency and existence. QED.

Thus “private receipt” is not synonymous with “independent runtime noise”.
This is the forced-observation argument from
[information and release](information-and-release.md#paper-theorem-forced-informative-observations-obstruct-a-universal-claim),
specialized to two source states. It is a complete comparison game, not a
native compiler counterexample.

### Individually uninformative records jointly leak

**Model for this result.** Use the same source decision and payoffs. In the
target emit X uniform and independent of theta, followed by Y=X xor theta.
The player remembers both records before choosing. Neither emission changes
source state or offers an action.

**Negative paper result.** Each individual record has the same uniform marginal
for either theta, but no target SE preserves the source action law.

**Proof.** The remembered pair determines theta=X xor Y. The previous strict
best-response argument applies and gives the same distance 1/2. QED.

Consequently (A) must concern the complete remembered record. A per-packet or
per-receipt marginal test is insufficient. An iterative primitive proof can
instead compare the next observation kernels *conditional on the entire old
observed record* and the relevant source information; Y's conditional kernel
fails that stronger test.

### Independent runtime knowledge affects costs

**Model for this result.** The source has one player choosing A or B, with
payoffs 3/4 and one respectively. The target independently draws a fair bit R
and reports it to the player. Its source actions and base payoffs are unchanged,
but B has an additional execution fee 2R; A has no fee. There are no failures
or other decisions. This R is wholly independent of any source parameter.

**Negative paper result.** Source SE uniquely chooses B. Every target SE chooses
B at R=0 and A at R=1, so no target SE preserves the action law.

**Proof.** Source B is strictly better. Target B pays one at R=0 and minus
one at R=1; the displayed choices are strict best responses. Chance determines
all beliefs, and fully mixed action trembles prove consistency. QED.

An information-ancillary state can therefore be strategically relevant.
The example fails payoff correspondence, not the channel test. Miner price
signals and variable gas charges cannot be omitted merely because they are
independent of the game's secret inputs.

### A receipt anticipates a future source chance outcome

**Model for this result.** The source player first chooses bit a. Nature then
draws a fair bit C, and the player's payoff is [a=C]. Select the source SE
choosing a=0. In the target a fair R is observed before that choice, and the
later coin C equals R. There are no fees or other choices. The unconditional
law of C is fair. At the initial source decision there is only one history,
so the current-prefix observation channel test (A) is vacuous.

**Negative paper result.** Every target SE chooses a=R, so no target SE preserves
the selected source action law. Copying a=0 nevertheless preserves the source
initialized joint law of (a,C); on-path law agreement and current-prefix
posterior agreement alone therefore do not prove incentives.

**Proof.** Either source action gives expected payoff 1/2. In the target, after
observing R, choosing a=R strictly beats the other action. Chance fixes those
beliefs, and action trembles supply consistency. The target action-1
probability is 1/2, whereas the selected source probability is zero. QED.

This example violates the theorem's conditional logical-kernel condition:
given the full runtime record R, the next source coin is not fair. The
condition requires source transition kernels to stay unchanged at each
augmented history, not merely after averaging runtime state or only along an
honest initialized execution. A replay channel drawn causally from already
realized source histories avoids anticipation only if this conditional
transition requirement is also maintained.

### Independent runtime state removes an opportunity

**Model for this result.** The source has one player choosing A, payoff zero,
or B, payoff one. The target independently draws and reveals a fair R. If R=0,
both actions are available. If R=1, only A is available. All utility values
remain their source values, and the game is finite.

**Negative paper result.** Source SE chooses B surely. Every target SE chooses
B at R=0 and A at R=1; the source logical law cannot be preserved.

**Proof.** At R=0, B strictly dominates A; at R=1, B is infeasible. The two
positive chance branches fix beliefs, and action trembles wherever there is a
choice supply consistency. QED.

This fails menu/execution correspondence, not secrecy. A bounded wait that
always reaches the original menu is a different interface from uncertain
admission, insufficient gas, a closed deadline, or exhausted capacity.

## Checked boundary and explicit implementation gaps

The checked token-view reference defines
`GameTheory.Protocol.PublicScheduler` with a public projection `pub`, fixed
number `draws`, and kernel reading public projection, full token transcript
and pending count. Its `view : player → Token → View` determines each player's
observed part of each token. The information model remembers
`transcript.map (view player)` and the pending count alongside source information.
`PublicScheduler.expanded_sequentialEquilibrium` and the Paper pin
`Vegas.Paper.public_scheduling_sequential_equilibrium` establish the bounded
token-view case, including the fully public identity view. This is the checked
construction described in
[public scheduling](../public-scheduling-se-preservation.md).

The proof uses replay bijections and equal marginal fiber masses
(`fiberMass_congr`, `bayesBelief_lift_map`), rather than requiring an injective
view or full token visibility. This is checked evidence for that particular
bounded constructor. The general channel-test theorem proved here has paper
status; arbitrary native observations and variable-length packet execution
are not an established instantiation of the checked constructor.

**Independent mathematical review.** A second math agent reviewed the
decision-prefix replay condition, full-belief consistency construction,
conditional continuation argument, adaptive whole-policy reduction, and all
complete finite counterexamples. The review found no mathematical correction.
This is paper-proof review, not machine-checked evidence.

Reusable lower-layer adapters already establish actual probability facts:

- [ConditionalObservation](../../GameTheory/GameTheory/Math/Probability/ConditionalObservation.lean)
  provides `conditional_observation_kernel` and `conditional_kernel_of_fiber`
  for cancelling an observation-local channel, and
  `exists_updated_observation_kernel` for propagating such a channel through
  a source transition under explicit recovery and primitive-kernel conditions.
- [ObservedChoice](../../GameTheoryExtensions/Math/Probability/ObservedChoice.lean)
  factors a choice drawn from an observation-local auxiliary readout into a
  source behavioral kernel. It does not establish observation-locality for a
  real service or remove correlated target equilibrium outcomes generally.
- [ProportionalBeliefTransport](../../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
  supplies Bayes cancellation after primitive reach/fiber identities have
  been proved. It is not an operational substitute for proving (A) and (B).

For an actual packet backend, the missing work is to enumerate all physically
available observations and actions, derive its open-loop runtime channels,
prove the marginal logical transition/menu laws, and establish fees and
bounded service assumptions. Runtime aliases, owner receipts, observable
pending packets, and retry histories cannot be omitted from this derivation
because they are absent from the source language.

## Summary cards

| Candidate simplification | What is proved or assumed mechanically | Conclusion and omission boundary |
| --- | --- | --- |
| Finite remembered auxiliary-channel abstraction | Replay channel marginal constant on each source decision fiber; original source menus/transitions/payoffs; bounded chance processing | Paper theorem: every source SE has exact preserving SE, with one common consistency sequence and whole continuation rationality |
| Hidden-state source-public scheduler with private garblings | Joint runtime kernels read recoverable public source past; observed private/public views remember the complete relevant record | Paper corollary: correlated receipts and learned runtime state can be ignored by a preserving policy; no coalition or all-target-equilibrium claim |
| Secret-dependent receipt | Source-hidden bit becomes known before a decision | Complete finite negative: no preserving SE, action-law TV 1/2 |
| Per-record rather than full-record ancillarity | Each of X,Y is uniform but their remembered pair reveals the hidden bit | Complete finite negative: marginal packet tests alone do not suffice |
| Independent fee state | Receipt predicts a source-action-dependent monetary cost | Complete finite negative: secrecy alone cannot abstract away costs |
| Anticipated source chance | Pre-choice receipt predicts a later source coin while its unconditional law stays the same | Complete finite negative: decision-prefix Bayes agreement and honest initialized-law agreement do not suffice |
| Independent availability state | Receipt predicts loss of an original source action | Complete finite negative: sure bounded delay differs from uncertain opportunity |

The source language can remain abstract about runtime observations when these
two operational questions have answers: what does the *full remembered record*
reveal within a source information set, and what can the runtime state change
in the logical continuation? The details remain in the backend proof. They
do not have to become source-level syntax, and they cannot simply be dropped
from the implementation game.
