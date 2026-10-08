# Preservation targets and robustness for commit–reveal ledgers

Analysis by Codex. This research note separates properties that a ledger
interface might support. It gives finite-game proofs and counterexamples;
it does not change the language, runtime semantics, preservation checklist,
or current implementation. None of its new results is a Lean theorem.

The useful target is a compiler and backend fixed before an equilibrium is
selected. Reliable honest execution, hiding commitments, correct settlement,
and large collateral address different parts of that target. Their
combination requires a proof that covers deviations, off-path information,
and entire continuation policies.

## A source model that retains private state

Let a source program denote a finite extensive-form game with perfect
recall. There are finitely many players, finite action menus, a finite
initial joint private-state distribution, and finite primitive chance
kernels. Each player's observations specify its information partition.
Its remembered private state and earlier observations persist throughout
the sequence of commitments and openings. The joint prior may be
correlated. This model does not replace retained private state by a fresh
independent prior at each phase.

A commitment can bind a value chosen strategically. An opening can disclose
that value or take a lawful source alternative, including withholding when
the source permits it. Failure, abort, and continuation after failure are
part of the source game when specified. An abstract opening need not expose
packet bytes or network polling; it must still specify which logical facts
become known, to whom, and before which subsequent choices.

Let a compiler, backend configuration, and collateral rule assign this
game a target game and a logical terminal readout. The configuration may
depend on the program, its payoff bounds, and declared runtime guarantees.
It is selected before a source equilibrium. A preservation theorem has
the quantifier order

\[
 \forall G\quad\exists\text{ fixed target configuration }T_G\quad
 \forall A\in\operatorname{SE}(G)\quad\exists A'\in\operatorname{SE}(T_G).
\]

The configuration may be supplied by a single uniform construction over a
class of source games. Choosing a different scheduler, admission rule, or
deposit after inspecting the selected assessment proves a weaker claim.
Fixing collateral means fixing its settlement and utility consequences too;
it does not allow an equilibrium-dependent reimbursement.

The target must identify its actual player actions and observations.
Malformed messages, retries, fees, public traffic, and timing choices cannot
be omitted merely because the intended client does not use them. A
restricted interface can be a legitimate research model, but its relation
to the available physical interface remains a separate obligation.

## Four preservation questions

Write \(Q_A\) for the source logical terminal law, and \(Q'_{A'}\) for the
target logical terminal law after erasing runtime details.
The designated comparison includes the joint initial private parameters
and the declared logical results, unless a result explicitly studies a
coarser projection. Its readout is fixed before the equilibrium too.
Matching an unconditional output distribution by resampling hidden state
does not establish this joint correspondence.

| Question | Quantification and required conclusion |
| --- | --- |
| Selected-outcome implementation | Every source SE assessment has some target SE with \(Q'_{A'}=Q_A\). |
| Reflection of all equilibria | Every target SE outcome equals the outcome of some source SE. |
| Copying an assessment | Retained target strategies equal the selected source strategies, and target beliefs project to source beliefs at every corresponding information set; new sites receive a consistent, rational completion. |
| Consistent approximate preservation | Every source SE admits target assessments with exact global consistency, small whole-continuation regret, and small logical-law and utility error. |

Copying an assessment is stronger than selected-outcome implementation when
the comparison includes the same initialized logical outcome. Literal
copying can be inappropriate if a target information set contains new
physical histories or if several target copies have to use small prescribed
trembles. Reflection and forward implementation are separate directions.
Neither follows from the other.

For weak PBE, beliefs satisfy Bayes' rule at positive-probability information
sets and sequential rationality everywhere. At unreached sites they need
not arise from one common tremble sequence. Here **SE** means ordinary
Kreps–Wilson consistency plus sequential rationality. **Nash** requires only
initialized whole-policy optimality. In a finite perfect-recall game, an SE
is a weak PBE and a Nash equilibrium; preserving some target Nash outcome
does not establish the target's off-path credibility.

The single immutable-disclosure result in
[full-public-disclosure-phase-preservation.md](../full-public-disclosure-phase-preservation.md)
has a particularly strong source quantifier: every source Bayesian Nash
outcome is implemented by a target SE under its stated hypotheses. It
does not establish the corresponding result for strategically selected
commitment values or a sequence retaining old hidden state.

The exact public-delay construction in
[public-scheduling-se-preservation.md](../public-scheduling-se-preservation.md)
is a useful separate positive target. Its waits are chance moves, preserve
the source menus and payoffs, and depend only on recoverable source-public
history. It permits correlated adaptive public delays and retained private
state. A raw timing action, risky admission decision, or extra revelation
requires another argument.

## Compare logical outcomes and utility costs separately

A useful approximation specification supplies three numbers:

- logical outcome error \(e\), measured by total variation;
- sequential incentive error \(r\), measured in utility units;
- utility fidelity error, measured by an explicit coupling or expected
  absolute payoff difference, rather than automatically by payoff-law TV.

Physical completion and logical failure need distinct readouts if the
runtime can stop before producing a complete logical outcome. Gas costs,
delay discounting, locked-capital costs, and collateral charges belong in
the target utility model. Erasing them from the logical readout does not
erase their effect on incentives.

**Proposition: payoff-law TV is discontinuous under harmless fees.** Consider
any one-terminal game with source payoff zero. Its implementation has the
same logical terminal and charges a deterministic fee \(\varepsilon>0\).
The logical-law error is zero, but

\[
 d_{\rm TV}(\delta_0,\delta_{-\varepsilon})=1.
\]

Indeed, the event containing only zero has probability one and zero in
these two payoff laws. Nevertheless the expected absolute payoff error,
under the unique coupling, is exactly \(\varepsilon\). The fee does not
change any strategic choice because there is none. Thus even exact
logical preservation and negligible utility error cannot imply small TV
distance between numerically different realized-payoff distributions.

More generally, suppose source and target share a finite logical terminal
space, their logical laws are within \(e\), and their terminal payoff
functions obey

\[
 \max_z|u_i'(z)-u_i(z)|\le\eta_i,
 \qquad \max_z u_i(z)-\min_z u_i(z)\le W_i.
\]

A maximal coupling of their logical terminals has mismatch probability at
most \(e\). On matching terminals payoff discrepancy is at most \(\eta_i\);
on any pair it is at most \(\eta_i+W_i\). Consequently

\[
 \mathbb E|u_i'(Z')-u_i(Z)|\le \eta_i+W_i e.
\]

This also bounds the difference in expected payoffs and the corresponding
Wasserstein distance on the real line. If utilities depend on additional
physical records, the premise must instead supply a coupling bound for
those actual records. A bound only on logical labels cannot control an
unbounded fee or delay bill.

## Small exact results and counterexamples

### Tiny fees can remove a selected exact equilibrium

**Proposition, paper proof.** A one-player game offers actions \(A,B\), with
source payoff one for either. Every mixture is a source SE, weak PBE, and
Nash equilibrium. Fix the target interface in advance and charge fee zero
for \(A\), fee \(\varepsilon>0\) for \(B\). Its unique exact equilibrium
chooses \(A\). Its logical-law TV distance from the selected pure-\(B\)
source equilibrium is one for every \(\varepsilon>0\).

The proof is the strict comparison \(1>1-\varepsilon\). The pure-\(B\)
target policy is nonetheless an exactly consistent assessment with
whole-policy regret \(\varepsilon\) and logical-law error zero. There is
only one information set, so no belief issue is concealed.

The example applies to action-dependent costs, not to a common unavoidable
constant fee. It shows why a theorem preserving **every selected** exact
source equilibrium needs more than vanishing utility perturbations.
A transport-noise version with an actual opening and lawful withholding
is proved in
[probabilistic-runtime-preservation.md](../probabilistic-runtime-preservation.md).
These counterexamples leave some other source equilibrium implementable;
they do not assert absence of target equilibria.

### Honest initialized fidelity does not control sequential incentives

**Proposition, paper proof.** Nature draws \(\theta\in\{0,1\}\), with
\(\Pr(\theta=1)=9/20\). A sender knows \(\theta\), chooses Out or In, and
gets zero from Out. After In a receiver chooses Accept or Reject. Sender
payoff is one from Accept and minus one from Reject. Receiver payoff from
Accept is one at \(\theta=1\), minus one at \(\theta=0\); Reject gives zero.
In the source, the receiver does not learn \(\theta\).

Both sender types choosing Out and the receiver choosing Reject is a source
SE. To prove consistency, let each type choose In with the same positive
tremble rate. The receiver posterior remains \(9/20\), so Accept has
expected payoff \(-1/10\), strictly below Reject. Add fully supported
receiver trembles tending to Reject. In the limit, each type strictly
prefers Out to the payoff minus one from In. This is one global
consistency sequence.

Now modify the interface so that In truthfully discloses \(\theta\) before
the receiver acts. The all-Out initialized logical law is unchanged under
the same prescribed sender policy. But at the receiver's singleton
\(\theta=1\) site, sequential rationality requires Accept. Type one then
strictly prefers In to Out. No target SE or weak PBE implements the
all-Out law. A Nash profile can still support all-Out by threatening Reject
at both unreached receiver sites; that threat is not sequentially rational.

Thus selected on-path transcript equality is insufficient even when the
interface only reveals a truthful fact after a legitimate source action.
This is a general abstraction boundary, not an assertion that the current
compiler exposes such a fact. A retained correlated private cell requires
fidelity at legal off-path actions too.

A chance-only version is even smaller. A player chooses Out for zero or
In followed by a lottery paying either one or minus one. Source In always
pays minus one; target In always pays one. Honest Out execution agrees
exactly, but its source equilibrium disappears. The chance kernel at the
legal off-profile In history changed by order one.

### Extra public randomness separates implementation from reflection

**Proposition, paper proof.** Two players choose \(A\) or \(B\) without
seeing the other's action. Each gets one if their actions match, zero
otherwise. Model this as player one acting first and player two at an
information set hiding player one's action. Source SE outcomes are those
of the Nash equilibria: pure \((A,A)\), pure \((B,B)\), or the independent
half-half mixture, whose mismatch probability is one half.

Add a fair public coin before either choice and let both copy the coin.
At each coin value this is a strict matching continuation equilibrium, so
the target profile is an SE. Fully mixed action trembles tending to the
prescribed matching actions supply a common consistent assessment.
Its outcome law places probability one half each on \((A,A)\) and \((B,B)\),
with no mismatches. No source SE has that law.

All source SE outcomes can still be implemented by ignoring the coin.
Thus harmless public scheduling randomness can preserve every selected
source outcome while introducing additional target equilibrium outcomes.
Reflection would require treating such public coordination as part of the
source, permitting an explicitly broader source equilibrium concept, or
establishing a stronger restriction on target behavior.

### Conditional error needs a reach-probability denominator

**Lemma, paper proof.** For probability laws \(P,Q\), event \(E\), and
\(Q(E)=b>0\), if \(d_{\rm TV}(P,Q)\le e\) and \(P(E)>0\), then

\[
 d_{\rm TV}(P(\cdot\mid E),Q(\cdot\mid E))\le 2e/b.
\]

For any \(B\subseteq E\), subtract normalized event probabilities, first
using denominator \(b\). The difference is at most
\(|P(B)-Q(B)|/b+P(B)|b-P(E)|/(P(E)b)\le2e/b\).
Taking the supremum gives the bound.

The denominator is substantive. Let \(Q(a)=b,Q(c)=1-b\), where
\(E=\{a,d\}\). Move mass \(e\le b\) from \(a\) to \(d\) to obtain \(P\).
Their unconditional TV distance is \(e\); their conditional TV distance
at \(E\) is exactly \(e/b\). Taking \(e=b\to0\) gives conditional
distance one under arbitrarily small unconditional perturbations.

In an equilibrium argument, \(b\) can be a player-tremble reach
probability rather than an exogenous probability. An estimate for honest
initialized execution cannot simply be reused as the same estimate at
every off-path information set.

## Primitive uniform guarantees and approximate SE

The following reuses the proof in
[noisy-runtime-approximate-se-preservation.md](../noisy-runtime-approximate-se-preservation.md)
and adds an explicit bounded payoff-perturbation term. It is a finite-game
paper theorem, conditional on a structural game adapter in a concrete
ledger application.

Fix one finite full extensive-form tree with perfect recall, unchanged
player ownership, information sets, action menus, and terminal labels.
Let chance kernels be \(p_0,p_n\). Histories compatible with \(p_0\) are
those whose chance-edge product is positive; **every legal player choice**
is allowed in this definition. Pruning chance-impossible histories gives
the source game; targets may make some formerly impossible chance
branches reachable. Perfect recall holds on the full tree, including
these new branches. New physical choices at an existing information set,
changed observation partitions, or an unbounded retry tree are not included
in this theorem.

Assume there are at most \(L\) chance moves per path and

\[
 \delta_n=\max_{h\text{ compatible with }p_0}
 d_{\rm TV}(p_n(\cdot\mid h),p_0(\cdot\mid h))\to0.
\]

The maximum runs over compatible chance nodes, including nodes reached
after deviations. Kernels after a first newly enabled chance branch may
be arbitrary. Let source payoffs on the full tree have range \(W_i\),
and assume \(\max_z|u_i^n(z)-u_i^0(z)|\le\eta_{i,n}\to0\).
Bounds cover formerly impossible terminal outcomes. A deposit growing
without bound as \(n\) increases needs a different estimate.

**Theorem: consistent approximate preservation.** For every source SE
assessment, there are target assessments with exact consistency and
vanishing whole-continuation sequential regret. Their copied strategies
and beliefs converge to the selected source assessment and their logical
terminal laws converge in TV. The construction gives zero regret at
genuinely new information sets. Utilities satisfy a coupling error bound;
realized-payoff-law TV is asserted only when the payoff readout is unchanged.

Here is the construction and bound. Choose a source fully mixed consistency
sequence \((\sigma^k,\mu^k)\) approaching the selected SE. Let \(r_k\to0\)
be its maximum whole-policy regret and \(m_k>0\) its minimum copied-site
reach probability. Choose \(k(n)\to\infty\) slowly so
\(\delta_n/m_{k(n)}\to0\). Source regret tends to zero by continuity of
the finitely many pure continuation-plan comparisons; these trembles
themselves need not be rational.

Freeze every copied player lottery at \(\sigma^k\) as chance, preserving
the original owner's observed action and recall record. Choose an SE
of the resulting finite auxiliary game at genuinely new decisions, using
the target payoff functions. Perfect recall implies that after a player
acts at a genuinely new information set, it cannot later act at a copied
one: every history at the latter would remember the earlier own new
decision, contradicting its having a compatible source history.
Therefore an auxiliary whole-policy best response at a new site is also
a target whole-policy best response there.

Reinsert the fixed positive copied lotteries into the auxiliary SE's
fully mixed sequence. This is one full target consistency sequence.
Copied sites have positive target reach for sufficiently small noise;
give them their actual Bayesian beliefs. Coupling source and target until
the first changed chance outcome gives mismatch probability at most
\(L\delta_n\), uniformly over all prescribed or deviating continuation
policies. No independence between opportunities is required.
Copied beliefs are consequently within \(2L\delta_n/m_k\) of \(\mu^k\).

Compare a target continuation policy directly to its restriction on
compatible source histories, not to the frozen auxiliary policy. For each
player the resulting bound is

\[
 \operatorname{Regret}_n(I)
 \le r_k+2\eta_{i,n}
       +2W_i\left(2L\delta_n/m_k+L\delta_n\right)
\]

at copied sites. Target-only actions can influence this comparison only
after a coupling mismatch. If \(e_k\to0\) is the logical-law difference
between source tremble \(\sigma^k\) and the selected source policy, then

\[
 e_n^{\rm logical}\le L\delta_n+e_{k(n)},\qquad
 \mathbb E|u_i^n(Z_n)-u_i^0(Z_0)|
 \le \eta_{i,n}+W_i(L\delta_n+e_{k(n)}).
\]

These bounds prove the claim. Every target assessment is exactly
consistent, rather than merely close to a Bayes equation. Its rationality
is approximate in utility units at every information set, including sites
off path under its own prescribed policy.

This argument retains the source's entire correlated private-state
structure. No phase reset is used. It does not establish preservation under
an arbitrary new raw interface; one must first construct the fixed finite
tree and information adapter. Applying it to service noise in a backend
whose full interface already preserves SE is a useful conditional route.

There is also a simpler initialized comparison. Under these hypotheses,
any extension of a source Nash profile to new sites has target Nash regret
at most \(2\eta_{i,n}+2W_iL\delta_n\). Prescribed and unilateral-deviation
payoffs each differ from the source comparison by at most
\(\eta_{i,n}+W_iL\delta_n\). This bound requires no conditional denominators,
but supplies neither consistent beliefs nor sequential credibility.

## When can an exact equilibrium survive small perturbations?

Small primitive errors do not imply that every selected source SE has a
nearby exact target SE. The one-player tie example disproves that claim
already. Robust incentives can support a stronger conclusion, but a
margin must specify which decision, policy, and conditional law it covers.

**Proposition: strict backward-induction stability.** Fix a finite
perfect-information full tree, including all chance branches, and a pure
source policy \(s\). At every player decision node, suppose its prescribed
action has payoff advantage at least \(\gamma>0\) over each other action,
when all subsequent player decisions follow \(s\). This condition is
required at every node of the full tree, even a node having zero initial
source chance probability. Let all source terminal payoffs have ranges
at most \(W\). Suppose every chance kernel changes by TV at most
\(\delta\), every terminal payoff changes by at most \(\eta\), and paths
have at most \(L\) chance moves. If

\[
 2(WL\delta+\eta)<\gamma,
\]

then \(s\) is still the unique backward-induction policy at every legal
target player node. It is a target SE and has logical-law error at most
\(L\delta\).

**Proof.** Under fixed continuation policy \(s\), each action's payoff at
each decision node changes by at most \(WL\delta+\eta\), by the same
coupling and payoff estimate. Every prescribed-versus-alternative gap
remains positive. Backward induction first establishes \(s\) at terminal
decisions, then at each predecessor because all later decisions already
use \(s\). Singleton beliefs are unique. Fully mixed trembles converging
to \(s\) establish consistency. The terminal coupling gives the law bound.

This is a sufficient condition, not a necessary interface characterization.
It avoids the correlated-belief problem by restricting to perfect
information. An imperfect-information extension must control posterior
changes, mixed support equalities, and off-path completion as well as
utility margins. A root strict Nash inequality alone does not do that.

## An asymptotic reflection theorem with fixed chance support

There is a useful converse continuity statement even though forward
preservation of each selected exact equilibrium fails.

**Theorem, paper proof.** Fix a finite perfect-recall tree, ownership,
information partition, and action menus. Source and target chance kernels
have exactly the same positive support. On each retained chance edge,
source probability is at least \(\kappa>0\). Suppose nodewise chance-TV
error \(\delta_n\to0\) and terminal payoff functions converge uniformly.
Every limit point of target SE assessments is a source SE. Hence every
converging sequence of target SE logical laws has a source SE limit law.

**Proof.** For \(\delta_n<\kappa\), each chance-edge probability ratio
between target and source lies between \(1-\delta_n/\kappa\) and
\(1+\delta_n/\kappa\). For the same fully mixed behavioral player profile,
each history likelihood ratio lies between

\[
 a_n=(1-\delta_n/\kappa)^L,
 \qquad b_n=(1+\delta_n/\kappa)^L.
\]

Player factors cancel, even if the profile reaches an information set only
with extremely small probability. Normalizing over an information set
changes the ratio bound to \([a_n/b_n,b_n/a_n]\). Thus source and target
Bayesian beliefs under that same profile differ by a quantity tending to
zero uniformly over all fully mixed player profiles and information sets.

Take a convergent subsequence of target SE assessments. For its \(n\)-th
member, select a sufficiently close fully mixed consistency witness in
that target. Evaluating the same witness under source kernels changes
its Bayesian beliefs by only the uniform error just obtained. These source
full-mix witnesses converge to the limiting assessment, proving source
consistency. Sequential rationality follows by continuity of each of the
finitely many pure whole-continuation-plan comparisons in strategies,
beliefs, kernels and payoffs. Terminal-law continuity proves the outcome
claim. Compactness of the finite assessment space supplies limit points.

**Uniform corollary.** For any fixed norm on this finite assessment space,

\[
 \sup_{A_n\in\operatorname{SE}(G_n)}
 \inf_{A\in\operatorname{SE}(G_0)}\|A_n-A\|\longrightarrow0.
\]

Otherwise select a sequence of target SEs staying at least a fixed positive
distance from the source SE set. Compactness supplies a convergent
subsequence, and the theorem places its limit in that closed source set,
a contradiction. Uniform terminal-law continuity also yields

\[
 \sup_{A_n\in\operatorname{SE}(G_n)}
 \inf_{A\in\operatorname{SE}(G_0)}
 d_{\rm TV}(Q^{(n)}_{A_n},Q^{(0)}_A)\longrightarrow0.
\]

This uniformly reflects all target equilibria approximately into the source
equilibrium set. It is still one-sided: the distance from an individually
selected source equilibrium to the target equilibrium set can remain
positive, as the tiny-fee counterexample shows.

The theorem is upper hemicontinuity, or reflection of limit points. It is
not exact reflection at each positive noise level, and does not choose a
nearby target SE for each selected source SE. It requires fixed support;
the approximate preservation construction above permits new chance support
and uses slow source trembles precisely where this uniform likelihood-ratio
argument is unavailable. Nor does it cover extra public randomness that
splits information sets, as in the coordination counterexample.

## Strict pure SE with retained private information

The fixed-support likelihood estimate also supplies an imperfect-information
exact-equilibrium stability result. It retains correlated private state;
it does not require perfect information or resetting a phase's prior.

**Theorem, paper proof.** Fix a finite perfect-recall extensive-form tree
with the same players, node ownership, action menus, information partition,
and terminal labels in source and target. Source and target have the same
positive chance edges, and each source chance-edge probability is at least
\(\kappa>0\). At every chance node the target kernel differs from the source
by TV at most \(\delta_n\to0\); paths have at most \(L\) chance moves.
Terminal payoff functions differ uniformly by at most \(\eta_n\to0\).
Let \((s,\mu)\) be a source SE whose behavioral policy is pure.
At every information set, assume
the prescribed action has conditional advantage at least \(\gamma>0\)
over every alternative action, when the player subsequently follows \(s\).
Let \(W\) bound all source payoff ranges, \(\eta_n\) bound the uniform
terminal-payoff error, and set, for \(\delta_n<\kappa\),

\[
 a_n=(1-\delta_n/\kappa)^L,\quad
 b_n=(1+\delta_n/\kappa)^L,\quad
 C_n=b_n/a_n-1\longrightarrow0.
\]

If \(2[\eta_n+W(C_n+L\delta_n)]<\gamma\), then there is a target SE
\((s,\mu_n)\) using exactly the same pure policy, with
\(d_{\rm TV}(\mu_n(I),\mu(I))\le C_n\) at every information set.
Its logical-law error is at most \(L\delta_n\).

**Proof.** Take one source fully mixed consistency sequence approaching
\((s,\mu)\). For fixed \(n\), evaluate this entire sequence under target
chance kernels. A subsequence of its finite vector of Bayesian beliefs
converges to some \(\mu_n\). Hence \((s,\mu_n)\) is exactly target-consistent.
The history likelihood-ratio estimate, uniform over strategic tremble rates,
proves the stated distance to \(\mu\).

For each information set and each initial action followed by \(s\), changing
the starting belief contributes at most \(WC_n\), subsequent chance kernels
at most \(WL\delta_n\), and terminal payoffs at most \(\eta_n\). Comparing
two actions doubles this bound, so all prescribed one-action advantages
remain strictly positive.

In a finite perfect-recall game, these local comparisons with a consistent
assessment imply whole-continuation optimality. The reason consistency is
needed can be made explicit. Under a fully mixed witness, perfect recall
makes the owner's past action factors common within each future owned
information set. Its conditional beliefs there therefore do not change
when replacing its earlier policy while holding others fixed. Bayesian
updating along a positive-probability continuation permits backward
replacement of the last deviating decision, then the previous one.
Taking the consistent limit establishes the same one-shot-deviation
principle at zero-reach sites. Equivalently, near the limit the finitely
many strict action inequalities persist; replacing the owner's future
trembled lotteries by the prescribed pure policy has vanishing effect
on each conditional action value. Finite backward optimization against
the other players' fully mixed policies then proves optimality of that
pure policy, and continuity gives the limiting whole-policy comparison.

Thus \((s,\mu_n)\) is sequentially rational as well as consistent. The
uniform terminal coupling proves its logical-law bound.

The conclusion is an **exact target equilibrium with a nearby law**;
it is not exact equality of outcome laws under changed chance kernels.
The strict margin is required at every information set, not only the root
or the selected equilibrium path. Mixed source SEs have support
indifferences, and this theorem supplies no stability claim for them.
Arbitrary weak-PBE beliefs would not justify its one-shot-deviation step.

## Relation to computational extensive-form representation

Halpern, Pass and Seeman define representations of finite games by
computational game sequences. Their definition preserves history length,
actor order and terminal utility; it requires lifted source profiles and
simulation of polynomial-time unilateral deviations. Theorems 4.2 and 4.6
transfer source Nash and SE respectively. Their computational SE uses
computationally appropriate partitions and negligible deviation-dependent
utility losses, rather than ordinary SE on the literal string-information
partition. Forward transfer does not imply converse reflection.
These conditions are especially relevant to hiding commitments.
[Computational Extensive-Form Games, definitions 3.3 and 4.5, theorems 4.2 and 4.6](https://arxiv.org/html/1506.03030).

For this project, the research question is whether a ledger adapter can
establish analogous representation facts while explicitly accounting for
its physical interface. A pending opening readable before acceptance is
an efficiently observable event. A deadline, a fee choice, a missed receipt,
and a new opportunity to signal may change the game before anyone attempts
to break cryptography. Computational hiding of the earlier commitment does
not remove those events. Mapping several physical actions to one logical
step would require a different structural adapter from literal same-length
representation. Costs also need their own utility fidelity argument.

That observation does not rule out a computational preservation theorem.
It places cryptographic indistinguishability alongside scheduling,
observation, deviation simulation and utility fidelity. Ordinary ideal
finite SE, finite consistent approximate SE, and computational SE should
remain distinct research targets. Efficient players may be the appropriate
model for actual commitments, while the finite ideal game remains useful
for high-level strategic analysis.

## Candidate targets and catalog cards

These are useful separate projects; none is asserted to be the uniquely
minimal ledger interface.

| Candidate | Target and available argument | Remaining ledger obligation |
| --- | --- | --- |
| Exact public delay | Every selected source SE, including retained correlated private state, has a copied target assessment under the existing public scheduling construction. | Show physical scheduling adds no retained player timing choice or private-state signal, and preserves menus and utilities. |
| Noisy finite service | Every selected source SE has exactly consistent target assessments with vanishing whole-policy regret and logical-law/utility error. Paper proof above. | Construct the common finite tree, recall and information adapter; bound primitive error at every compatible history and actual costs. |
| Robust exact behavior | Strict backward-induction policies, and strict pure SEs with fixed positive chance support, survive small kernel and utility error. Paper proofs above. | Establish conditional margins at every decision and the relevant structure/support hypotheses; mixed source equilibria need another argument. |
| Asymptotic reflection | Target SE limit points are source SE under fixed positive chance support and fixed information. Paper proof above. | Decide whether the physical interface satisfies the fixed-structure premise, or weakens reflection by adding coordination. |
| Computational representation | Transfer rationality against efficient deviations after proving structural, cryptographic and strategic representation. Existing primary-source theorem, not a ledger instantiation. | Model physical transcripts and timing; prove deviation simulation and actual utility fidelity. |

Concise result cards for the research catalog:

1. **Selected exact equilibria are fragile.** Finite one-player tie; an
   \(\varepsilon\) action fee removes one chosen source SE at logical TV
   distance one. Exact-consistent approximate regret is only
   \(\varepsilon\). Status: complete paper counterexample.
2. **Outcome and cost metrics must separate.** Same logical terminal,
   constant fee \(\varepsilon\): logical TV zero, payoff-law TV one,
   expected absolute payoff error \(\varepsilon\). Status: complete proof.
3. **Off-path observation fidelity matters.** The \(9/20\) truthful
   disclosure game has a preserving all-Out Nash profile but no preserving
   weak PBE or SE after disclosure is added. Status: complete paper proof.
4. **Public randomness need not reflect equilibria.** A public coin creates
   a correlated matching outcome absent from the source's SE outcomes while
   preserving all source SE outcomes. Status: complete paper proof.
5. **Approximate SE has a primitive route.** Finite unchanged full tree,
   compatible-history chance error \(\delta_n\), bounded payoff error
   \(\eta_n\), and a slow consistency sequence give exact consistency and
   regret \(r_k+2\eta_n+2W(2L\delta_n/m_k+L\delta_n)\). Status: complete
   paper proof; physical interface adapter remains open.
6. **Exact reflection of limits has a cleaner support condition.** Fixed
   positive chance support makes conditional likelihood ratios uniformly
   close, proving target-SE limit points are source SE. Status: complete
   paper proof; not forward lower hemicontinuity.
7. **Strict pure assessments admit nearby exact SEs.** With fixed positive
   chance support, the source consistency witness yields target beliefs
   within \(C_n\); a global conditional action margin exceeding
   \(2[\eta_n+W(C_n+L\delta_n)]\) preserves the exact pure policy. Status:
   complete paper proof; excludes mixed ties and altered information.

The remaining broad problem is to give a physical commit–reveal interface
whose primitive guarantees justify one or more of these targets while
retaining strategic value choices, correlated hidden state, lawful aborts,
and the actual opportunities to communicate. The existing single-phase
results and scheduling construction supply useful components. They do not
by themselves prove composition for arbitrary ledger interaction.
