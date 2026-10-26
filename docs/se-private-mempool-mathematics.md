# Sequential equilibrium with private mempools: mathematical foundations

Preservation for the current concurrent runtime under private pending
observations remains unproved and unrefuted here. The results below are finite
hand proofs and conditional construction lemmas, not a discharge of that
runtime's information or continuation obligations.

Complete pending observation is not necessary for SE preservation in general.
The private-noise theorem below preserves every selected source SE, including
the entire initialized outcome law, without making any reception public.
Conversely, forgetting observations in an arbitrary fine-information SE can
destroy all equilibria with its outcome, even when its limiting strategy already
ignores those observations.

The constructive route is to work on the actual private information sets.
Conditional error control and simultaneous completion solve two parts of that
construction. Actual continuation incentives remain essential: small probability
of accidental errors does not deter deliberate deviations. The
[compiler and incentive analysis](se-private-mempool-compilation.md) addresses
waiting, penalties, rollback and alternatives with absorbing abort.

These are mathematical proofs, not newly checked Lean results. They do not
establish or refute preservation for the full current concurrent runtime with
only complete observation removed. The [model audit](se-private-mempool-research.md)
identifies the current dependency. Neither a proof's hidden state nor its random
tape is an additional player observation.

| Question | Mathematical conclusion |
|---|---|
| Can private reception preserve SE? | Yes, for source-adapted private-noise overlays, with arbitrary correlated source priors. |
| Can a fine equilibrium simply be projected? | No; its off-path beliefs may require hidden-information-dependent trembles. |
| When do inequalities for every bounded gain function survive a posterior change? | Exactly when the new posterior is a mixture of source information-set posteriors. |
| Must every hidden coordinate be preserved? | No; the actual continuation-gain family can require less. |
| Can rare native errors remain rare at rare private views? | Yes, with regular witnesses and error rates chosen relative to their reach. |
| Must off-path completion occur in public subgames? | No; simultaneous information-agent completion supplies one legal consistency sequence. |
| Is a failed bounded exponent search a refutation? | No; fixed finite rational instances instead admit exact real-algebraic decision procedures. |

## Common finite conventions

All games below have a finite extensive-form tree, fixed chance probabilities,
bounded terminal utilities, and perfect recall. Delete histories made impossible
by zero-probability chance branches. Every remaining information set is therefore
reached with positive probability under every completely mixed behavioral
profile. Every information set is an antichain. A local deviation replaces the
law at one information set by a pure action and retains the prescribed
continuation policy. For perfect recall, nonpositive gains from all such local
deviations give sequential rationality. All convergence is coordinatewise.

Write r_s(h) for the reach probability of history h under profile s. For an
information set I, write r_s(I)=sum_{h in I}r_s(h). A fully mixed profile gives
the Bayes belief mu_s(h|I)=r_s(h)/r_s(I).

## A complete positive class: source-adapted private noise overlays

This theorem preserves a selected source SE, rather than trying to descend an
arbitrary equilibrium from a more informative implementation.

Take a finite perfect-recall source game. Add a finite hidden random variable Z
independent of the entire source chance process, including the initial state;
Z may contain correlated random seeds for different players. It is not public
or jointly observed. For each source history h and player i, let the player's
additional transcript be T_i(h,Z). Require that, whenever h and h' belong to the
same source information set J of player i,

    T_i(h,z) = T_i(h',z) for every z.

Equivalently, the transcript is a function of the player's recalled source
information and the hidden auxiliary seed. The target information at a source
decision consists of the original source information J and this transcript.
Assume the target retains its observations and hence has perfect recall. There
are exactly the same strategic decision opportunities and action menus as in
the source, and target utilities and the selected terminal readout ignore Z.

**Theorem.** Every source SE has a target SE obtained by ignoring the added
transcripts, with exactly the same initialized joint readout law. No independence
between different players' source private inputs is required.

**Proof.** Let (s_n,mu_n) be a common completely mixed source sequence converging
to the selected source SE. Lift s_n to the target by ignoring the transcripts.
These are legal fully mixed target profiles. Because all lifted players ignore
Z, a physical source history h and seed z have joint reach
r_{s_n}(h)P(Z=z). At a target information set I=(J,t), write

    K_I = P(T_i(J,Z)=t).

For an actual target information set K_I>0; impossible signal values can be
pruned. Summing over compatible seeds gives

    P_{s_n}(h and I) = 1_{h in J} r_{s_n}(h) K_I.

Thus the target Bayes posterior, projected to source histories, is exactly
mu_n(.|J), for every n, including source-off-path information sets. At a target
local alternative a, the current action is changed and all future lifted
players still ignore Z. The conditional continuation gain from actual (h,z)
therefore equals the source local continuation gain from h and a. Averaging
gives exactly G_target,n(I,a)=G_source,n(J,a). The finitely many source gains
have upper bounds tending to zero by convergence to source SE. Compactness
provides a common limit of target Bayes beliefs; the strategy limit is the
lifted source strategy. It is consistent by this same fully mixed target
sequence and rational by the gain equality and perfect recall. Marginalizing
out the unused seed leaves the source initialized joint law unchanged. QED.

Within this independent-seed model, the pointwise transcript condition can be
weakened to equality of its conditional law within each J: the proof uses only
the constant factor K_I. The conditional future payoff and transition law under
the lifted continuation still ignores the auxiliary observation because Z is
independent of the entire source chance process and all lifted policies ignore
it. For a more general network overlay that independence argument is no longer
automatic; posterior equality alone does not establish continuation equality.

A concrete instance is private subsampling of a fixed schedule of opaque packet
slots whose visible authors, timing, and contents are already determined by the
observer's source information. Reception noise can be privately correlated
across players and remain entirely absent from the ledger. An arbitrary
initially correlated private-type prior is harmless here. The theorem does not
cover hidden-type-dependent traffic counts or timings, meaningful packet
payloads, extra strategic scheduling actions, aborts, or alternative ledger
orders without additional work. Those are operational adapter obligations,
not shortcomings in SE consistency itself.

## Exactly when posterior mixtures preserve every source inequality

Let a finite set of source histories be partitioned into nonempty source
information sets \(J\). Let \(p(h)>0\) on these histories and put
\(\mu_J(h)=p(h)/p(J)\) for \(h\in J\), zero elsewhere. Let \(q\) be a native
posterior, already projected to these histories. The following are equivalent:

1. \(q=\sum_J w_J\mu_J\) for nonnegative weights summing to one.
2. \(q(h)/p(h)\) is constant on each \(J\).
3. Every function \(f\) satisfying \(\mathbb E_{\mu_J} f\leq0\) for every \(J\)
   also satisfies \(\mathbb E_q f\leq0\).

Proof: (1) implies (2), with ratio \(w_J/p(J)\); (2) implies (1), with the
necessarily unique weights \(w_J=q(J)\). Averaging gives (1) implies (3). If (2)
fails, some \(J\) with \(q(J)>0\) has
\(q(\cdot\mid J)\ne\mu_J\). Choose a subset \(A\subseteq J\) with
\(q(A\mid J)>\mu_J(A)\). Define

\[
 f(h)=\begin{cases}1_A(h)-\mu_J(A),&h\in J,\\0,&h\notin J.\end{cases}
\]

Then every source information set has expected value zero, but
\(\mathbb E_qf=q(A)-q(J)\mu_J(A)>0\). This proves the contrapositive of
(3) implies (2). The separating function lies in \([-1,1]\). If \(q\) instead
charges histories outside the support of \(p\), their indicator separates in
the same way.

Consequently, summing over hidden histories does not automatically make a
posterior a mixture of source Bayes posteriors. It works exactly when the summed
likelihood is constant within each source information set. This is necessary
for transport of **all possible bounded payoff/gain functions**, but not
necessary for transport of the continuation gains of one fixed game. A
separating function is not a runtime counterexample until it is realized by a
legal deviation and payoff in an admissible program, with all service and
enforcement hypotheses retained.

For a fixed game, let \(\mathcal D\) be the actual family of source continuation
gain functions supplied by legal deviation adapters. Equality of expectations
only requires \(q-\sum_Jw_J\mu_J\) to annihilate their linear span. One-sided
preservation requires the corresponding inequalities, which can be weaker
still. The gain family must include the relevant continuation policies and
conditioning sites; matching terminal observables alone does not imply this.

### A finite separating example

Take one source information set with histories \(x,y\), prior \((1/2,1/2)\),
and native posterior \((2/3,1/3)\). The source is indifferent between baseline
payoff zero and an alternative with gain \((1/2,-1/2)\). At the native site the
alternative has gain \(1/6\). There is only one source Bayes posterior, so no
mixture can repair this discrepancy. A game whose two legal actions have these
payoffs realizes the separation; whether such a pair of hidden states and
observation is available in the protected concurrent runtime is a separate
question.

## Exact covariance transport for the actual gain family

Write \(q(h)=p(h)L(h)/Z\), where \(Z=\sum_h p(h)L(h)>0\). For each source site,
put \(m_J=\mathbb E_{\mu_J}L\) and \(w_J=p(J)m_J/Z\). Fix a native information
set \(I\) and a native local alternative \(a\). A usable source adapter must
choose, for each source site \(J\), a **legal source continuation deviation**
\(d_{I,J,a}\), the same for every hidden history in \(J\). A choice depending on
the unknown history would not be an admissible policy.

Let \(D_{J,a}(h)\) be its gain against the prescribed source continuation at
history \(h\). Suppose an actual continuation coupling establishes

\[
 G_N(I,a)=\sum_hq(h)D_{J(h),a}(h)+r_{I,a}.
\]

Then, omitting terms with \(m_J=0\),

\[
 G_N(I,a)
 =\sum_Jw_J G_S(J,d_{I,J,a})
  +\sum_Jw_J\frac{\operatorname{Cov}_{\mu_J}(L,D_{J,a})}{m_J}
  +r_{I,a}.
\]

This is an identity: use
\(\mathbb E(LD)=\mathbb E(L)\mathbb E(D)+\operatorname{Cov}(L,D)\) separately
inside each source site. It exposes three independent obligations: a legal
deviation adapter, control of actual gain covariance, and the continuation
comparison error. A posterior statement without the first and third is not an
SE preservation theorem. In a sequence, the **weighted conditional covariance
sum** needs a uniform upper bound tending to zero; assuming a fixed lower bound
on every small observation probability is unnecessary and often false.

Pairwise antitonicity is a concrete sufficient condition for one covariance:

\[
\operatorname{Cov}_{\mu}(L,D)
 =\tfrac12\sum_{x,y}\mu(x)\mu(y)
       (L(x)-L(y))(D(x)-D(y)).
\]

If every displayed product is nonpositive, the covariance is nonpositive.
However, one-sided covariance should not be oversold. If a source gain has
expectation zero and the requirement is nonpositive gain after **every**
positive-probability observation, the tower property forces every conditional
gain to be zero. A favorable negative covariance at one observation is
compensated elsewhere unless the source has strict slack.

For example, take prior \((1/2,1/2)\), gain \(D=(1,-1)\), and event likelihood
\(L=(1/4,1/2)\). The source gain is zero and the event-conditioned gain is
\(-1/3\). The complementary event has likelihood \((3/4,1/2)\) and gain
\(1/5\). Thus checking only the first event misses a profitable site.

## Operational producers: what private gossip can and cannot preserve

### Fixed traffic whose observable form depends only on source information

Here is a concrete sufficient construction. During a source decision interval,
let the packet slots, authors, timestamps, and routes be fixed by public data.
For a focal player, let the visible content of each packet be determined by that
player's source information \(J\); a packet carrying another player's hidden
choice must instead be observationally opaque to the focal player. At each
prescribed opportunity, sample receipt of each packet with fixed probabilities
that depend only on these public or source-observable data. Use independent
receipt bits, or any fixed joint receipt law with the same invariance. The
focal transcript is a function of \(J\) and these bits. Hence

\[
 \Pr(I\mid h)=K(I\mid J(h)),
\]

and Bayes conditioning gives exactly the mixture in the posterior-mixture theorem. Arbitrary
correlation in the initial prior is allowed: the argument compares observation
likelihoods, not the factorization of the prior.

This construction includes a ledger-only view and private Bernoulli
subsampling of a fixed opaque traffic pattern. It does not include hidden-type
dependent packet counts, timing, payloads, or policy choices without a separate
invariance proof. Independent random coins do not by themselves make the
resulting signal independent: the hidden state may control which coins are
consulted and what their outcomes mean.

A causal version can be proved inductively: states related by the desired
source-information relation must have equal laws of the next observable event
and next related state, under every relevant legal action. Baseline and
deviating actions must be included where continuation transport needs them.
This is a substantive kernel condition. It is not supplied merely by giving
the initial state an independent random seed.

### Gain-relevant summaries can be smaller than full hidden histories

Suppose a finite controlled process has a summary \(T(x)\). Compared states must
also share the same current personal/visible history; equivalently include that
history in the summary. Otherwise the same observation-adapted policy can act
differently on two states with equal summaries. Legal action menus
depend only on the visible history and this summary. For all related hidden
states \(T(x)=T(y)\), and every relevant action \(a\), require equality of the
joint law of

\[
  (T(X_{t+1}),\text{next observation})
\]

under the fixed transition kernel. Require immediate and terminal payoffs to
factor through the summary and visible events as well. Other players' fixed
strategies must be included in that kernel; their hidden-state-dependent
responses cannot be omitted. Backward induction shows that every
observation-adapted continuation policy has the same value at related states:
the terminal case follows from payoff factorization, and the induction step
uses the equal joint transition law and the same admissible action rule.
Therefore every continuation gain is a function of the summary.

If a private observation preserves the source conditional law of this summary,
it preserves all those gain expectations even if it changes the posterior on
irrelevant archive coordinates. This is a genuine weakening of full-history
likelihood proportionality. It requires closure under controlled transitions
and future observations, not just a finite list of terminal moments.

### Absence is informative even with content-blind packet sampling

Let a hidden bit \(X\) be fair. There is one packet if \(X=0\) and two if
\(X=1\). Each is independently received with fixed probability \(q\),
\(0<q<1\). After receiving no packet,

\[
 \Pr(X=1\mid\text{none})
 =\frac{(1-q)^2}{(1-q)+(1-q)^2}
 =\frac{1-q}{2-q}.
\]

For \(q=1/2\), this is \(1/3\), not \(1/2\). The rule never examines packet
content; hidden counts suffice. This disproves the implication from
content-blind reception to general likelihood invariance. It does not by
itself refute the concurrent preservation theorem, because its regular
traffic may prohibit the hidden-dependent count pattern.

## Exact common-sequence descent

Here the fine and coarse games share the physical histories, player to move,
chance laws, menus, utilities and desired initialized terminal record. Every fine
information set J lies within a coarse set I, with a common menu throughout I.
Both partitions have perfect recall; arbitrary merging need not preserve it.

**Theorem.** Suppose s_n are completely mixed coarse behavioral profiles, lifted
to fine profiles by assigning the same law at every J contained in I. Suppose
their fine Bayes assessments converge to a fine sequential equilibrium
(s,mu^F). Then some subsequence of their coarse Bayes assessments converges to a
coarse sequential equilibrium (s,mu^C). Its full physical terminal law, and hence
every chosen initialized joint readout law, equals the law of the fine profile s.

It suffices more generally that all fine local deviation gains at index n are
at most eta_n, uniformly over sites and pure actions, with eta_n tending to zero;
an already established fine limit assessment is not required in that formulation.

**Proof.** For a coarse set I and a fine set J contained in I, define

    w_n(J|I) = r_{s_n}(J)/r_{s_n}(I).

The fine sets partition I, so these numbers are nonnegative and sum to one.
For h in J,

    mu^C_n(h|I) = w_n(J|I) mu^F_n(h|J).

Fix a common legal action a. From an actual h in J, a local deviation at coarse I
and a local deviation at fine J generate identical future play: they both choose
a now and use the original profile thereafter. Neither can revisit any history
in I, by the antichain condition. Thus the conditional gain satisfies exactly

    G^C_n(I,a) = sum_{J contained in I} w_n(J|I) G^F_n(J,a).

This identity concerns one common physical profile s_n. It does not compare
Bayes beliefs computed under two different profiles.

The space of all finite belief systems is compact, so take one subsequence on
which every coarse Bayes belief converges. The strategy limit s is coarse legal
because equality of the fine strategy coordinates on each I is closed. Fine
sequential rationality at the limit and continuity of the finitely many gain
functions imply eta_n=max(0,max_{J,a}G^F_n(J,a)) tends to zero. The displayed
identity gives G^C_n(I,a)<=eta_n. Passing to the common subsequential limit gives
nonpositive coarse local gains. Perfect recall gives sequential rationality.
Consistency uses this same sequence of completely mixed coarse profiles.
Finally, fine and coarse interpretations of s assign identical probabilities
to every physical move, so their terminal laws agree exactly. QED.

The whole-sequence coarse legality is a sufficient construction hypothesis. It
is not a necessary condition for the existence of some preserving coarse SE:
a different consistency witness or a direct coarse construction can suffice.
Merely knowing the limiting fine strategy is coarse legal, however, is false as
a replacement hypothesis, even when all on-path information lost is irrelevant
to the limiting actions. The next example isolates why.

## Limit legality alone: a complete counterexample

Fix any p with 0<p<1/2. Nature chooses theta in {0,1}, with P(theta=0)=p.
Player 1 observes theta in the fine game and chooses Out or In. Out terminates
with both payoffs zero. After In, player 2, who does not observe theta, chooses
A or B. Player 1 receives -1 after A and +1 after B, regardless of theta.
Player 2 receives one for correctly guessing theta (A guesses 0, B guesses 1)
and zero otherwise. In the coarse game only player 1's theta information is
removed. Both are finite perfect-recall games with identical action menus.

The fine profile s is Out at both of player 1's sites and A at player 2's site.
It is coarse legal. For 0<epsilon<1, take the completely mixed profile

    P_epsilon(In | theta=0) = epsilon,
    P_epsilon(In | theta=1) = epsilon^2,
    P_epsilon(A | In) = 1-epsilon.

Bayes' rule at player 2 gives

    P_epsilon(theta=0 | In)
      = p / (p+(1-p)epsilon) -> 1.

At the limit, player 2 strictly prefers A. At either of player 1's fine sites,
In then yields -1 while Out yields zero. Consequently the fine limit assessment
is an SE. Its initialized outcome law is theta distributed according to p and
Out with probability one. The finite-epsilon profiles need not be equilibria;
they are a legal common consistency witness, which is all SE consistency needs.

For complete clarity, at finite epsilon player 1's In-versus-Out payoff
difference equals -1+2epsilon, hence is negative for epsilon<1/2. The local gain
from forcing In instead of its current mixed law multiplies this difference by
the current Out probability. Player 2 prefers A whenever
epsilon<p/(1-p). This is stronger than needed for the limit argument.

Now consider *any* completely mixed coarse profile. Let x>0 denote the single
probability of In at player 1's coarse information set. At player 2,

    P(theta=0 | In) = px/(px+(1-p)x) = p.

Therefore every consistent coarse assessment, under any consistency sequence,
has posterior p at that site. Since p<1/2, player 2 strictly prefers B. Under B,
player 1 strictly prefers In. Every coarse SE thus plays In and B with
probability one. Such an SE exists, for example using any ordinary uniform
trembles converging to In/B. No coarse SE preserves the fine equilibrium's Out
law. The obstruction is the forced off-path posterior, not lack of a legal
coarse limiting strategy. The fine strategy is even a coarse Nash equilibrium;
its off-path threat is what consistency rules out.

## An input-preserving version, and exactly what it does not refute

The preceding example forgets an original private input. To avoid that feature,
introduce a sender S whose original private input is theta in *both* models and
whose utility is always zero. After seeing theta, S chooses E or L. Player 1
observes this additional signal in the fine model and receives no signal in the
coarse model. Neither model gives player 1 theta as an original private input.
Player 2 observes only whether player 1 chose In, as before. The original input
ownership of every player is unchanged. S's choice can be represented as a
temporary communication observation that leaves the same eventual public
record in either case; an abstract example is one fixed marker delivered early
or late, followed by one fixed public inclusion. This is an information-tree
construction, not a claimed Vegas queue/ledger realization: ordering, legal
response menus, and timing visibility would need a separate runtime audit.

The fine limiting profile has S choose E at theta=0 and L at theta=1, player 1
choose Out after either signal, and player 2 choose A. Use the following common
fully mixed witness:

    P_epsilon(E | theta=0) = 1-epsilon^3,
    P_epsilon(E | theta=1) = epsilon^3,
    P_epsilon(In | E) = epsilon,
    P_epsilon(In | L) = epsilon^2,
    P_epsilon(A | In) = 1-epsilon.

The two masses of reaching player 2 are

    P_epsilon(theta=0,In) = p epsilon(1-epsilon^3+epsilon^4),
    P_epsilon(theta=1,In) = (1-p)epsilon^2(1+epsilon^2-epsilon^3).

Their theta=1/theta=0 ratio tends to zero. Therefore player 2's limiting belief
assigns theta=0 probability one. S is indifferent at every site; player 1
strictly prefers Out at both signal sites; player 2 strictly prefers A. The fine
assessment is an SE, witnessed by exactly the displayed legal fully mixed
sequence. For a simple explicit finite bound, if 0<epsilon<=1/2, then the ratio
is at most (10/7)((1-p)/p)epsilon. Thus epsilon<min(1/2,7p/(10(1-p))) ensures
player 2 already prefers A; player 1's finite-epsilon In-versus-Out payoff
difference remains -1+2epsilon.

In every completely mixed coarse profile, player 1 has one In probability x,
independent of theta and S's choice. Summing over S's choice gives
P(theta=0,In)=px and P(theta=1,In)=(1-p)x. Every consistent coarse assessment
again gives player 2 posterior p. Hence every coarse SE plays In/B. This refutes
automatic descent of arbitrary fine SE even when the only forgotten observation
is an extra communication signal and every original input remains available.

It does *not* refute preservation of an equilibrium selected from the original
source game. If the source is the game without the extra signal, its equilibrium
is already In/B; the coarse target realizes it. The fine Out/A equilibrium is a
new equilibrium sustained by the additional signal and its type-dependent
trembles. A theorem that begins with a selected source SE and constructs its
coarse implementation can avoid this counterexample. Thus two questions must
remain separate: whether arbitrary fine equilibria descend, and whether the
source equilibria of interest admit a coarse implementation.

## A weaker constructive hypothesis: relative closeness of trembles

Exact coarse legality at every index is stronger than necessary even for a
transfer argument using an existing fine consistency witness.

**Theorem.** Let s_n be completely mixed fine profiles whose fine Bayes
assessments converge to a fine SE (s,mu). Suppose

    d_n = max_{i,I,J,K contained in I,a}
            |log(s_n(a|J)/s_n(a|K))| -> 0.

Choose one representative J_I in each coarse I and define a coarse profile
t_n(a|I)=s_n(a|J_I). Then a subsequence of the coarse Bayes assessments of t_n
converges to a coarse SE with limiting strategy s and the same terminal law.

**Proof.** The t_n are legal fully mixed distributions, since each is copied
from an actual fine information set with the same action menu. Let H be an upper
bound on the number of player decisions along a history. At every such decision
the t_n/s_n action-probability ratio lies in [exp(-d_n),exp(d_n)]. Chance factors
are identical. Multiplication gives, for every supported history h,

    exp(-H d_n) <= r_{t_n}(h)/r_{s_n}(h) <= exp(H d_n).

Summing gives the same bounds for each information-set reach probability.
Dividing shows that the fine Bayes belief ratio at any fine information set
lies in [exp(-2H d_n),exp(2H d_n)]. Hence the L1 distance of the fine beliefs is
at most exp(2H d_n)-1, uniformly over fine information sets. Strategy coordinate
differences also tend to zero. The fine Bayes assessments of t_n therefore
converge to the same fine SE (s,mu). Apply exact common-sequence descent to t_n.
QED.

Absolute strategy distance is insufficient: epsilon and epsilon^2 have
vanishing absolute difference, but their ratio diverges; precisely this ratio
creates the incompatible posterior in the counterexample. The relative
criterion controls vanishing-probability actions and therefore off-path beliefs.
It is a sufficient criterion, not an asserted necessary characterization.

For a finite power witness

    s_epsilon(a|J) = c_{J,a} epsilon^{k_{J,a}}
                      / sum_b c_{J,b} epsilon^{k_{J,b}},

with c positive and min_a k_{J,a}=0, let C_J=sum_{a:k_{J,a}=0}c_{J,a}.
The relative criterion holds exactly when each action has the same exponent
across the fine sets inside I and the same normalized leading coefficient
c_{J,a}/C_J. Indeed their probability ratio is asymptotic to
(c_{J,a}/C_J)/(c_{K,a}/C_K) times epsilon^{k_{J,a}-k_{K,a}}. Finite many entries
make coordinatewise ratio convergence uniform. These are concrete additional
constraints for a power-witness search, not a general game-to-certificate
compiler or a guarantee that such a witness exists.

## A belief-robust sufficient condition without any fine witness

Suppose s is a coarse legal profile. For every player i, coarse information set
I, actual history h in I, and legal pure action a, suppose

    Delta_s(i,h,a) <= 0,

where Delta compares forcing a now followed by s with following s now and
afterward, conditional on the actual physical history h. Then s is the strategy
part of a coarse SE. To prove this, take the completely mixed coarse sequence
t_n=(1-epsilon_n)s+epsilon_n u, where u is uniform at each information set.
Take a common convergent subsequence of its finite Bayes beliefs. At the limit,
the gain from a at I is sum_h mu(h|I)Delta_s(i,h,a), which is nonpositive under
every possible belief mu. Thus the limit is consistent and sequentially
rational. The terminal law is the law of s.

This condition is strong: it asks for optimality state by state, rather than
only under the player's posterior. It can nevertheless settle implementation
choices that are dominated, safely ignored, or pinned to a payoff floor. It
cannot be assumed for arbitrary source Bayesian decisions.

## A precise rare-error lemma, independent of free-site completion

The useful regular set is a set of **native histories**, not merely a set of
source states. It must include every fixed stochastic reception outcome that
can occur on regular play. The lemma below uses the actual native information
partition at every stage of the consistency sequence.

### Finite setup

Fix a finite extensive-form game with at most \(H\geq1\) strategic decisions
on any path. Initial randomization is part of fixed chance. Let \(R\) be a
prefix-closed family of active regular histories with the root in \(R\). Let
\(B\) be a stopping boundary. There are two allowed successor forms from a
regular history:

* Every supported chance successor stays in \(R\) or enters \(B\).
* At each regular decision history \(h\), a nonempty set of good actions
  continues into \(R\) or \(B\). Actions outside that set can leave regular
  play.

Define the copied information sets by
\(\mathcal C=\{I:I\cap R\ne\varnothing\}\). Require **no reentry from the
boundary**: no decision history descending from \(B\) belongs to a copied
information set. A permanent public abort flag is a sufficient way to ensure
this. More generally the condition is on the actual information sets, not on
whether a global flag happens to be present in the machine state. If there is
no stopping boundary, use \(B=\varnothing\).

For every \(n\), fix a legal behavioral reference distribution \(\beta_n(I)\)
at every copied information set. Its support is independent of \(n\). At
every regular \(h\in I\), every action in this support is good. Every regular
history must have positive reference reach: its chance factors are positive,
and all its strategic actions have positive \(\beta_n\) factors. Equivalently,
one may define \(R\) as the fixed support of the reference play stopped on
entering \(B\). The reference must be a legal policy on native information
sets: different regular nodes in one native information set cannot prescribe
different hidden-state-dependent distributions.

Choose a full-support legal distribution \(\nu_n(I)\) at every copied site.
Set

\[
 \sigma_n(I)=(1-\delta_n)\beta_n(I)+\delta_n\nu_n(I)
 \qquad(I\in\mathcal C),
\]

where \(0<\delta_n\leq1/(2H)\). At all other information sets choose an
arbitrary legal full-support completion \(\gamma_n\). This is one legal,
fully mixed native behavioral profile, regardless of how \(\gamma_n\) is
chosen or whether it depends on \(\delta_n\).

Select once and for all a regular witness \(h_I\in I\cap R\) for each copied
information set. Let \(r_n(h_I)\) be its chance-and-reference reach product,
and put

\[
 a_n=\min_{I\in\mathcal C}r_n(h_I)>0.
\]

If there are no copied sites, the conclusion is vacuous. The number \(a_n\)
may tend to zero arbitrarily fast. It depends on the source perturbation and
regular timing probabilities, but not on free-site completion.

### Claim and proof

At every copied information set,

\[
 \Pr_{\sigma_n}(h\notin R\mid I)
 \leq \frac{H\delta_n}{(1-\delta_n)^H a_n}
 \leq \frac{2H\delta_n}{a_n}.
\]

To prove the numerator bound, inspect a play until its first departure from
\(R\). While it remains regular, every decision information set is copied.
A chance move can only remain regular or enter \(B\). A \(\beta_n\)-supported
move can only remain regular or enter \(B\). Thus any path reaching an
irregular history in a copied site must previously take a strategic action
outside the reference support, before entering \(B\). The latter qualification
is essential: paths through \(B\) cannot reach a copied site by non-reentry.
At each of at most \(H\) strategic opportunities, conditionally on no earlier
departure, the probability of an outside-support move is at most \(\delta_n\).
A union bound gives probability at most \(H\delta_n\). Arbitrary play after
the first departure cannot increase this event's total probability.

For the denominator, every proper prefix of \(h_I\) lies in \(R\), so every
strategic choice on that witness occurs at a copied information set. The
target probability of each required action is at least \((1-\delta_n)\)
times its reference probability. Hence

\[
 \Pr_{\sigma_n}(h_I)
 \geq(1-\delta_n)^H r_n(h_I)
 \geq(1-\delta_n)^H a_n.
\]

No free-site distribution occurs in this product. Site reach is at least
witness reach. Finally, Bernoulli's inequality yields
\((1-\delta_n)^H\geq1-H\delta_n\geq1/2\). Dividing establishes the result.

For example, choose

\[
 0<\delta_n\leq
 \min\left\{\frac1{2H},\frac{a_n}{2H(n+1)}\right\}.
\]

Then every copied site's conditional irregular mass is at most \(1/(n+1)\),
uniformly over **all** free-site completions. This is a finite diagonal
choice. Source perturbations \(\varepsilon_n\) and harmless timing
probabilities \(\rho_n\) can first be fixed; compute \(a_n\) from them, then
choose the implementation-error rate \(\delta_n\). Their supports must remain
fixed, but no rate comparison between \(\varepsilon_n\) and \(\rho_n\) is
otherwise needed for this lemma.

No rectangularity, hidden-type independence, or same-information-set repair of
an irregular path is used. A regular witness provides the denominator.

### The entire copied-site posterior is close to the reference posterior

There is a stronger conclusion useful for likelihood transport. Define the
reference play using \(\beta_n\), stopped on entering \(B\). Its law before
that boundary is well-defined without free-site choices. Couple it to the
target play by sampling, at each copied decision, the mixture flag of
probability \(\delta_n\). Until the first flag, sample the same reference
action and the same fixed chance successor in both processes. The histories
are then identical and regular. If the common path enters \(B\), neither
process can later reach a copied information set. A union bound puts the
probability of a flag before these stopping events at most \(H\delta_n\).

For a fixed copied \(I\), record the first reached history in \(I\), or a
cemetery value if \(I\) is not reached. The two resulting distributions have
total variation at most \(H\delta_n\). Their masses of \(I\) are positive,
and the reference mass is at least \(a_n\). Consequently,

\[
 \operatorname{TV}\bigl(\Pr_{\sigma_n}(\cdot\mid I),
                       \Pr_{\beta_n}(\cdot\mid I)\bigr)
 \leq \frac{H\delta_n}
 {\max\{\Pr_{\sigma_n}(I),\Pr_{\beta_n}(I)\}}
 \leq\frac{H\delta_n}{a_n}.
\]

For completeness, the finite conditioning inequality used here is
\(\operatorname{TV}(P(\cdot\mid E),Q(\cdot\mid E))
\leq\operatorname{TV}(P,Q)/\max\{P(E),Q(E)\}\), whenever both event masses
are positive. Write \(r=\sum_{x\in E}\min(P(x),Q(x))\) and
\(m=\max\{P(E),Q(E)\}\). The unconditional common mass is at most
\(r+1-m\), so \(\operatorname{TV}(P,Q)\geq m-r\). The conditional common
mass is at least \(r/m\), so conditional total variation is at most
\((m-r)/m\), proving the claim.

This controls mixture-noise draws that happen to choose regular actions as
well as draws that leave regular play. Therefore one can establish a clean
fiber factorization for the reference law and transfer its posterior
comparison to the full native consistency sequence. The factorization itself
and the continuation comparison are still separate obligations.

### Why fixed chance and the boundary condition matter

Suppose Nature sets an unobserved error bit to one with probability \(q>0\)
before a player's single information set. Call only bit-zero histories
regular. The player has a regular witness and no strategic error occurs, but
conditional irregular mass is always \(q\). This violates chance closure.
Sending strategic trembles to zero cannot remove fixed network or chance
events.

If a deadline expiry leaves regular active play, it must either count as a
regular successor or enter a boundary with no future copied information set.
Calling it a rare error when its probability is fixed is invalid. A boundary
known only to one player does not automatically prevent reentry into another
player's copied information set. Public permanent exclusion is sufficient;
other cases need a direct information-set argument.

The lemma also does not bound a **deliberately chosen deviation** that leaves
\(R\) with probability one. Such an action needs a legal source simulation,
an exclusion/deposit payoff bound, or another direct gain argument. Rarity
under the candidate profile is not deterrence. Harmless waiting actions can be
included in the reference support with positive \(\rho_n\), but their effects
on payoffs, information, source interpretation, and service guarantees still
need proof.

## Simultaneous rational completion of free sites

Free information sets need not be public subgames. Let all copied-site
distributions above be fixed. At each free information set \(I\), choose
positive floors \(f_{n,I}(a)\) on every legal action, with total
\(\eta_{n,I}=\sum_a f_{n,I}(a)<1\). Let the free-site agent choose a residual
distribution \(z_I\) and implement

\[
 q_I(a)=f_{n,I}(a)+(1-\eta_{n,I})z_I(a).
\]

Create one finite normal-form agent for each free information set, with the
utility of its owning player in the original game. Its pure residual actions
are the legal actions of that information set. Expected utility is multilinear
in these residual distributions, so a mixed Nash equilibrium of this finite
normal-form game exists. It supplies all free distributions simultaneously.
This uses only the fixed native chance law and actual native information sets.

Let \(r_I>0\) be the reach of a free information set under the resulting fully
mixed profile. Positive reach holds at every information set containing a
chance-supported history; permanently unreachable sites can be pruned. Since
an information set is not revisited along a path, its own behavioral choice
does not affect \(r_I\) or its Bayes belief. For a pure local alternative \(a\),
with all other site choices fixed, the agent's unconditional utility
improvement is exactly

\[
  r_I\bigl(V_I(a)-V_I(q_I)\bigr).
\]

Here \(V_I\) includes all future continuation choices of every player, including
other free-site agents with the same owner. The equality follows by partitioning
plays into those that reach \(I\) and those that do not; on the latter, the
policy change has no effect. The pure physical action in this identity need
not satisfy the tremble floors. The feasible Nash comparison instead replaces
the residual distribution by that pure action while retaining all floors; its
utility difference is the positive factor \(r_I(1-\eta_{n,I})\) times the
corresponding residual conditional difference. At a Nash equilibrium the residual distribution
\(z_I\) must be supported on maximizers of \(V_I(a)\). Otherwise changing the
residual distribution to a maximizing action strictly improves unconditional
utility, since \(r_I(1-\eta_{n,I})>0\).

Writing \(M_I=\max_aV_I(a)\), we obtain

\[
 M_I-V_I(q_I)
 =\sum_a f_{n,I}(a)(M_I-V_I(a))
 \leq \eta_{n,I}(\max_aV_I(a)-\min_aV_I(a))
 \leq \eta_{n,I}\,\Delta u_i,
\]

where \(\Delta u_i\) is the finite player's terminal payoff range in the fixed
native game. This bound is independent of how small \(r_I\) is. Dividing by
reach is legitimate because the Nash condition is exact, not an approximate
unconditional best-response inequality.

Choose floors with \(\max_I\eta_{n,I}\to0\). Take a subsequence on which the
entire native behavioral profile and its Bayes assessment converge. Compactness
is finite-dimensional. The resulting assessment is consistent because this
same legal fully mixed native sequence supplies all beliefs. Continuity of
finite conditional continuation values in beliefs and behavioral policies
then gives nonpositive local gain at every free information set. If copied
information sets also satisfy local gain bounds tending to zero, the limit
is sequentially rational by the finite perfect-recall one-shot principle.

The rare-error denominator is uniform over these completions: all chosen
regular witness histories visit only copied sites. Thus one can first choose
\(\delta_n\) from the reference witness minimum and then choose any of the
constrained equilibria. Their existence does not require public free subgames
or any prior support factorization.

This is an **SE construction framework**, not yet the missing runtime theorem.
The main remaining local task is to bound every copied-site native alternative,
including waiting, malformed messages, hidden retries, and nonexcluding
deviations. It is not enough to establish optimality only for canonical source
actions. The copied reference itself must also be legal under the actual
private observation partition; a coarse-measurable limit of an illegal fine
sequence would not suffice.

## Combining completion, conditional control and source comparison

Use the regular reference, copied sites and free completion above. Let
\(q_n^I\) be the reference first-hit posterior at copied site \(I\), and let
\(\Delta_n(h,a)\) be the local gain under the **actual completed profile**
\(\sigma_n\), including its subsequent free-site choices. Suppose uniformly
over copied sites and pure actions that

\[
 E_{q_n^I}\Delta_n(h,a)\le e_n,\qquad e_n\longrightarrow0.
\]

This premise can follow from a legal source deviation comparison, likelihood-gain
control or direct domination. It must hold for the actual completion or uniformly
over the eligible completions. Comparing with an unrelated canonical continuation
is insufficient.

Let \(M_i\) be player \(i\)'s terminal payoff spread. Since
\(\Delta_n(h,a)\in[-M_i,M_i]\), conditional TV control gives

\[
 G_{\sigma_n}(I,a)\le e_n+2M_iH\delta_n/a_n.
\]

Free-site gains are at most \(\eta_{n,I}M_i\). If
\(\delta_n/a_n\to0\) and \(\max_I\eta_{n,I}\to0\), take one subsequence on which
the entire profile and all Bayes beliefs converge. Its common fully mixed
witness proves consistency; the gain bounds and perfect recall prove sequential
rationality. Thus the limit is an SE.

For joint-law preservation, complete the reference arbitrarily after boundary
\(B\). Suppose its record law is within \(\ell_n\) of the desired source law,
and reference play reaches \(B\) with probability \(b_n\). Coupling until the
first mixture-noise flag or \(B\) gives

\[
 d_{\rm TV}(P_{\sigma_n},P_{\mathrm{source},n})
 \le H\delta_n+b_n+\ell_n.
\]

Only noise or reaching \(B\) can allow the arbitrary free continuation to change
the record. Require explicitly \(b_n\to0\) and \(\ell_n\to0\). Together with
the stated noise rates and convergence of the source law, these give the selected
initialized joint law in the limit, including inputs and payoff coordinates.
This is a complete finite mathematical implication. Its difficult runtime
premise remains the actual copied-site comparison.

## Hidden randomness can restore deterministic replay without publication

In any finite-horizon finite-state stochastic process, fixed transition or
observation kernels can be represented by a hidden random table. For each
time \(t\), state \(s\), and action \(a\), sample an entry
\(U_{t,s,a}\) according to the relevant fixed kernel at \((t,s,a)\). Sample
these entries independently of each other and of the initial input; the
initial input itself may have any correlated law. At time \(t\), use the entry
for the actual state and action. Each entry is used at most once because of
the time coordinate. Finite path probabilities are exactly the products of
the original kernel factors: unused table entries sum out to one.

Conditioned on the whole hidden table, replay is deterministic. This is a
probabilistic representation, not an observation rule. No player, ledger, or
scheduler is given the table, so it introduces no common knowledge. Finite
products of finite PMFs permit arbitrary real probabilities; a uniform finite
seed with rational probabilities is not required.

For stateful gossip, put its memory in \(s\), or use a suitable joint random
delay/route tape. Independent resampling is not valid if one omits state that
encodes temporal correlations. A persistent per-packet delivery delay can be
drawn once and retained. All parameters and the entire tape law stay fixed
through the SE consistency sequence.

This representation does **not** prove likelihood cancellation. If paired
histories query different table entries or require different observations,
their probability weights may differ. One must prove an appropriate
probability-preserving relabeling or sum the exact weights over replay fibers.
In particular, the extra nonreceipt condition in the two-packet example
contributes a factor \(1-q\); it is not an unused coin that sums to one.

## Exact information obstruction, with its runtime limitation

Let the source initial state be a finite random variable \(\theta\) with law
\(p\), and suppose the selected source outcome requires a decision
\(a=f(\theta)\). In an implementation, let \(S\) be the decision maker's entire
legal information before the irrevocable decision, with kernel
\(K(s\mid\theta)\). An arbitrary legal randomized decision has a kernel
\(\alpha(a\mid s)\), and therefore

\[
 \Pr[a=f(\theta)]
 =\sum_s\sum_a\alpha(a\mid s)
       \sum_{\theta:f(\theta)=a}p(\theta)K(s\mid\theta)
 \le \sum_s\max_a\sum_{\theta:f(\theta)=a}p(\theta)K(s\mid\theta).
\]

The inequality is sharp: at each signal choose a maximizing action. The source
joint law gives the event \(a=f(\theta)\) probability one, so its total-variation
distance from every implementation joint law is at least one minus the displayed
upper bound. Exact preservation is possible only if every positive-probability
signal fiber contains states with the same required action. This is a policy
impossibility, stronger than an equilibrium impossibility.

For a fair bit that is independently erased with probability \(\delta\), the
bound is \(1-\delta/2\), and the joint-law distance is at least \(\delta/2\).
Crucially, \(S\) must include every legal channel and the entire personal recall;
omitting the player's source private input would invalidate the argument.
Here \(K\) is fixed by the upstream play and observation model. If earlier
policies can change \(K\), a universal impossibility argument must establish the
bound uniformly over all feasible upstream kernels, or separately show why the
selected preserved law fixes the relevant kernel.

This does not presently embed in Vegas. Proper commitment packets have shape
`.commitment event handle`, with no raw value. A proper opening can be submitted
only in the installed phase, and the later commitment phase requires the prior
public phase to finish. Source private inputs remain in the owner's observation.
Thus the proposed information loss would have to be demonstrated inside those
interfaces; merely deleting pending visibility does not establish it.

## Exact decidability for any fixed finite rational instance

This gives a complete mathematical discriminator without pretending that a small
search or one failed encoding rules out all preserving SEs. Assume explicitly
specified finite extensive games with finite perfect-recall information sets,
rational chance probabilities and payoffs, and finite observed terminal records.
Remove histories with zero chance reach under every behavior profile, and omit
information sets containing no remaining history. These cannot be reached by any
fully mixed behavioral strategy. In the runtime instance, finiteness must include
the relevant private observation outcomes and the terminal audit readout; arbitrary
infinite internal chance representations cannot simply be declared finite.

### Closure formulation: a direct independent route

For a completely mixed behavior profile \(\tau\), each surviving history's reach
\(r_h(\tau)\) is a polynomial with rational coefficients. For an information set
\(I\), let \(M_I(\tau)=\sum_{h\in I}r_h(\tau)>0\). Bayes beliefs are exactly the
nonnegative normalized variables satisfying
\(\nu_I(h)M_I(\tau)=r_h(\tau)\).

An assessment \((\sigma,\mu)\) is consistent exactly when

\[
 \forall\varepsilon>0\;\exists\tau,\nu:\quad
 \tau\text{ completely mixed},\quad \nu\text{ satisfies Bayes},\quad
 \|\tau-\sigma\|_\infty<\varepsilon,\quad
 \|\nu-\mu\|_\infty<\varepsilon.
\]

In finite dimension this is equivalent to the defining sequential-limit
condition: a sequence implies every neighborhood is hit; conversely choose a
witness for \(\varepsilon=1/n\). Absolute-value inequalities are pairs of linear
inequalities. Thus consistency is a first-order formula over the real field.

Sequential rationality is also polynomial: enumerate the finitely many pure
continuation deviations at each information set and require the prescribed
conditional continuation payoff to dominate each. Expected payoffs are finite
sums of products of strategy and belief coordinates. Checking pure continuation
policies suffices because any randomized continuation is a convex combination of
pure continuation policies, with its random choices sampled in advance; perfect
recall gives their usual realization-equivalent behavioral interpretation.

For each finite terminal-record atom \(x\), the induced joint probability
\(P_\sigma(x)\) is polynomial. Consequently the conjunction of SE and
\(P_\sigma(x)=q(x)\) for all atoms is a first-order real formula. Quantifier
elimination decides whether a target SE with the specified rational law exists.
This is a mathematical decision procedure, not a practical complexity claim.
It agrees with the established algebraic approach: Blume and Zame's Theorem 2
proves that the sequential-equilibrium correspondence is semialgebraic, using
Tarski–Seidenberg and an epsilon–delta formulation of limits.
[Blume and Zame, author manuscript, Theorem 2](https://econwpa.ub.uni-muenchen.de/econ-wp/game/papers/9309/9309001.pdf).
The underlying real-field decision method is classical.
[Tarski, A Decision Method for Elementary Algebra and Geometry](https://doi.org/10.1525/9780520348097).

More generally, fixed finite source and target games permit the sentence

\[
 \forall\sigma_S,\mu_S\;[
   \operatorname{SE}_S(\sigma_S,\mu_S)\Rightarrow
   \exists\sigma_T,\mu_T\;
   (\operatorname{SE}_T(\sigma_T,\mu_T)\land
      P_{\sigma_T}=P_{\sigma_S}))].
\]

This decides universal preservation for the fixed pair, including the complete
initialized joint law. One need not first know a rational target equilibrium law;
source and target strategies are quantified real variables. It does not decide
the general theorem over all programs or unbounded runtimes.

### Power certificates remove the closure quantifier

The checked finite-game completeness theorem in
`GameTheoryExtensions/Analysis/Protocol/PowerCompleteness.lean`,
`GameTheory.Protocol.InformationModel.BehavioralAssessment.IsSequentiallyConsistent.exists_power_certificate`,
preserves the exact assessment. It justifies this alternative finite decomposition.

Enumerate (a) the positive strategy support at each information set and (b) the
nonempty positive belief support at each information set. For an action coordinate
\(c\), set order \(k_c=0\) on positive strategy support and require \(k_c>0\)
elsewhere. Let \(m_h\) be the vector of occurrence counts of every behavioral
action coordinate along history \(h\). For a selected leading history \(g_I\),
require

\[
 (m_h-m_{g_I})\cdot k=0\quad(h\text{ in positive belief support}),\qquad
 (m_h-m_{g_I})\cdot k>0\quad(h\text{ outside it}).
\]

These constraints form a finite homogeneous rational linear system. If it has a
real solution, rational density inside its rational equality subspace preserves
all finitely many strict inequalities; clearing denominators yields a natural
integer solution. Equivalently, scale strict positive inequalities to be at least
one and test ordinary rational linear feasibility. Thus unbounded integer exponent
enumeration is unnecessary. The finitely many support patterns can each be accepted
or rejected by linear feasibility independently of coefficient feasibility.

For positive coefficients \(a_c\), put
\(\tau_c(t)=a_ct^{k_c}/\sum_{d\in A(I_c)}a_dt^{k_d}\). Require
\(a_c=\sigma_c\) on zero-order coordinates; these sum to one at each information
set. The leading reach coefficient is
\(w_h=c_h\prod_c a_c^{m_{h,c}}\), where \(c_h>0\) is the fixed chance reach.
All local normalization denominators tend to one. Consequently Bayes limits are
zero on nonleading histories and on leading histories satisfy

\[
 \mu_I(h)\sum_{g\in S_I}w_g=w_h.
\]

These are polynomial equations and positivity constraints. Add the polynomial
sequential-rationality inequalities and terminal-law equations. Each linearly
feasible support pattern gives an existential real formula. Their finite
disjunction describes exactly the preserving SEs. Soundness follows directly by
the displayed normalized-power sequence; completeness is the cited checked
finite-history theorem. Fixed chance probabilities are coefficients, never
trembling variables. This construction is stronger than bounded exponent search,
but its implementation and size reduction remain separate work.

## Related work and ownership

Sugaya and Wolitzky show that communication revelation principles can fail for
SE in multistage games: richer communication can enlarge the set of consistent
off-path beliefs. Their positive characterization permits enriched communication,
and their mediator is allowed to tremble. This supports treating communication
changes as changes to consistency, not merely strategy measurability. It is not
a theorem about a fixed ledger or fixed chance scheduler.
[The Revelation Principle in Multistage Games](https://economics.mit.edu/sites/default/files/inline-files/revelationprinciple_0.pdf).

Blume and Zame's Theorem 2 establishes semialgebraicity of the SE strategy
correspondence for finite perfect-recall extensive forms, with nature
probabilities fixed as part of the game form. Their working-paper proof uses
real-algebraic closure formulas. The full-assessment derivation above also
retains beliefs and the initialized record explicitly.
[The Algebraic Geometry of Perfect and Sequential Equilibrium](https://econwpa.ub.uni-muenchen.de/econ-wp/game/papers/9309/9309001.pdf).

Geffner and Halpern construct sequentially rational communication implementations
using carefully ordered rare errors. Their asynchronous scheduler and message
assumptions need separate checking: a fixed reserved-service tape and one
broadcast envelope with correlated private receipts are different objects.
[Communication Games, Sequential Equilibrium, and Mediators](https://arxiv.org/abs/2309.14618).

The generic mathematical layer belongs with finite conditional probability,
actual information-set completion, legal deviation transport and consistency
certificates. In particular,
`GameTheory.Protocol.InformationModel.exists_consistent_component_completion`
in [ComponentCompletion.lean](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean)
already supplies common-sequence completion, and
`GameTheory.Protocol.InformationModel.sequentialEquilibrium_of_copied_comparisons_limit_of_lawError`
in [LocalSimulationLimit.lean](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
already accepts mixtures of legal source gains and initialized-law errors.
The existing likelihood-gain and power-certificate modules supply other generic
consumers. Another abstract equilibrium existence layer is not the priority.

Vegas must supply legal observation-based policies and operational producers:
source-blind likelihoods where required, actual continuation comparisons,
timing/alias control, and failure semantics. These finite arguments require no
new Multitubes dependency. Proposed generic transport or stopping theory and
Multitubes examples should be evaluated separately from the Vegas compiler.

New bibliography keys are `SugayaWolitzky2021Revelation` and
`BlumeZame1994Algebraic`; the communication comparison also uses the existing
`GEFFNER2024105890` entry. The maintained paper's mathematical statements require
their own checked theorem pins; these hand proofs do not supply them.
