# Consistent approximate SE under vanishing service noise

Analysis by Codex. There is a useful positive result between exact SE
preservation and approximate Nash preservation. In a fixed finite game,
small primitive chance-kernel errors allow every selected source SE to be
approximated by target assessments that are exactly consistent and have
vanishing whole-continuation sequential regret. Their initialized outcome
laws also converge to the selected source law. Exact nearby target SEs need
not exist, as the selected-equilibrium example in
[probabilistic-runtime-preservation.md](probabilistic-runtime-preservation.md)
shows.

This is a paper theorem with an explicit construction and quantitative
bound. It is not a checked Lean capstone. A noisy actual-runtime application
still needs the finite tree and information adapter stated below.

## Primitive hypotheses and the preservation target

Fix a finite extensive-form tree with finitely many players, finite
nonempty action menus, and perfect recall. Its node ownership, action
labels, information partition, terminal histories, and payoff functions
are fixed. Only the chance kernels change, from $p_0$ to $p_n$.
The initial random draw, if any, is one of these chance moves.

A source-compatible history is a history whose chance-edge probabilities
under $p_0$ have positive product. Compatibility includes every legal player
choice, not just choices prescribed by a selected equilibrium. Remove
chance-impossible histories to obtain the source game $G_0$.
The target $G_n$ similarly retains histories compatible with $p_n$.
Thus formerly zero-probability chance branches may become possible.

Call an information set copied if it contains a source-compatible
history. Otherwise it is genuinely new. Information labels and player
recall are inherited from the same full tree; the target does not silently
merge, split, or relabel the old information sets. Perfect recall must hold
on this full tree, including newly reachable branches. It is insufficient
to check recall only on the old support.

Let $L$ be the maximum number of chance moves on a path. For player $i$,
assume terminal payoffs over the entire full tree lie in an interval of
length $W_i$. These bounds cover formerly impossible outcomes too. Fixed
finite payoffs supply such bounds automatically. Growing deposits or other
noise-dependent unbounded payoffs require another argument.

Assume the primitive chance error satisfies

$$
\delta_n=\max_{h\text{ source-compatible chance node}}
 d_{\mathrm{TV}}(p_n(\cdot\mid h),p_0(\cdot\mid h))\longrightarrow0.
$$

This includes all source-compatible histories reached after deviations,
not merely honest initialized play. Requiring the same bound at every
chance node of the full tree is a convenient stronger hypothesis. Kernels
at genuinely new histories may actually be arbitrary: the first-departure
coupling below never needs to compare them.

Sequential regret at an information set means the largest conditional
payoff improvement from replacing that player's **entire remaining
policy**, holding other players' prescribed policies fixed and using the
assessment's belief at that information set. A consistent approximate SE
here has a single global fully mixed sequence establishing exact
Kreps–Wilson consistency, and bounds this regret at every legal decision
information set. It does not use approximate Bayes conditioning or permit
arbitrary weak-PBE beliefs.

**Paper theorem.** For every source SE assessment $(\sigma,\mu)$ of $G_0$,
there are consistent target assessments $A_n$ with:

- maximum whole-continuation sequential regret tending to zero;
- strategies and beliefs at every copied information set converging to
  the selected source assessment;
- initialized terminal-history law, and hence any fixed observable
  outcome and realized-payoff law, converging in total variation to that
  source law.

At genuinely new information sets the construction has zero sequential
regret. It does not preserve any arbitrary specification at a
chance-impossible source site, which is absent from the source game, and
does not assert existence of an exact target SE close to the selected
source outcome.

## Uniform coupling before the first changed chance outcome

Extend any behavioral profile to the full tree. Run the source and target
with the same action samples whenever their histories agree. At each
source-compatible chance node use a maximal coupling of $p_0$ and $p_n$.
Its conditional mismatch probability is at most $\delta_n$.

Before the first mismatch, the histories coincide and remain
source-compatible. There are at most $L$ chance opportunities. Consequently
the probability of any mismatch is at most $L\delta_n$. After a mismatch,
no further comparison is needed. The bound is uniform over all prescribed
profiles and all unilateral continuation policies, even though their
histories and actions are adaptive.

This gives total-variation error at most $L\delta_n$ for terminal
histories, for a fixed information set's reached-history-or-not-reached
readout, and for a continuation begun at any source-compatible history.
It remains valid if target-only continuation kernels are arbitrary.
There is no independence assumption across chance opportunities.

## Choose source trembles slowly

Source consistency supplies fully mixed source profiles $\sigma^k$ with
their actual Bayesian beliefs $\mu^k$, such that

$$
(\sigma^k,\mu^k)\longrightarrow(\sigma,\mu).
$$

Let $m_k>0$ be the minimum source reach probability of a copied decision
information set under $\sigma^k$. All these probabilities are positive:
there are finitely many copied sets, all player lotteries have full
support, and each copied set contains a source-compatible history. If
there are no copied decision sets, take $m_k=1$.

Let $r_k$ be the maximum whole-policy sequential regret of
$(\sigma^k,\mu^k)$ in the source game. The source trembles need not be
rational, but $r_k\to0$. In a finite perfect-recall game, continuation
payoffs are continuous in beliefs and prescribed policies, and it
suffices to compare finitely many pure continuation plans. At the limiting
source SE every such gain is nonpositive.

Choose $k(n)\to\infty$ slowly enough that

$$
\frac{\delta_n}{m_{k(n)}}\longrightarrow0.
$$

For example, choose increasing thresholds $N_k$ so that
$L\delta_n\le m_k/k$ for every $n\ge N_k$, then let $k(n)$ increase only
when its corresponding threshold is passed. The finitely many initial
targets before the small-error regime can use arbitrary target SEs;
they do not affect the asymptotic claim.

The prescribed target copied-site lotteries will be $\sigma^{k(n)}$, not
necessarily the exact source lotteries $\sigma$. These small prescribed
trembles can be necessary to keep exogenous rare failures from dominating
beliefs at a copied site that was off path in the selected source SE.

## Complete the genuinely new sites by a finite auxiliary SE

Fix $n$ and $k=k(n)$. At every copied decision node replace the original
owner's choice by chance with fixed lottery $\sigma^k$ for that information
set. Leave all genuinely new player decisions strategic and retain $p_n$
at the original chance nodes. Call this the auxiliary game.

Keep the original information labels and remembered action observations:
when a copied choice is sampled by chance, its old owner still observes
the realized action in exactly the way its original recall did. This
construction does not make that player forget a previous action, or tell
another player an action it originally could not observe. Information
sets at remaining strategic nodes are unchanged. Their own past decision
sequence is the projection of the original remembered sequence onto
remaining decisions, so perfect recall is preserved. The auxiliary game
is finite and therefore has an SE.

The following no-return fact is essential. After a player acts at a
genuinely new information set $J$, it cannot later act at a copied
information set $I$. Perfect recall would require every history in $I$
to remember the earlier own decision at $J$. But a source-compatible
history in $I$ has only copied previous decisions and cannot contain $J$.
This is a contradiction. The fact concerns later decisions of that same
player; other players may still reach copied sites.

Take an auxiliary SE and reinstate the fixed positive lotteries at copied
sites as actual player lotteries. Its auxiliary beliefs at new sites
become target beliefs. Because an owner starting at a new site has no
future copied owned decision, every target whole-continuation deviation
available there is also available in the auxiliary game. Opponents'
frozen copied lotteries and all chance kernels are identical. Thus
auxiliary sequential rationality proves zero whole-policy target regret
at every new site. This does not infer whole-policy rationality from a
one-step best-response claim.

Consistency transfers exactly. The auxiliary SE has a fully mixed
sequence at its remaining strategic sites. Insert the fixed fully
supported $\sigma^k$ lotteries at every copied site in each sequence
term. These are fully mixed profiles of the original target, with the
same history likelihoods as the auxiliary sequence. Their new-site
belief limits are the auxiliary beliefs.

For sufficiently small $L\delta_n<m_k$, every copied site has positive
target reach probability regardless of the new-site completion: at $p_0$
the completion is never encountered, and the uniform coupling bounds
the change in its reach probability. Give copied sites their actual
target Bayesian beliefs. These beliefs are also the limits along the
inserted sequence, since their limiting denominators are positive.
One global sequence therefore witnesses consistency at all sites.

## Copied-site beliefs and whole-policy regret

Under $p_0$, the reinstated profile agrees with $\sigma^k$ on every
source-compatible history; the new-site completion is irrelevant.
For each copied information set $I$, the source and target
reached-history-or-not-reached laws are within $L\delta_n$.

If probability laws $P,Q$ are within $e$ and $Q(E)=b>0$, conditioning
gives a bound $2e/b$ whenever $P(E)>0$. For an event $B\subseteq E$,
write the normalized difference with denominator $b$:

$$
\left|\frac{P(B)}{P(E)}-\frac{Q(B)}b\right|
\le\frac{|P(B)-Q(B)|}b
 +P(B)\frac{|b-P(E)|}{P(E)b}
\le\frac{2e}b.
$$

Consequently the copied target belief at $I$ is within
$\eta_{n,k}=2L\delta_n/m_k$ of $\mu^k(I)$, uniformly over the auxiliary
completion.

Now compare any whole target continuation policy at $I$ directly with
its restriction to source information sets. Do **not** compare it with
the auxiliary game, whose frozen copied choices are unavailable to
deviation. Starting from a source-compatible history in $I$, the uniform
chance coupling compares these continuation laws within $L\delta_n$.
Target choices at new sites can matter only after a coupling mismatch.
The belief change contributes another $\eta_{n,k}$.

The prescribed conditional payoff and the deviating conditional payoff
each differ from their corresponding source values by at most
$W_i(\eta_{n,k}+L\delta_n)$. Thus at every copied site of player $i$,

$$
\operatorname{Regret}_{G_n}(I)
\le r_k+2W_i\left(\frac{2L\delta_n}{m_k}+L\delta_n\right).
$$

This treats all remaining own decisions, including newly reachable
decisions, in the deviation. The bound tends to zero with the chosen slow
index. New-site regret is already zero. Source consistency convergence
and the copied belief bound also prove convergence of the copied
assessment to $(\sigma,\mu)$.

If $e_k$ is the source terminal-law distance between $\sigma^k$ and
$\sigma$, continuity in the finite tree gives $e_k\to0$. The initialized
target terminal-law error is bounded by

$$
L\delta_n+e_{k(n)}\longrightarrow0.
$$

Any fixed readout, including the full realized payoff vector, can only
decrease this total-variation error.

## A uniform modulus for a fixed finite game

The asymptotic statement can be made uniform over the source game's
selected SE assessments, without obtaining a universal numerical rate.
The consistent assessment set is a closed subset of a finite product of
simplexes: it is the closure of the graph of Bayesian beliefs of fully
mixed profiles. Sequential rationality is closed by the finite pure-plan
payoff comparisons. Hence the source SE assessment set is compact.

For any accuracy level, choose one sufficiently close fully mixed source
tremble term with sufficiently small source regret near each source SE.
These neighborhoods cover the compact SE set. A finite subcover uses
only finitely many tremble terms, and therefore has a positive minimum
copied reach probability. One sufficiently small primitive noise bound
then works for every selected source SE, by the preceding construction.
Terminal-law continuity is uniform in this fixed finite tree.

Thus there is a game-dependent modulus tending to zero that bounds
regret, logical-law error and copied-assessment distance simultaneously
for all selected source SEs. It may depend on delicate off-path tremble
orders. The proof does not give a general linear or polynomial rate in
$\delta_n$.

## Conditional application to a checked native backend

The theorem applies first to a native game already known to have a
preserving SE. For example, fix a finite instance of the checked audited
calendar compilation, its initial law, raw player menus, public driver,
observation and recall rules, terminal audit, and finite deposit vector.
Lift a selected high-level source SE through that checked backend. The
result is the source assessment $G_0$ for the present noise theorem; it
already includes the full audited raw interface of that backend.

At each public service round, replace the normal driver's command law
by a lottery that uses the normal law with probability $1-\rho_n$ and
an outage wait with probability $\rho_n\to0$. Keep the application,
player menus, audit and payoffs fixed. For a bounded number $N$ of service
rounds, form the finite union tree containing both normal and outage
branches. Retain original player observation and recall labels on that
tree. This requires an actual finite structural tree/information
embedding; it has not been supplied as a Lean adapter here.

At every source-compatible service history, this mixture changes the
primitive command kernel by TV at most $\rho_n$. Beyond a first outage
the normal driver may react arbitrarily to the changed history; those
new histories do not need to remain close to a corresponding source
kernel. The first-departure coupling still gives initialized law error
at most $N\rho_n$ before adding the selected native source tremble error.
Actual execution may encode each service round with several internal
moves; its finite common tree must bound those as well, for example by
the native body's $2N+1$ move horizon where applicable.

Subject to that structural adapter and bounded raw menus, every original
high-level source SE therefore has consistent noisy-native assessments
with vanishing whole-policy sequential regret and typed outcome/payoff
law error. The deposits remain fixed finite constants, so the relevant
payoff range does not grow as noise decreases. This is a meaningful
approximate-SE target for noisy backends, stronger than approximate Nash.
It is compatible with the exact-law failure lower bounds and the absence
of nearby exact target SEs.

This conditional application does not itself translate the high-level
language into a newly enlarged raw interface. It starts from a checked
preserving native backend, then perturbs only its service chance kernels
within one common finite structural game. Changed information semantics,
new actions at old information sets, different audits or deposits, and
unbounded physical execution require separate arguments. A fixed source
horizon alone does not bound the number of physical opportunities.

Finally, closeness of the honest initialized transport law alone is not
the primitive hypothesis. A backend can behave identically on honest
play while changing a chance kernel by order one after a legal deviation
or at a copied off-path site. Its conditional incentives can then remain
order one apart. The theorem derives conditional posterior control from
uniform primitive error over all source-compatible histories and slowly
chosen source trembles; it does not assume the desired posteriors.
