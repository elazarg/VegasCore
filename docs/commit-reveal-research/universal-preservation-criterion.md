# A compositional criterion for SE preservation

Analysis by Codex. This note gives a finite-game paper theorem assembled from
an information/execution argument and the existing checked terminal-audit
extension. Its clean-action constructor allows real, uncharged runtime
choices. It is not a characterization of all possible compilers, a theorem
for the current full raw Vegas runtime, or an adopted backend specification.

The useful distinction is between three things: a lawful source choice, an
implementation choice that changes only ancillary runtime data, and a
departure that needs another incentive argument. An alternative packet name
is not automatically ancillary. A receipt, bid, nonce or retry can reveal a
private fact or change a subsequent logical opportunity.

## Fix the interface before selecting an equilibrium

Let a public descriptor B specify a finite source program, its observation and
utility conventions, permitted load and physical horizon, and a class of
builders. Every realized builder gives a finite extensive-form game with
perfect recall. Menus are nonempty at decisions. Histories include the actual
observations players can obtain and remember. Legal source chance edges have
positive probability; zero-probability edges are removed from its legal tree.

Divide each builder's target into a **clean game C**, retaining all actions
covered by the equivalence argument below, and a **raw game T**, adding the
other physically allowed choices. C is a structural action restriction of T:
same states, chance transitions and observations on clean histories, with
smaller action menus. It is not necessarily an extensive-form subgame.
The restriction concerns all lawful source histories, not just one intended
profile. Unknown or unclassified raw choices make the application incomplete.

The descriptor supplies uniform utility bounds L_i and U_i and positive
collection bounds rho_i across the builder class. Choose the collateral and
its monetary convention before selecting a builder or source assessment:

\[
K_i=\max\{0,(U_i-L_i)/\rho_i\}.
\]

For all bounded source utilities, the constants may depend on their declared
bounds; one fixed finite deposit is not claimed to cover every unnormalized
utility scale. Source choices already subject to an intrinsic forfeit retain
that source payoff. The compiler cannot increase a punishment on lawful
withholding and silently call the source game unchanged.

## A clean constructor that permits extra choices

Start with a finite source game G with perfect recall. Expand each logical
transition by a bounded finite amount of runtime processing. The service can
have hidden persistent state, public records and private receipts. There is
sure progress to the next logical transition under every legal clean action
and every compatible runtime state. A physical deadline outage is not
stuttering in this constructor.

At a copy of a source player decision I, let J=(I,z) be the target information,
where z is the entire remembered auxiliary record. Replace each source action
a by a finite nonempty family of clean implementations (a,r). The player
chooses both components. The alias r can be private or publicly observed.
The available source actions remain exactly those at I. Alias families and
their selectors are information-local at J. Own source choices and auxiliary
observations are retained with stage labels sufficient for perfect recall.

For **every** implementation (a,r), at **every** complete current runtime
history above h, the next logical transition has the original source law
for a. Runtime processing may respond to r, affect auxiliary records, or
change bounded waiting time. It may not change the logical menu, original
source observation, logical chance kernel, terminal readout or utility.
Terminal utility is u_i of the erased source terminal history. This excludes
unmodeled fees, capital costs, participation and external rewards; the
[cost analysis](costs-and-scope.md) explains exact cancellation conventions
and quantitative alternatives.

The conditional logical-kernel clause is important. An auxiliary signal that
predicts a not-yet-drawn source chance outcome violates it. Matching current
source-history beliefs alone would not rule out that additional information.

Choose one information-local full-support selector kappa for the clean alias
families. It is part of this proof interface and does not depend on the selected
source equilibrium or utility. Full support means every available r has
positive probability conditional on a and J. For a source decision prefix h,
replay the actual runtime kernels, fixing only the past source actions and
chance outcomes in h, and sampling aliases using kappa. Let Q_h^kappa be the
law of the complete runtime prefix omega at the ready copy of h. The replay
does not condition on future outcomes or successful admission.

Let Z_i(h,omega) decode everything player i can physically remember. Require

\[
I_i(h)=I_i(h')\quad\Longrightarrow\quad
 (Q_h^\kappa\circ Z_i(h,\cdot)^{-1})
 =(Q_{h'}^\kappa\circ Z_i(h',\cdot)^{-1}).          \tag{1}
\]

This is a finite channel equality derived from physical kernels and the fixed
selector. It includes support and the joint law of the full remembered
record, including timing, absence, sender, bytes, fee metadata and receipts.
Testing separate packet marginals or only reached honest histories is weaker.
The complete runtime prefix need not be public, and different players'
auxiliary views can be correlated.

The selector is a strategy used to construct an equilibrium, rather than a
claim that aliases are actually chance choices. The execution condition
covers every player-selected alias. The channel test covers the one prescribed
selector, including its future use after deviations. Players may use other
selectors in other equilibria or deviations.

### Clean preservation, paper proposition

Under this constructor and (1), every source SE (sigma,mu) has a clean SE.
At J=(I,z) it chooses a according to sigma(I) and r according to kappa.
Beliefs project to mu at every decision, including off path. Its joint erased
terminal-history and utility law is exactly the source law.

**Proof of consistency.** Take one fully mixed source consistency sequence
sigma_n with Bayesian beliefs converging to mu. Lift its action probabilities
as sigma_n(a|I) kappa(r|a,J). All clean player choices are positive. Multiplying
primitive transition probabilities gives

\[
w'_n(h,\omega)=w_n(h)Q_h^\kappa(\omega).
\]

The runtime replay includes the probabilities of the chosen aliases. Source
action probabilities factor out because their logical component ignores z.
This factorization is independent of n. By (1), the auxiliary marginal at
J=(I,z) is a common positive number q_I(z) for all h in I. Hence the full
Bayesian belief at that mixed index is

\[
\mu_{n,i}(h\mid I)
\frac{Q_h^\kappa(\omega)[Z_i(h,\omega)=z]}{q_I(z)}.
\]

The second factor is a fixed kernel. Full beliefs therefore converge, not
just their projection. One lifted mixed sequence supplies consistency at all
clean decisions. No limiting zero reach probability is divided by.

**Proof of rationality.** Fix J and any local lottery over pairs (a,r). From
each compatible full runtime history, use that lottery once and the lifted
policy later. Erasure gives precisely the source continuation using its
pushforward lottery over a, and sigma afterward. This follows by induction:
processing terminates, the logical kernel is unchanged for every r, and all
future logical components ignore the auxiliary data. The payoff does not
depend on r. Averaging over the constructed belief gives the source
comparison at I under mu. Its gain is nonpositive. Target perfect recall and
the finite one-shot-deviation principle with consistent beliefs then establish
optimality against every whole adaptive continuation policy. Such policies
can react to later aliases and receipts; they are not restricted to ignoring
them. Finally, initialization erasure proves the joint terminal law. QED.

Public aliases are therefore not banned. Their mere existence does not imply
preservation either. If an alias is available only to one hidden type and
publicly certifies that type, no full-support ancillary selector may exist.
Giving every type the same visible name is not a substitute for the test.

A particularly simple instance has only private response aliases: changing r
preserves the **exact** public packet, application effect, receipts, scheduler
recall and every other player's observation; only its author remembers the
private name. Menus are stable under erasing those names and contain their
normal forms. This is the operational case of the checked
[private-response-alias theorem](../../Interaction/ReactiveAliasEquilibrium.lean).
It is stronger evidence than a payload-only equality. An actual retransmission
usually changes the network record and does not satisfy those primitive
equalities. A one-decision choice of guaranteed equivalent timing or encoding
can fit the broader paper constructor, but an adaptive retry protocol needs
its own history, menu and channel proof.

## Add the remaining raw actions with an actual audit

**Interface for this step.** The whole clean game C, including all its
uncharged aliases, is the structural action restriction of raw T. Both games
are finite with perfect recall. Raw base utility b_i is at most U_i on every
raw terminal history and equals the clean source utility on every clean
terminal history, which is at least L_i. Any fees or other retained costs
have already been accounted for in this equality. These bounds are independent
of the chosen collateral, or hold uniformly for its declared range.

A terminal audit uses authentic evidence and actually collects K_i with a
specified probability; the charge is not just an accusation or a theoretical
entitlement. It is zero on **all** clean complete histories, including lawful
deviations and alternative aliases. At every clean hidden decision history,
each additional current raw action by i has collection probability at least
rho_i, under every joint continuation policy. The bound covers successful
inclusion, disclosure before collection, later replacement, and arbitrary
behavior after another charge. A fresh or previously unused collectible
amount is available at the first departure. No obligation to behave lawfully
in a dirty suffix is assumed.

The runtime audit is nonstrategic in this model, and the collected money is
burned or paid outside the ordinary modeled players. Deposit-dependent bounty
redistribution requires a different payoff bound. Fundability and capital
timing are explicit omissions here, not consequences of a finite formula.

**Enforcement calculation.** After any such first departure, expected net
utility is at most U_i-rho_i K_i, which is at most L_i. A retained continuation
gives at least L_i and incurs no audit charge. The bound is pointwise in hidden
history and arbitrary future play, so it survives every information-set belief.
No assumed posterior or equilibrium continuation appears in the calculation.

A uniform rho can be obtained from finite mechanics. For a fixed builder,
enumerate retained hidden histories, excluded current actions and pure joint
contingent plans; if each collects with positive probability, their finite
minimum is positive and mixtures inherit it. This alone is not a uniform
minimum over an infinite builder class. A public bounded-horizon survival
argument, for example rho>=alpha epsilon^N, can provide the common bound
without independence between steps. The pointwise primitive conditions must
hold for every permitted load and action, rather than only the intended bid.
See [service-and-enforcement.md](service-and-enforcement.md).

### Assembled preservation, paper theorem

For every builder in the declared class, under the clean constructor, channel
test, structural raw extension and uniform audit conditions above, the single
finite deposit vector K preserves every source SE: each has a raw target SE
with the same joint logical terminal law and clean realized utility law.
Clean copied beliefs first project to source beliefs; the raw extension
preserves those clean beliefs. Raw new sites receive rational consistent
continuations.

**Proof.** Construct the clean SE by the preceding proposition. Apply
`sequential_equilibrium_extends_of_terminal_audit` from
[TerminalAudit](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)
to the structural restriction C to T, using L,U,rho,K. Finite perfect recall
supplies the decision-recall and antichain conditions; finite nonempty menus
supply a fully mixed reference. The existing completion theorem constructs
one globally consistent raw assessment, with rational play at new sites and
the same initialized clean history law. Audit soundness makes its initialized
settlement exactly the clean utility law. Compose the readout with the clean
erasure. The same K works for every selected source assessment and every
builder satisfying the uniform bounds. QED.

Only the terminal-audit extension and the cited special adapters are checked.
This assembled constructor and its runtime application are paper results.
An independent mathematical review accepted the complete constructor,
including its consistency argument and uniform audit quantifiers; a separate
review checked the assembly. This review status does not establish the missing
native runtime adapters or replace machine checking.
The owning
[passage restriction layer](../../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
is what supplies consistency/completion; the scalar inequality alone does
not. [ObservedChoice](../../GameTheoryExtensions/Math/Probability/ObservedChoice.lean)
factors observation-local auxiliary choices into source behavioral kernels
under explicit probability premises. It is useful for more general whole-policy
simulation adapters, but does not prove those premises for a real packet
backend. This note does not assert that every source-equivalent protocol can
be represented by the particular paired-action constructor.

## A complete local necessity result over all bounded utilities

There is a sharp information test in a smaller, fully specified problem.
Nature draws a finite hidden state theta and source observation X. One player
observes X and chooses from a finite action menu; payoff can be any bounded
function of (theta,X,action). The target keeps the same menus and payoffs,
and forcibly provides an extra finite observation Z before the choice.
There are no other actions, fees, punishments or future chance draws.
Compare the joint law of (theta,X,action).

**Paper equivalence.** Every selected source equilibrium action law is
implemented by a target equilibrium for every bounded utility specification
if and only if

\[
\Pr(\theta\mid X=x,Z=z)=\Pr(\theta\mid X=x)
\]

on every positive-probability target observation, provided the utility family
permits a two-action decision menu. For a fixed menu containing only one
action, informative observations have no strategic effect.

**Sufficiency.** Copy each source action lottery, ignoring Z. Conditional
expected utilities of every action are unchanged. All beliefs are ordinary
positive-reach Bayes beliefs; action trembles give consistency.

**Necessity.** If a posterior changes at (x,z), choose an event E of hidden
states whose posterior q there exceeds its source probability p at x;
complement E if necessary. Choose p<t<q. Safe pays t. Bet pays one on E and
zero otherwise at X=x; at other source observations give Bet zero. Source
Safe is uniquely optimal everywhere. Target Bet is strictly better at (x,z),
which has positive probability. No target equilibrium has the all-Safe source
joint law. All utilities lie in [0,1]. This is an actual nonexistence of a
preserving equilibrium for the chosen finite game, not just a broken proof.

For an observation refinement (X,Z), the displayed identity is equivalently
an ancillary channel Z|X on supported states. It makes the refined experiment
a state-independent garbling of X, while projection to X is the reverse
garbling. This is the finite decision-theoretic notion of Blackwell equivalence;
the general comparison-of-experiments framework is developed in
[Blackwell's original paper](https://doi.org/10.1214/aoms/1177729032).
The equivalence and separating decision above are proved directly here.

This local result does not characterize multiplayer SE preservation. Separate
players can receive individually ancillary but correlated records; public
randomness can coordinate their choices. An experiment-equivalence statement
at one decision also says nothing about menus, fees, future chance prediction
or off-path consistency. The replay and continuation clauses in the positive
theorem address those different obligations. Nor is every listed sufficient
condition independently necessary: different games can tolerate information,
fees or admission failures that a universal utility class cannot.

## Preservation, reflection and the knowledge boundary

The assembled theorem is forward implementation and belief transport, not
reflection. Even a fair public coin, independent of all hidden state, can add
correlated target equilibria: in a two-player matching game the players copy
the coin, producing half (A,A) and half (B,B) with no mismatches. That joint law
is not a source Nash/SE outcome without the coin. Ignoring it nevertheless
implements every source equilibrium. The complete example is in
[preservation-and-robustness.md](preservation-and-robustness.md). Enforcement
does not convert a forward theorem into an all-target-equilibria theorem.

Formally the configuration order is public B, then fixed K(B), then a builder
S in its class, then any source SE A, then a preserving target assessment.
The assessment can depend on S. This is distinct from a single complete
strategy implementable by players who know only B. The clean selector may be
a common public rule, but dirty-site equilibrium completions need not be.

Unknown persistent builders require a Bayesian game with a specified common
prior. Uniform pointwise collection bounds survive arbitrary posterior
averaging. Information fidelity instead needs the actual joint replay law
to satisfy (1): a builder type correlated with a hidden source type can leak
it through runtime observations even if each fixed builder looks harmless.
Independent builder uncertainty with source-public processing provides a
useful sufficient instance. Prior-free ambiguity, strategic miners, coalitions
sharing private receipts, external markets, computationally bounded policies,
and unfunded or costly escrow are outside this theorem.

The source language can remain abstract. What must be concrete is the backend
proof: enumerate raw choices and observations, prove which choices have a
source-behavior simulation, derive the channel and logical-kernel identities,
and establish collectible incentives for the remainder. Nothing here requires
pending packets to be physically invisible, and no unclassified physical
channel is excused by an honest-client abstraction.
