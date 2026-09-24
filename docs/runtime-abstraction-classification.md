# Classifying runtime abstractions

## Question and scope

Fix a finite runtime game and a finite outcome interface `O`. In Vegas, `O` can
be initial private types paired with final public results. Utilities are arbitrary
functions `O -> Player -> Real`; packet identities are not themselves rewarded.
The question is which abstractions preserve sequential equilibrium uniformly
over these utilities, and which additional abstractions become sound when
utility is fixed to the program's declared payoff.

Use the existing Kreps--Wilson predicate, whole continuation deviations and
one common fully mixed sequence. This analysis introduces no runtime or syntax.

The operational investigation proceeds by
[restricting one feature of the current runtime](runtime-feature-restrictions.md)
and studying what survives when that restriction is lifted. Each comparison
holds the surrounding application and service fixed and seeks a requirement
on further abstractions retaining the relevant game. The generic results below
support those comparisons; they do not replace the missing same-runtime
equilibrium proofs with classifications of unrelated terminal experiments.

## Checked results and their boundaries

- The [incentive-cone criterion](../GameTheoryExtensions/Protocol/SequentialIncentives.lean)
  and [SE criterion](../GameTheoryExtensions/Analysis/Protocol/Sequential.lean)
  characterize utility-uniform preservation between supplied assessments.
- [Continuation simulation](../GameTheoryExtensions/Protocol/ContinuationSimulation.lean)
  is a compositional sufficient certificate matching prescribed and deviating
  outcome laws with the same finite mixture of source comparisons. It works
  without finite outcomes; target consistency and initialized-law equality are
  separate obligations. The [private alias theorem](../Interaction/ReactiveAliasEquilibrium.lean)
  supplies an operational positive instance of erasing private response names.
- [Observation abstraction](../GameTheoryExtensions/Analysis/ObservationAbstraction.lean)
  classifies a terminal single-player experiment against full state information:
  preserving the retained fact permits erasure; merging positive-prior states
  with different facts admits a reporting-utility obstruction. Necessity uses
  an action menu that can report the finite retained fact; lost information need
  not matter in a fixed game whose actions cannot exploit it. Sufficiency applies
  to arbitrary action carriers and utilities of fact/action pairs. This is not a
  rule for arbitrary multiplayer metadata: payoff-irrelevant signals can
  coordinate players or become evidence later.
- The [terminal protocol adapter](../GameTheoryExtensions/Analysis/Protocol/DecisionExperiment.lean)
  proves the same classification for standard sequential equilibrium. It covers
  every consistent assessment, whole continuation-policy deviations, one common
  perturbation sequence, and the actual initialized fact/action law. For finite
  states and finite nonempty action menus, preserving the fact equates the full
  sets of sequential-equilibrium outcome laws.
- The [four-observation experiment](../GameTheoryExtensionsTests/ObservationQuotients.lean)
  checks every map from four observations to four labels: 256 candidates, 84
  retaining the chosen fact. `finite_labels_complete` covers arbitrary signal
  carriers by relabeling their finite images. Labels can present the same partition.
- The [coalescing experiment](../GameTheoryExtensionsTests/CoalescingEquilibrium.lean)
  separates outcome implementability from a utility-independent compiler using
  actual SEs. It does not establish an outcome abstraction impossibility.
- The [fixed-payoff classification](../GameTheoryExtensions/Analysis/ObservationPayoff.lean)
  permits observation erasure exactly when each supported observation fiber has
  a common maximizing action. Its [protocol theorem](../GameTheoryExtensions/Analysis/Protocol/DecisionPayoff.lean)
  preserves every abstract SE's retained law for this one payoff. It does not
  assert equality of the two games' complete sets of equilibrium outcome laws.
- [Continuation decisions](../GameTheoryExtensions/Analysis/Protocol/ContinuationDecision.lean)
  reduce whole-policy deviations at an actual protocol information site to
  posterior rewards. Rational responses use only maximizing actions. The
  posterior may be non-degenerate, and the payoff is fixed. The earlier binary
  disclosure obstruction is an instance.
- [Induced information advantage](../GameTheoryExtensions/Analysis/Protocol/InducedInformation.lean)
  bounds a deviator's gain by an informed benchmark minus the best score
  attainable from an observer's partial signal. It supplies a positive uniform
  gap from a relevant observation collision and lifts feasible deviations to
  initialized rationality bounds. The native selective-association proof uses
  its probability and continuation results directly.

The finite real-algebra reduction below is not a Lean theorem or implemented solver.

Precisely, the terminal criterion is that `q(s) = q(t)` implies
`fact(s) = fact(t)` on the prior support. It is equivalent to all-utility
preservation of every coarse optimum's fact/report law against full information.
Under this condition, the sets of optimal fact/action laws agree for every
utility and action carrier. The policy translations are utility-independent.
The observation `fact` itself passes the criterion, and every passing
observation determines it through a decoder on the prior support. Thus it is a
coarsest safe observation in this terminal class. This conclusion does not apply
to general multiplayer games or to a runtime that is itself only partially informed.

## Preservation statements and quantifiers

Let `A` be the abstract game and `R` the runtime game. Write `a = (sigma, mu)`
for an assessment, `Cons_G(a)` for consistency, `SE_G(u, a)` for sequential
equilibrium, and `L_G(a)` for the initialized law on `O`.

Three statements must remain distinct:

1. **Uniform assessment lifting.** Choose an assessment map `T` independently
   of utilities. For every consistent `a`, its image is consistent, has the same
   outcome law, and satisfies every utility for which `a` is an equilibrium.
   The strategy component must be induced by a playerwise compiler when this is
   advertised as compilation; beliefs may use the full assessment mathematically.
2. **Preservation by a fixed strategy compiler.** Choose playerwise maps `F_i`
   independently of utilities, opponents and analyst beliefs. Require
   `forall u sigma mu, SE_A(u, (sigma, mu)) -> exists nu,
   SE_R(u, (F sigma, nu))` and the same `O`-law. The target beliefs may depend on
   `u`. A uniform assessment lift is a sufficient certificate, but the checked
   fixed-assessment cone criterion is not asserted necessary for this statement.
3. **Outcome implementability.** Require
   `forall u a, SE_A(u, a) -> exists b,
   SE_R(u, b) and L_R(b) = L_A(a)`.
   The target strategies may also depend on utilities. This says nothing about
   one executable compiler.

The first implies the second when its strategy component has the required form;
the second implies the third. The relevant distinction is `exists b, forall u`
versus `forall u, exists b`. A failed comparison for one proposed `b` does not
rule out all other native assessments. The
[selective-association separation](selective-association-proof-contract.md)
does rule out outcome implementability for its specified games and utility.

Fixing `O` is substantive: a constant makes outcome comparison uninformative;
the entire native trace can forbid useful erasures by definition.

### Coalescing exposes the quantifier distinction

The one-player abstract game offers `x`, `ya`, `yb`. The split game offers
`x` or `y`, followed by `a` or `b` after `y`. Both utilities give `x` payoff two;
one rewards `a` by one and `b` by zero, the other reverses them. The same abstract
`x` assessment is an SE for both. Each utility has a native SE with outcome `x`,
but no native strategy is rational for both at the off-path `y` decision.
If the compiler can inspect declared utilities, it can choose the appropriate
continuation. The checked impossibility concerns a utility-independent compiler,
even one that sees the whole source profile and chooses utility-dependent beliefs.

### Restricting utility to the declared payoff

If program `p` declares payoff vector `r(p)`, requiring utility to equal that
vector permits a compiler to inspect it through `p`. The relevant contract is
`SE_source(r(p), a) -> exists b, SE_native(r(p), b)` with the chosen retained law
preserved. A compiler contract additionally requires
`b.strategy = F_p(a.strategy)`, with a playerwise executable `F_p` when that is
the advertised interface. The payoff is fixed before source equilibria are
quantified. Choosing a separate target assessment for each equilibrium is
weaker than constructing such a compiler.

This restriction removes contradictions that require the same program and
strategy translation to work for two conflicting external utility functions.
It does not remove impossibilities already established for one declared payoff.
Nor does it exclude new target deviations: a receiver may still profit, under
that same payoff, by using evidence the source hid.

For terminal decisions the exact fixed-payoff criterion is particularly simple:

> For every supported observation fiber, the sets of maximizing actions at its
> constituent states have a nonempty intersection.

The checked theorem equates this condition with preservation of every abstract
optimum's retained fact/action law by some fully informed optimum. If a match
exists, the direct lift that ignores the extra information already works.
The protocol theorem gives the same statement for standard SE, including all
consistent assessments and whole-policy deviations.

The [fixed-payoff tests](../GameTheoryExtensionsTests/ObservationPayoff.lean)
include a hidden bit that changes the reward amount without changing the best
action. Erasing this bit preserves the fixed-payoff equilibria, although the
all-utility classification rejects the erasure. Changing to the single fixed
correct-report payoff makes the same erasure fail, even with payoff-dependent
target strategies. Thus payoff-specific compilation helps precisely where
the additional information does not require a different optimal decision.

This is a directional preservation statement. For constant payoffs, for
example, an informed equilibrium may correlate its action with the hidden fact
in a way that no abstract policy can reproduce. Such additional target
equilibrium outcomes do not prevent preserving every source equilibrium.

## How the generic results factor the native impossibilities

The terminal observation classification alone cannot be substituted into an
arbitrary multiplayer continuation. The enclosing game must establish what
the player knows, which decisions are feasible, and how their consequences
contribute to the initialized outcome.

The continuation-decision theorem provides the first reusable bridge: a
history-wise reward law, common response distribution, and legal pure-decision
policies imply an exact posterior-optimality criterion at the actual site.
It covers partially informative beliefs and every whole-policy deviation.
The rejected-opening binary obstruction obtains its continuation values and
rationality bound from this theorem.

The induced-information theorem provides the second bridge. Suppose an
inducing deviation gives one recipient score at least `b`, while another
recipient's score is bounded by a policy based only on signal `q(s)`. If
`V(q)` is the best expected score using that signal, the inducing player's
expected advantage is at least `b - V(q)`, under the stated payoff inequality.
This is uniform over the less informed recipient's policy. An observation
collision gives `V(q) < 1` for finite correct-report actions, so perfect informed
reporting yields a strictly positive gap. Publication loss or informed error
can be accounted for by a smaller certified benchmark `b`.

In the [selective-association proof](selective-association-proof-contract.md),
the concrete secrecy and evidence arguments supply the premises: Alice can
induce a fair bit, Bob must report it correctly, Carol's report law does not
depend on that bit, and Alice can still open. The generic calculation yields
`1 - 1/2`; the generic continuation lift turns that deviation guarantee into a
lower bound on every rational target assessment's initial payoff. The actual
source equilibrium and its zero payoff remain separate proved facts.

This factors the strategic calculation without erasing the service assumptions.
It does not subsume obstructions from missing opening capabilities, scarce
transmission opportunities, replay-sensitive inclusion, or compiler recovery.
Those change available continuations and their effects, rather than only an
observer's information.

## The exact semantic criterion

For fixed assessments, each deviation gives a difference vector on `O`:

`d = law(prescribed continuation) - law(deviating continuation)`.

Sequential rationality says `dot(d, u_i) >= 0` for every deviation of player `i`.
Let `C_G(a,i)` be the closed convex cone generated by those differences. The
checked theorem states, for a consistent abstract assessment:

> A fixed native assessment preserves sequential equilibrium for every utility
> if and only if it is consistent and each native incentive difference belongs
> to the corresponding abstract cone.

Outcome-law equality is a separate obligation. The cone family may be infinite;
the theorem is not an algorithm. Finite nonnegative combinations are checked
sufficient certificates. Failed cone inclusion supplies a separating utility,
which refutes this fixed assessment lift.

A useful characterization for the weaker outcome question is also available
directly from the definitions. Let `U_G(a)` be the set of utility profiles making
assessment `a` sequentially rational, and define

`V_G(p) = union { U_G(a) | Cons_G(a) and L_G(a) = p }`.

Then all-utility outcome implementability is equivalent to
`V_A(p) subset V_R(p)` for every outcome law `p`. To see this, membership in
either union is precisely existence of a consistent, rational assessment with
that law. These unions need not be single convex cones. This characterization
identifies the right quantifiers; converting it into structural or computational
certificates is the substantive work.

## A finite class that can be enumerated

Start with an unfolded finite perfect-recall game tree and fixed chance kernels.
Legal histories include deviations. Initially retain the decision calendar and
enumerate finite maps on histories, information sets and actions, requiring:

- prefixes, terminals and the mover agree;
- terminal observations factor through the map to `O`;
- each abstract information set has a well-defined action menu;
- action maps are constant on the acting player's information sets;
- projected transition laws are independent of the representative of an
  abstract history/action;
- the abstract information structure has perfect recall.

These are well-formedness conditions, not preservation certificates. Quotient
labels come from bounded finite sets; projected probabilities come from runtime
kernels. Complete enumeration of this class remains open beyond the checked
observation experiment. Coalescing additionally exposes contingent plans as
actions and needs a separate transformation grammar and preservation statement.

Order candidates by factorization. For the terminal experiment, the retained
fact gives the natural coarsest sufficient observation on prior support. A
greatest safe quotient for general games is not assumed to exist or not exist;
closure under joins is a separate question.

## An exact decision procedure in principle

Graf, Engesser and Nebel construct polynomial constraints for all SEs of a
finite perfect-recall game and solve them by cylindrical algebraic decomposition
(CAD). Theorem 15 treats consistency; Section 4 assembles the system and describes
its rational-coefficient implementation and scaling limits. Their displayed
reach formula suppresses chance factors; our adapter must account for them.
[Symbolic Computation of Sequential Equilibria,
AAMAS 2024](https://www.ifaamas.org/Proceedings/aamas2024/pdfs/p715.pdf)

The comparison reduction below is our proposed application, not that paper's
theorem or a Lean formalization.

Use two explicitly finite perfect-recall game trees with rational fixed chance
probabilities and finite terminal maps to the same `O`. This restriction concerns
the effective input: quantified utility values can range over all reals.

Remove zero-probability chance branches and empty information sets. Chance stays
fixed during perturbation; positive chance factors enter the reach polynomials.
Parameterized chance kernels that can acquire zero entries need support cases.

An assessment has finitely many real strategy and belief coordinates. Simplex
constraints enforce nonnegativity and normalization. Initialized outcome laws
`L_G(sigma)` are finite sums of reach polynomials grouped by `O`.

A fallback to the specialized polynomial construction is to encode the limit
definition itself. For an assessment `a`, require its simplex constraints and

`forall epsilon > 0, exists b,
  FullyMixed(b.strategy) and Bayes(b) and distanceSquared(a,b) < epsilon^2`.

For every decision information set `I` and history `h` in it, Bayes consistency
is the polynomial equation

`b.belief(I,h) * reach_b(I) = reach_b(h)`.

Fully mixed strategies and positive chance support give every legal history
positive reach, so these equations specify Bayes conditioning. One vector `b`
covers all coordinates. In finite dimensions this condition is equivalent to a
common convergent sequence: use distances `1/n` in one direction and convergence
in the other. Independent perturbation rates at different sites are not assumed.

For rationality, quantify a whole replacement behavioral policy, represented
by its finitely many simplex coordinates, at each information set. The expected
continuation payoff is polynomial in strategies, beliefs, and `u`. This avoids
assuming a one-shot-deviation principle before proving its applicability to the
operational adapter. Together these give a first-order real formula
`SE_G(u,a)`, even without first eliminating its internal quantifiers.

All-utility outcome implementability becomes the closed real formula

`forall u a,
  SE_A(u,a) -> exists b, SE_R(u,b) and L_R(b) = L_A(a)`.

Its negation supplies one utility and one abstract equilibrium whose outcome
law no native equilibrium matches. Unlike a failed fixed-lift cone test, this
is the full outcome impossibility quantifier.

For a *specified* playerwise compiler `F` with an effective semialgebraic graph,
add `b.strategy = F(a.strategy)` to the existential clause. The compiler must
be total on legal source policies and independent of utilities; its graph and
playerwise property are separate proof obligations. Polynomial action-map
lifts are a simple candidate class. A rational formula must explicitly handle
its denominator domains.

Real quantifier elimination applies to these finite formulas with rational
coefficients, even with all real utility coordinates quantified. An arbitrary
unknown compiler function is not one real variable: synthesis requires a finite
grammar or finite-dimensional semialgebraic family, whose parameters are
quantified before utilities and strategies.

This completeness route needs a verified finite-game adapter, formula translation
and real-algebra engine. It is not a practical proposal for the whole Vegas tree.
Failure to find a structural certificate must return `unresolved`, not impossibility.

## Relation to established theory

- Bergemann and Morris compare multiplayer information through Bayes correlated
  equilibrium outcomes, a different static solution concept. [Theorem 2](https://economics.mit.edu/sites/default/files/publications/paper_79_bce.pdf)
- Battigalli, Leonetti and Maccheroni characterize behavioral equivalence by
  coalescing and interchanging/simultanizing, for finite perfect-recall structures
  without chance. Their reduced-strategy/terminal-path equivalence does not
  itself establish our utility-independent assessment translation.
  [Behavioral equivalence of extensive game structures](https://didattica.unibocconi.it/mypage/upload/48808_20200512_034701_BATTI-LEO-MACCHE2020GEB.PDF)
- Halpern, Pass and Seeman prove computational SE preservation from representation
  conditions. Their history map preserves depth and mover; extra runtime
  activations do not automatically fit. This is relevant to a future backend.
  [Computational Extensive-Form Games, Definition 3.4 and Theorem 4.5](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf)
- Dilmé's integer-power sequences suggest finite relative-tremble-rate
  certificates, without an established uniform exponent bound for our search.
  [Proposition 4.2](https://d-nb.info/1314875949/34)

## Next proof opportunities

1. Complete the [passive-observation comparison](runtime-feature-restrictions.md)
   on the existing native fixture: prove the restricted native equilibrium,
   retaining the same application, service and payoffs. The enabled-observation
   native payoff bound is checked; the restricted native equilibrium is open.
2. Instantiate the checked
   [observation requirement](../GameTheoryExtensions/Analysis/Protocol/ObservationRequirement.lean)
   on native continuation decisions. The
   [restricted native prefixes](../VegasTests/SelectiveAssociationRestricted.lean)
   and [certificate acquisition constraint](../Vegas/Pending/ReactiveEvidenceOrigin.lean)
   establish operational parts of that argument. Distinguish an
   observation-respecting lift from unrestricted initialized outcome
   implementation; the latter needs the induced-deviation argument.
3. For partially informed fine and coarse observations, investigate equality of
   posterior laws of the retained fact on merged fine fibers. Conditional
   averaging suggests sufficiency; different posteriors suggest a separating
   threshold decision. This stronger criterion is not the checked `Determines`
   theorem, which compares against full state information.
4. Use the continuation-decision and induced-information results to classify
   further evidence interfaces. A structural criterion deriving all operational
   premises from an arbitrary runtime abstraction remains open; the
   [selective-association witness](selective-association-proof-contract.md)
   supplies one concrete instantiation.
5. Derive finite incentive generators and explicit perturbation certificates
   from structural presentation maps, without assuming the desired preservation.
6. Instantiate the classification on native response distinctions before
   asserting a minimal or sufficient ambient source interface.

Generic results belong in `GameTheoryExtensions/`, operational certificates in
`Interaction/`, and compiler instances in Vegas. A family of services adds an
explicit quantifier; effective classification requires its parameterization.
