# PMF semantics and interaction bounds

## Finding

General PMF semantics removes the finite-support obstacle to fully mixed
strategies on countably infinite response menus. It does not by itself remove
the compiler theorem's fixed interaction horizon or supply the equilibrium
completion argument for an infinite runtime game.

This assessment inspects upstream GameTheory at commit
[06db68c12bba6d84c19ff94e6de821ec5c9a42e0](https://github.com/elazarg/GameTheory/tree/06db68c12bba6d84c19ff94e6de821ec5c9a42e0).
The checked-in dependency is e1aff265355a3383b9cba963259470e596a85c9c.
The upstream code was inspected in an isolated checkout; it was not rebuilt
here, and no dependency or compiler proof was migrated. Upstream's
[delivery record](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/docs/PMFRestorationWorklog.md)
reports the restoration's build and regression evidence.

## What upstream supplies

| Obligation | Upstream evidence | Limit |
| --- | --- | --- |
| Strategies and beliefs with infinite support | [Sequential assessment](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Analysis/Protocol/Sequential.lean) uses ordinary PMFs; sequential consistency no longer requires finite information-history fibers. | Full mixing still requires a law assigning positive mass to every legal choice. PMFs support countable discrete choices, not nonatomic full mixing over real-valued actions. |
| Concrete infinite-menu trembles | [Sequential regression](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Analysis/Protocol/PMFSequentialTest.lean) constructs geometric full-support choices, infinite-support beliefs and vanishing trembles around a pure choice. | This validates the semantic capability; it is not a compiler theorem. |
| Bayes beliefs over variable-depth histories | [Behavioral Bayes](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Protocol/BehavioralBayes.lean) sums first-arrival reach weights over antichain information fibers, including unbounded depths. | Correct information sets and recall still need proof. |
| Passing incentives through limits | [Sequential limits](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Analysis/Protocol/SequentialLimits.lean) transports whole-policy optimality through convergent assessments without finite state, history or action carriers. | The general result assumes bounded payoffs, convergent normalized strategy/belief laws, convergent approximations to every deviation, and finite continuation fuel. |
| Terminal laws without a uniform numerical horizon | [Backward execution](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Protocol/Backward.lean) constructs terminal PMF laws by well-founded recursion. | Well-founded legal play is stronger than almost-sure termination. This does not supply an unbounded-interaction SE preservation theorem. |
| Infinite play laws | [Infinite-play experiment](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Experimental/PostArchitecture/PMFInfinitePlayGate.lean) validates a measure construction and chronological marginals for stochastic games. | Experimental stochastic path semantics, not an existing general reactive-runtime SE bridge. |

The public [assessment compactness](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Analysis/Protocol/AssessmentCompactness.lean)
and [SE existence](https://github.com/elazarg/GameTheory/blob/06db68c12bba6d84c19ff94e6de821ec5c9a42e0/GameTheory/Analysis/Protocol/SequentialExistence.lean)
theorems still require finite carriers. The delivery ledger explicitly excludes
a general infinite-space equilibrium existence claim.

## Three restrictions to separate

1. **Finite alternatives at an activation.** The present finite message alphabet
   and fresh-binding value alphabet support finite-support full mixing. PMF
   permits genuinely countable alphabets instead. Arbitrary finite strings
   or integers are relevant examples. Preserving SE over those alphabets still
   needs a construction of the target assessment and its incentives.
2. **A fixed maximum number of interactions.** The reactive protocol stores a
   remaining activation budget, and service rosters are finite lists. Replacing
   their probability type leaves those restrictions intact. A random finite
   execution with no common bound needs terminal-law and continuation proofs;
   a deadline alone does not supply a bound on pending communication.
3. **Finite equilibrium completion.** Extra target information sites need
   rational behavior even after deviations. The current proof obtains it using
   finite equilibrium existence and extracts a common belief limit using finite
   compactness. Both steps require replacement when the relevant carriers become
   infinite, even if the number of execution steps stays bounded.

The third issue is mathematical, not just Lean syntax. For example, point
masses concentrated on successive natural numbers converge pointwise to zero:
each fixed number eventually receives no mass. Every subsequence indexed by a
strictly increasing sequence has the same pointwise limit, whose total mass is
zero. Thus arbitrary sequences of countable PMFs cannot inherit the finite
simplex's normalized-limit extraction argument. A migration needs explicit
belief limits or a proof preventing probability from escaping to arbitrarily
remote histories. This elementary argument identifies a proof gap, not an
impossibility for this compiler.

## Where the compiler currently uses these restrictions

- [Reactive protocol](../../Interaction/ReactiveProtocol.lean): explicit
  remaining budget, finite-fuel execution and termination rank.
- [Finite assessment](../../Interaction/ReactiveFiniteAssessment.lean): uniform
  finite-menu trembles.
- [Consistency completion](../../GameTheoryExtensions/Analysis/Protocol/ConsistencyCompletion.lean):
  common convergent subsequences of finite belief laws.
- [Agent completion](../../GameTheory/GameTheory/Analysis/Protocol/AgentCompletion.lean):
  finite Nash existence chooses off-path responses jointly.
- [Restriction extension](../../GameTheoryExtensions/Analysis/Protocol/RestrictionExtension.lean)
  and [terminal audit](../../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean):
  finite target histories and a certified terminal horizon.
- [Binding resources](../../Vegas/Pending/ReactiveBindingResources.lean):
  finite candidate capacity at least as large as the activation horizon.

## Migration order and research gates

The dependency also moves Lean/Mathlib from 4.34.0 to 4.34.1 and removes the
parallel finite-distribution API. A semantics-preserving port should first retain
the existing bounds and recover the existing compiler theorems. Real expected
utility now needs integration certificates; existing finite bounds can supply
them during this phase.

Then separate two generalizations:

1. **Countable response alphabets at a bounded horizon.** Replace uniform
   trembles with supported countable reference laws. First test the difficult
   part: a consistent, rational completion for the compiler's actual off-path
   subgames. Investigate explicit completion or sufficient control of belief
   tails, rather than assuming arbitrary countable-game existence. Only then
   remove alphabet and finite candidate restrictions where the proof permits it.
2. **No deterministic interaction bound.** Specify termination and settlement
   for the service, retain all intermediate observations and reactions, and
   derive terminal laws and continuation comparisons from finite prefixes.
   A candidate route uses uniform conditional termination-tail bounds for the
   perturbations and deviations used in the proof. This is a proposed research
   condition, not a checked sufficient condition for SE preservation. Root-level
   almost-sure termination alone does not discharge all off-path obligations.

The audit obligation remains separate: collectible expected punishment must
dominate possible gains at the relevant information sets. Infinite message
spaces or unbounded interaction do not themselves supply a uniform coverage
bound or bounded utility gains. These need explicit proofs or assumptions.

**Assessment:** the PMF port is a sound foundation for removing artificial
finite-alphabet restrictions. Removing the interaction cap is a plausible
further theorem project with identifiable obligations. It is not established
by upstream's port or by the present VegasCore compiler proof.
