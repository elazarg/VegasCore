# Source semantics and implementation contract

## Typed publication results

`Vegas.Source` defines the complete failure-aware source semantics: all four
constructors, typed result expressions, arbitrary binding and disclosure
policies, private action recall, and dependent public chance. Checked terminal
theorems establish resolution of every publication obligation and satisfaction
of every retained guard, under arbitrary policies. The complete source also
has a checked compiler to the dependency-driven `Vegas.EventGraph` IR, with exact
honest and unilateral-deviation laws and same-error Nash equivalence. This edge
has no failure-dominance or finite-domain premise. The full source-to-pending theorem composes this certificate with the
checked graph-relative runtime simulation. The [active tower](active-tower.md)
states the ideal-service boundary.
The design choices and examples are collected in
[source-design-rationale.md](source-design-rationale.md).

Continuing failure requires explicit typing. A continuation expecting an
ordinary public value of type `A` cannot receive a failure outside `A`.
Changing only the operational relation would leave expression, distribution,
and payoff evaluation without an inhabitant of their expected input type.

The agreed choice is **explicit typed publication results**:

- A publication has type `Result A`, distinct from ordinary nullable data of
  type `Option A`. Failure and successful publication of an ordinary `none`
  remain distinguishable.
- Expressions must explicitly eliminate `Result A` to obtain an ordinary
  value. A failure branch is programmer code, not a compiler-chosen default.
- Expression evaluation stays total. Payoff expressions produce ordinary
  integers, and distribution expressions produce normalized laws in every
  branch. Source chance does not acquire a failure action or a strategic
  publisher; its output remains an ordinary value.
- Retain `ret`, `sample`, `commit`, and `reveal`. Add result inspection to the
  embedded expression interface, not another rich protocol language.

Programmer convenience belongs in the frontend. The core keeps explicit
failure handling rather than separate success/failure protocol continuations,
implicit ordinary defaults, or automatic failure propagation.

## Chance and distribution annotations

**Working decision: retain primitive public chance.** Keep `sample` distinct
from player-controlled commitments, and revisit this representation if a
uniform input interface demonstrably simplifies the complete semantics and
compiler. No distribution-annotation feature is added by this decision.

A sample specifies a conditional kernel as part of the program:

```text
K : PublicView -> FinDist A
```

It draws once at the specified source step and publishes the result. A player
does not choose whether to obey that kernel, replace the result, or withhold
its publication in this source operation. This is an abstract specification,
not evidence that every target runtime supplies the required service.

A distribution annotation on a commitment can have different meanings:

- An assumption about a reference player's policy fixes or constrains that
  policy for the analysis. Ordinary deviations may still replace it.
- A restriction on admitted strategies also restricts the deviations quantified
  by a theorem. The restriction must be explicit, especially when the intended
  runtime permits those strategies.
- A prescribed nonstrategic policy can represent chance through a synthetic
  controller. This is a possible representation of the same operation, not an
  impossibility to be ruled out.

A direct equivalence for the third encoding uses the corresponding information
and execution contract: the prescribed conditional law, matching publication
timing and visibility, and no extra choice to replace, fail, retry, or delay the
result. Fixing the synthetic controller in the comparison, or giving it a
singleton admitted strategy class, supplies the nonstrategic policy contract.
More permissive implementations may also be equivalent, but need their own
refinement argument. Merely assigning an unrestricted controller constant
utility does not restrict its possible behavior or establish the outcome and
deviation laws.

The probability contract concerns the joint law, not just a marginal. If a
private bit `X` is fair, a commitment to `B = X` is marginally fair too, but its
publication reveals `X`. Even fairness conditional on the prior public view
does not rule this out. The source sample instead draws from `K(public view)`
conditional on the complete source prehistory, including previously chosen
private values. A realization must preserve the appropriate conditional law
or prove the weaker observation-relative law actually used by the theorem.

Annotations can usefully describe prescribed randomization, partial distribution
constraints, or private inputs. Such descriptions belong initially to profile,
setup, or capability assumptions; they need not replace the primitive which
specifies an exogenous public draw. Internal execution interfaces may share
machinery for strategic and fixed-kernel inputs without identifying their
deviation contracts.

Every backend covering the full language must give `sample` an implementation
under a named chance-service contract. A contract which permits selective
withholding, biased selection, or resampling does not implement this operation
merely because it labels a provider's commitments random. If a target cannot
realize the stated source kernel, report the missing capability or the need
for a different source mechanism; do not silently exclude programs with samples.
Programs without samples need no chance-service assumption.

## Settled contracts

These guide the implementation independently of its representation:

1. Failure is outside the ordinary payload domain.
2. Commitment fixes a value or an unopenable candidate without checking its
   guard immediately. Guard validity must not restrict away invalid binding
   choices in the source operational game.
3. Opening cannot replace the private candidate. Guard rejection changes the
   public result, not the player's retained private knowledge.
4. Deferred guards are ordinary relations with static required support. Their
   lifting is vacuous when any required component fails and waiting when none
   has failed but some remain pending. No ordinary value is extracted from an
   unopened binding. Static support, including dead branches, is semantic;
   ordinary Boolean equivalence alone does not justify changing it.
5. A public value with an outstanding relational obligation is observable
   but is not certified to satisfy that relation. Previous public effects
   are never retracted.
6. Player policies see their information, including retained private values,
   public results, and their own action history. Executable guard evaluation
   uses publicly available resolved dependencies. These are different
   interfaces.
7. Failure is per publication. Permanent withdrawal is a separate additional
   rule, not an implicit consequence of one failed opening.
8. Public pending traffic and raw failed-opening payloads remain observable in
   target models. A result-store projection cannot erase their strategic effect.
   Compliant prescribed failure must avoid leaking rejected data omitted from
   the source view; arbitrary deviators remain free to transmit their own data.

The source visibility discipline requires that unresolved private
dependencies of a guard belong to its author. Earlier public values, including
chance results, are already available; an older guard cannot depend on a
future chance draw. Owner equality does not replace authenticated authority or
timely-service assumptions in a runtime.
