# Full-source semantics and downstream migration

## Status and source decisions

The checked deferred-publication component supplies consistency, immutable
bindings and publications, incremental obligation registration, and ordinary
honest feasibility. It does not define the complete revised source language.
The active `VegasCore` semantics and its compiler theorems remain unchanged.

Integrating continuing failure requires a programmer-visible typing choice.
Currently `reveal` introduces an ordinary public value of type `A`. Its
continuation cannot receive a failure outside `A`. Changing only the
operational relation would leave expression, distribution, and payoff
evaluation without an inhabitant of their expected input type.

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
K : PublicView -> RationalLaw A
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
   choices in the proposed source operational game.
3. Opening cannot replace the private candidate. Guard rejection changes the
   public result, not the player's retained private knowledge.
4. Deferred guards are ordinary relations. Their null-vacuous lifting and
   pending status belong to publication semantics, not partial expression
   evaluation.
5. A public value with an outstanding relational obligation is observable
   but is not certified to satisfy that relation. Previous public effects
   are never retracted.
6. Player policies see their information, including retained private values
   and public results. Executable guard evaluation uses publicly available
   resolved dependencies. These are different interfaces.
7. Failure is per publication. Permanent withdrawal is a separate additional
   rule, not an implicit consequence of one failed opening.
8. Public pending traffic and raw failed-opening payloads remain observable in
   target models. A result-store projection cannot erase their strategic effect.

The source visibility discipline must prove that unresolved private
dependencies of a guard belong to its author. Earlier public values, including
chance results, are already available; an older guard cannot depend on a
future chance draw. Owner equality does not replace authenticated authority or
timely-service assumptions in a runtime.

## Source acceptance milestone

Before changing downstream compiler interfaces, construct and check one complete
source semantics with all four constructors and the following properties:

- Heterogeneous payloads and ordinary nullable payloads.
- Private initial values, distinct from their public disclosure results.
- Invalid/unopenable binding choices and informed withholding at reveals.
- Deferred relational guards, including reverse-order partial disclosure.
- Programmer-defined settlement on failures and on successful publication.
- Public dependent chance with a total law in every admitted public state.
- Fresh names and an explicit resolution obligation for every sealed resource.
- A utility-free source game with observation-local policies at both binding
  and disclosure decisions, not just the existing commit-only policy carrier.
- Concrete ordinary successful play and nonconstant failure-sensitive utilities.

Resolve these admission details explicitly while defining the source interface:

- Raw syntax currently permits repeated aliases, while checked accounting
  prevents repeated discharge. Specify the checked resource contract; do not
  silently turn failure into either retry or permanent withdrawal.
- Existing conditional-copy accounting may discharge an original binding
  without a literal reveal of it. Its replacement must express the intended
  optional disclosure, or identify a further language-design choice before
  removing that capability.
- Ordinary honest feasibility and operational totality are different claims.
  Unconditional availability of failure does not justify admitting an
  allegedly useful game with no ordinary successful play. Decide the checked
  feasibility contract without importing a desired strategic theorem as a
  well-formedness field.

## Migration order and proof obligations

1. **Source interface and semantics.** Implement the agreed result typing,
   expressions, states, obligations, decisions, and execution
   together. Prove local consistency and preservation of private knowledge;
   exercise all constructors in one mixed-feature source example.
2. **Typed graph edge.** Compile every revised source constructor and retain
   expression code, guard support, publication provenance, and observations.
   Prove honest laws and causal unilateral-deviation correspondence for this
   edge. No homogeneous, sample-free, or always-accepting fragment substitutes
   for full constructor coverage.
3. **Logical/public-message edge.** Adapt the typed ordered application to
   publicly resolvable deferred guards, immutable candidate acceptance,
   source-defined failure, and the exact chance law. Reuse the shared message
   runner and independent service contracts. Do not retain a private-validation
   oracle as the purported ordinary public implementation.
4. **Strategic composition.** Establish graph-relative causal comparison laws
   with unchanged opponents. Derive utility bounds from stated source
   incentives for optional withholding and invalid binding choices, rather
   than assuming native checkpoint inequalities. Compose the source edge and
   backend edge to obtain the end-to-end Nash theorem.
5. **Ledger and VM.** Realize authenticated calls, atomic application steps,
   reverts, deadlines, costs, bounded code, and cryptographic services through
   additional independently specified edges.

Retain stronger exact-law results where they hold; informed failure may need
utility domination instead. Full language coverage never means hiding a
partial compiler branch behind a feasibility or service assumption.

## Work allocation and retirement

The coordinating agent owns source meaning, typed interfaces, theorem scope,
integration, and status. Delegate expression implementation, source execution,
and independent mathematical review only after shared interfaces are settled.
Use disjoint files and one coordinated Lean build slot.

Port downstream edges after the source acceptance test passes. Superseded
modules may move to passive `archive/` references while their useful proofs are
consumed; remove them when no longer needed. Do not maintain aliases or a
second active implementation for compatibility. Do not remove build imports
while still claiming that the corresponding compiler edge is checked.

At each milestone, report the source coverage, deepest compiled target,
strongest proved strategic conclusion, assumptions, and next missing edge.
Keep `Paper.lean` as direct delegation to actual repository capstones and
identify pursued but unproved paper statements explicitly.
