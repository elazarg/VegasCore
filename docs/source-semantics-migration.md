# Full-source semantics and downstream migration

## Status and source decisions

`Vegas.Source` defines the complete failure-aware source semantics: all four
constructors, typed result expressions, arbitrary binding and disclosure
policies, private action recall, and dependent public chance. Checked terminal
theorems establish resolution of every publication obligation and satisfaction
of every retained guard, under arbitrary policies. The complete source also
has a checked compiler to the typed sequential `Vegas.Graph` IR, with exact
honest and unilateral-deviation laws and same-error Nash equivalence. This edge
has no failure-dominance or finite-domain premise. The candidate-message pipeline
still consumes `WFProgram` through `Vegas.EventGraph`; the complete native
theorem remains a separate goal.
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

The source visibility discipline must prove that unresolved private
dependencies of a guard belong to its author. Earlier public values, including
chance results, are already available; an older guard cannot depend on a
future chance draw. Owner equality does not replace authenticated authority or
timely-service assumptions in a runtime.

## Source acceptance milestone

This milestone is checked in `Vegas.Source` and `VegasTests.SourceSemantics`.
The tests establish complete execution laws and actual payout laws for the
mixed program; `Paper.lean` delegates to the general terminal-resolution and
guard-satisfaction theorems. The checked source-to-`Vegas.Graph` certificate
complements these source results; it does not establish the remaining
typed-graph-to-native-message edge. `Vegas.EventGraph` is not an additional
required target between them.

The acceptance criteria are one complete source semantics with all four
constructors and the following properties:

- Heterogeneous payloads and ordinary nullable payloads.
- Private initial values, distinct from their public disclosure results.
- Invalid/unopenable binding choices and informed withholding at reveals.
- Deferred relational guards, including reverse-order partial disclosure.
- Programmer-defined settlement on failures and on successful publication.
- Public dependent chance with a total law in every admitted public state.
- Fresh names and an explicit resolution obligation for every sealed resource.
- A utility-free source game with observation-local policies at both binding
  and disclosure decisions, not just the existing commit-only policy carrier.
- Concrete ordinary successful play with nonconstant, failure-sensitive
  utilities, including an explicit payoff branch for invalid publication
  results. This is an acceptance example, not a feasibility requirement for
  every well-formed program.

The source interface settles the admission details as follows:

- Every initial private binding and each commitment creates one resolution
  obligation. A reveal removes exactly that obligation and adds a fresh public
  result alias. Terminal syntax requires no obligations remaining; fresh names
  prevent duplicate resource identity or alias replacement.
- A reveal policy chooses disclosure or failure using its current source
  information. This expresses optional disclosure without copying an ordinary
  value as an implicit failure default. It is neither retry nor permanent
  withdrawal.
- Operational totality and ordinary failure-free feasibility are different
  claims. Admit unsatisfiable guards: failure is a source behavior, while
  well-formedness is structural and accounts for resources. A satisfying
  ordinary execution is a separate optional property, not an execution
  prerequisite.

## Migration order and proof obligations

1. **Source interface and semantics.** Implement the agreed result typing,
   expressions, states, obligations, decisions, and execution
   together. Prove local consistency and preservation of private knowledge;
   exercise all constructors in one mixed-feature source example.
2. **Typed graph edge (checked).** Compile every revised source constructor and retain
   expression code, guard support, publication provenance, and observations.
   The checked honest and unilateral-deviation laws cover the full language;
   no homogeneous, sample-free, or always-accepting fragment substitutes for
   full constructor coverage.
   The [source-to-graph design](source-graph-edge.md) specifies operation-specific
   binding and resolution nodes, immutable fields, guard placement, and own
   action recall without additional expression-construction assumptions.
3. **Public-message edge.** `GraphRuntime` directly hosts every typed graph
   operation in the shared message application, with public deferred checks,
   immutable candidate acceptance, explicit failure, and conditional chance.
   The local transition laws and mixed-feature transport tests establish its
   operational boundary. The prescribed-policy compiler and local command laws
   are implemented. Whole-program observation correspondence, completion under
   the concrete reserved service, and the whole-run honest law remain to be
   proved. See the
   [graph-to-message proof plan](typed-message-edge.md).
4. **Strategic composition.** Establish the exact unilateral-deviation mixture
   law under canonical ordered operations, with unchanged compiled opponents
   and one fixed admissible adaptive environment. Add utility bounds only for
   actions, information, or costs genuinely introduced by a later target edge.
   Compose the source edge and backend edge to obtain the end-to-end Nash theorem.
5. **Ledger and VM.** Realize authenticated calls, atomic application steps,
   reverts, deadlines, costs, bounded code, and cryptographic services through
   additional independently specified edges.

The present source objective is exact law because reveal and failure choices
belong to source strategies. No inherent need for a separate informed-failure
domination premise has been demonstrated. Full language coverage never means
hiding a partial compiler branch behind a feasibility or service assumption.

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
