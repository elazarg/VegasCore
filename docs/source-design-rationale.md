# Source design rationale

This note records the semantic choices for the failure-aware source language,
with small examples explaining their consequences. Source safety and the
source-to-pending outcome/deviation laws are checked under the explicit
ideal-service boundary. The mathematical publication rules are described in
[deferred-guards-semantics.tex](deferred-guards-semantics.tex).

## Publication results are explicit

A public disclosure has type `Result A`. It is either a successful ordinary
value `ok a` or a publication failure `fail`. This is intentionally different
from `Option A`: if `A = Option B`, then `ok none` is a successful publication,
whereas `fail` says that no ordinary `A` was published.

Expressions do not silently coerce `Result A` to `A`. They eliminate it:

```text
match disclosedBid with
| ok bid => ordinarySettlement bid
| fail   => failureSettlement
```

Payoffs and ordinary public expressions follow the same rule. A comparison
such as `disclosedBid < reserve` is not evaluated on failure, and failure does
not win the comparison vacuously. The program must say what payoff the failure
branch receives. Expression evaluation stays total without inventing zero,
`none`, or another ordinary default.

## Static guard support

A guard is written over ordinary values, with a statically declared set of
required components. Its lifted publication check has three cases:

1. if any statically required component has failed, the guard is satisfied
   vacuously;
2. otherwise, if any required component is pending, the guard waits; and
3. otherwise, it evaluates the ordinary relation on the published values.

Pending is not failure. While a component is pending, no ordinary value is
extracted from its private binding to run public guard code.

For example, for a guard `x = y`, public `x = true` and pending `y` produces
`wait`. It does not read the sealed candidate for `y`. If `y` later fails, the
guard becomes vacuously satisfied. If `y` publishes an ordinary value, the
equality is evaluated.

Static support is semantic, including support in a branch that is not selected
at runtime. Consider:

```text
guard 1: y = true
guard 2: if true then y = true else y = x
```

Both ordinary tests require `y = true`. The second guard also has static
dependency `x`. If `x` has failed, that guard is waived and permits `y = false`;
the first guard still rejects it. Removing the dead branch therefore changes
failure behavior. A support-changing optimization needs a theorem for the
lifted semantics, not only Boolean equivalence. This choice makes the required
publication obligations explicit in the expression's static support.

A unary constant-false guard illustrates the boundary. If its subject remains
pending, the guard waits. Publishing any ordinary subject makes the relation
false, so that publication fails. The resulting failed subject then discharges
the guard vacuously. Such a program is executable even though it has no
all-ordinary successful execution.

## Failure is part of the source game

Unsatisfiable guards are admitted. The operational strategy space includes
binding unopenable candidates, withholding where the source operation permits
it, and producing publication failure. Well-formedness checks cover structure,
typing, freshness, ownership, and resource accounting; they do not require a
satisfying ordinary assignment.

An all-ordinary failure-free execution can be useful as a separate optional
property. It may support a liveness claim, an application-specific usefulness
claim, or a theorem specialized to cooperative play. It is not a prerequisite
for defining or executing the game.

The constant-false example consequently has a defined failure settlement,
without an ordinary successful execution.

An empty ordinary payload type has the same treatment: the player can bind an
unopenable candidate and the publication fails. Neither execution nor guard
evaluation needs an invented inhabitant of that type.

Nor does guard failure decide utility. One program may penalize failure, one
may reward it, and another may continue through later operations. The payoff
is whatever the explicit `Result` branches compute.

A player also retains its own decision history. Attempting to open an invalid
candidate and declining to open can produce the same public failure, but the
player remembers which action it took. Keeping only the result store would
erase that distinction and unnecessarily restrict its later strategies.
For example, its next ordinary choice may equal its previous disclosure
decision. A compiler that uses one failure message for both cases must preserve
that private memory or prove an equivalent policy realization. Equality of
public results alone does not prove that claim.

## Immutable private bindings

A failed disclosure changes its publication result, not the original private
binding. Suppose ordinary nullable bindings `x` and `y` must satisfy
`y = none` or `y = x`. Bind both to `some true` and publish `y` first.
Replacing the original `x` by `none` on a later timeout would leave
`(x, y) = (none, some true)`, which violates the binding relation. An incentive
premise about legal source failures cannot turn that pair into a legal one.

Separate private bindings and `Result` publications avoid this mutation.
The owner retains the original value; the failed public result is outside the
ordinary domain; and the lifted public relation handles that failure explicitly.
Already published values remain unchanged.

## Disclosure order is observable semantics

Let Boolean publications `x` and `y` be constrained by `x = y`. Reveal `y`
first. Its value is visible while the guard waits for `x`. If the later `x`
differs, `x` is the publication that fails; `y` is not retracted.

Reverse the disclosure order and the mismatching `y` fails instead. Both runs
satisfy the lifted guard, but their result stores and traces differ. Canonical
source operation order is therefore part of the semantics. A compiler cannot
justify reordering from final Boolean consistency alone.

A parity example makes the same point across types. Let `z : Fin 4` and
`p : Bool` have guard `p = isOdd z`. Revealing `p` first leaves a visible
ordinary Boolean with an outstanding obligation. A mismatching later `z`
fails; no default member of `Fin 4` is fabricated, and `p` remains published.

## Guard ownership

Guards read public data and their author's private resources. An unresolved
private dependency therefore has the same owner as the guarded commitment.
This also controls failure attribution.

For comparison, suppose Bob could guard his `y` by equality with Alice's
unrevealed `x`. If Bob published `false` first and Alice later opened a binding
to `true`, the last-resolver rule would fail Alice's publication. Restricting
unresolved private guard reads to the author prevents this cross-player
attribution. Relations on already public values remain available. This is the
source visibility discipline, not a claim that every possible cross-owner
guard mechanism is unimplementable.

## Public chance has a joint-law contract

The working design retains primitive public chance. A sample is an exogenous
draw from a declared kernel conditional on the complete relevant source
prehistory. It has no strategic player who may replace, retry, or withhold the
draw.

A backend must name the service that realizes this conditional law. The
requirement concerns the joint law, not merely the sample's marginal.

For example, let a hidden bit `x` be fair. Publishing a second bit `c = x`
makes `c` marginally fair, but reveals `x`. It does not implement a fresh fair
coin independent of `x`. A service for the fresh-coin source operation must
realize the required conditional law given `x` and the earlier history, even
if an observer has not yet seen `x`.

An equivalent fixed controller is possible only when its information, timing,
availability, and strategy contract force the same conditional law. Giving an
unrestricted coin publisher constant utility does not stop it from correlating
the draw or selectively withholding it.

## Exact compiler guarantee

Fix a source strategy profile, the canonical ordered operation schedule, and
the concrete bounded service with an adaptive wire environment. The checked compiler theorem has two
exact probability statements.

First, at every compiled source profile, decoding the compiled outcome gives
exactly the source outcome law. This is not limited to equilibrium profiles
or to a selected satisfying witness; packet histories need not coincide.

Second, for every unilateral target deviation, the decoded target outcome law
is a finite mixture of source outcome laws under unilateral source deviations.
The opponents retain their source strategies. The wire environment is fixed
between the reference and deviating target executions; the source execution
does not contain a wire scheduler. Extraction may use information available at
the corresponding source decision, but not on later disclosures.

The target mixture must have the claimed source marginal law. Pairing each
target trace with some supported source trace is insufficient. Independent
resampling is also insufficient when environment signals, chance, and the
deviator's observations are correlated.

Because source strategies themselves include reveal and failure choices, no
extra premise that informed failure is utility-dominated is needed at this
ordered edge. Utility bounds belong where a target really
adds actions, information, timing power, or costs that the source does not
contain, and their required strength should be justified by a counterexample.

## Failed-opening payloads

Public transport may reveal a payload even when application validation records
only `fail`. The relevant compiler obligation is exact about whose information
can leak and whether the prescribed implementation causes it.

If a deviating player sends its own rejected secret `x`, learning `x` is not an
obstruction to backtranslating that same player's deviation: the player was
already free to reveal its own information.

A more useful warning involves a second hidden value. Suppose a bad prescribed
implementation of source strategy `s` opens a doomed candidate by sending raw
payload `x`, and that payload is correlated with another valid hidden value
`z`. An opponent who observes the rejected transaction can guess `z` before
acting. The source failure result alone does not expose `z`, so this bad
implementation need not preserve source deviation laws or equilibria, even if
its all-compiled-profile outcome law is correct.

The remedy is part of compliant compilation: its prescribed failure
realization must not expose rejected data that the source observation omits.
Arbitrary target players remain free to send such data when they deviate.
Unchanged prescribed strategies ignore traffic outside their source
observations. The backtranslation must reproduce the resulting source outcome
law, not introduce a source action for every extra packet.

This example is not a counterexample to the intended compiler. It is a test
that rules out a leaky prescribed implementation. It also disappears as an
incentive counterexample when the failure outcome is absorbing and already
fixes the observer's payoff before any guess about `z` can matter.

## Scope of current checked results

`Interaction.GuardedPublication` currently checks a smaller deferred
publication component: heterogeneous pending/value/failure states,
null-vacuous guard checking, write-once resolution, consistency preservation,
and successful publication from a satisfying ordinary assignment. Its examples
include reverse disclosure and parity. `InteractionTests.GuardFailure` checks
ordinary agreement, support-sensitive resolution, a unary false guard, an
unopenable dependency, and that failure is not a winning comparison.

`Vegas.Source` defines all four source constructors, typed `Result` expressions,
observation-local binding and disclosure policies with own-action recall,
dependent public chance, and exact finite-distribution execution. Its strategy
space is inhabited even for empty ordinary payload types or unsatisfiable guards.
The detailed terminal outcome, payout projection, and externally chosen utility
are separate interfaces.

For every supported complete execution, `Initial.terminal_resolved` proves that
all private publication obligations have resolved, and
`Initial.terminal_guards_hold` proves that every retained guard is decided by
its code: either its subject or an input its code reads failed to publish, or
all of them were published and the code holds on the published values. Both
quantify over arbitrary source policies, including failure choices. They are safety results, not failure-free feasibility or equilibrium
claims. `Paper.lean` delegates directly to these two capstones.

`VegasTests.SourceSemantics` exercises every source constructor in one program:
an initial private Boolean, an optional-Boolean commitment, reverse-order
disclosure, a dependent public coin, and explicit failure-sensitive settlement.
It proves full terminal-state laws, including retained raw bindings, under
successful, rejecting, unopenable, and withholding policies. The fair branch
has probability one half for each Boolean; actual run payout laws distinguish
successful play from each failure case. A separate constant-false guard program
demonstrates defined forced failure.

The full `SourceProgram` compiler has exact outcome, payout, and arbitrary
unilateral-deviation laws to the typed `Vegas.EventGraph`, and same-error Nash
correspondence for source-outcome utilities. The
[source-to-graph certificate](source-graph-edge.md) covers every constructor
without a guard-feasibility or failure-dominance premise. The checked
[public-message edge](event-pending-deviation.md) preserves that complete graph,
yielding source-to-pending exact mixture simulation and same-error Nash
equivalence under its explicit ideal-service contract.
