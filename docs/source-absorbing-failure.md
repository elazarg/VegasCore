# Absorbing failure as the source language semantics

This design changes the source games. It does not assert a stronger theorem
about the continuing-failure games. The aim is one source executor, one graph
executor and one ledger application, with absorbing default enforced at every
level. The intended game remains a restriction of the source menus, rather
than another execution semantics.

No semantic replacement is implemented here. The checked
[separation fixture](../VegasTests/AbsorbingFailure.lean) proves that the source
evaluator admits an opening after the same owner's earlier withheld opening,
and that permanent withholding changes its observable law. It also checks the
different exclusion effects of accepted bindings and completed expiries. No
source-to-ledger preservation claim for the proposed semantics is proved.

## The semantic distinction to preserve

The source program can own two unresolved commitments. A policy can withhold
the first opening and disclose the second successfully. Its public result is
`(failure, success true)`. Permanent withholding gives `(failure, failure)`.
`VegasTests.source_permanent_withholding_changes_law` proves these laws differ.
Consequently, replacing failure behavior changes the full typed terminal law;
it is not merely a different representation of the same execution.

The runtime distinguishes two events that can write the same hidden failed
binding value:

* An accepted opaque binding may be unopenable. Its owner is not excluded at
  binding inclusion. The defect stays hidden until a failed public opening.
* An owned binding can expire without an accepted handle. That omission is
  public and immediately excludes its owner.

`VegasTests.accepted_binding_does_not_exclude` and
`VegasTests.completed_expiry_excludes_owner` check the trigger rules directly.
The runtime definition is
[ExclusionApplication](../Vegas/Pending/ExclusionApplication.lean); the public
receipt-based distinction is defined in
[PublicFailureEvidence](../Vegas/Pending/PublicFailureEvidence.lean).

Interpreting every hidden binding value `failure` as public default is
incorrect. The source predicate `ProtocolState.Excluded` includes hidden
failed bindings and therefore cannot be used unchanged as the control flag.

## Proposed single tower

The intended game restricts the source game's successful moves. Compilation
then follows the ordinary source -> dependency graph -> ledger tower.
Absorbing default is part of each level's operational semantics. There is no
failure-mode parameter, alternative source protocol or second graph evaluator.

At source, refactor evaluation around the typed `SourceProgram.Config` already
used by the execution protocol. Add a public `defaulted : Finset Player` field.
Use one recursive evaluator over this configuration, instead of maintaining
both separately threaded execution state and configuration execution.

Commitment decisions must distinguish accepted binding from omission. One
small sum type suffices: `bind result`, where `result` may itself be unopenable,
or `default`. A binding cell retains the result; the control flag records public
default. This preserves the difference between an opaque bad binding and a
missed commitment without introducing a new hypothesis.

An owned instruction whose owner is already defaulted automatically writes its
failure result. It does not request another strategic decision. Otherwise:

* a binding stores the submitted result without exposing a hidden defect;
* a defaulted binding writes failure and marks its owner defaulted;
* an attempted reveal runs the source guard checks once;
* a withheld or rejected reveal writes failure and marks its owner defaulted;
* public samples keep their declared law and the program continues;
* terminal observations retain the typed store and the public default set.

The public default set belongs in every player's observation. A later reveal
cannot repair default. Existing declarations that derive observations or actors
from a configuration must read this same control state; they must not reconstruct
another failure mode from private binding values.

At graph level, retain the ordinary event kernel and extend its binding
decision with the same accepted/default distinction. Carry the public default
set in its execution configuration. Defaulted owners' ready nodes complete with
the ordinary failure action, without calling their policies. This is automatic
control over the graph execution, not a new graph language or interpreter.
The current
`Vegas.EventGraphRuntime.State.completeFailure_step` already supplies the
local fact that automatic failure is a genuine graph step. Its extension must
also transport the new public default state.

At ledger level, consolidate the permanent-exclusion controller into the one
compiled application. Accepted commitment handles implement `bind`, owned
expiry implements `default`, and failed accepted openings implement failed
resolution. Automatic draining must use the graph's failure step. The
`RecoveryState` wrapper and default application split can then be removed once
their fields and proofs have been absorbed into the authoritative state.
Raw packets after exclusion remain possible network actions; the application
rejects their semantic effect and the count audit handles forbidden traffic.

## Utility and transfers

Default fixes the owner's base utility at the declared exit value. This is a
definition of the changed game, not an assumption that arbitrary valuations
already satisfy it. Merely setting executable transfers to zero does not fix
utility when external valuation still depends on the remaining outcome.

Preserve the distinction between exit valuation and exit transfer. The monetary
readout must return the declared exit transfer for a defaulted owner, and its
strategic utility must use the declared fixed total exit utility. The count
audit can still deduct for forbidden packets after default. The audit-free
source payoff and the audited ledger payoff therefore remain connected by an
explicit settlement projection.

No independence, service, coverage, finiteness or funding premise is added by
this design. The current preservation theorem's premises, including its exit
floor bound, remain obligations when that theorem is ported. No additional
restriction on valuations or initial laws should be introduced to make the port
easier.

## Compilation and proof obligations

The following are mathematical obligations, not completed results:

1. Prove the configuration evaluator agrees with its protocol presentation,
   including automatic steps at defaulted owners' instructions and the exact
   observation of public default status.
2. Compile source default decisions and implicit failures to the graph's one
   step relation. Prove typed-store and default-set correspondence for arbitrary
   source profiles, including voluntary default and hidden bad bindings.
3. Prove ledger inclusion, expiry and automatic draining refine those graph
   steps, with receipt provenance distinguishing hidden binding from omission.
   An Interaction transition can drain several nodes, so its graph refinement
   is a finite sequence of ordinary steps rather than exactly one step.
4. Reprove the actual bounded-client source law with the new full readout and
   unchanged service contract. Updating a theorem's source model in place does
   not prove it.
5. Recheck Nash deviation translation and sequential consistency/rationality
   separately. Exact equilibrium-path laws alone do not establish either.
6. Port the intended-SE theorem only after its source and target interpretations
   match. Its current conclusion does not cover every source-game equilibrium.

The sequential dependency mode has a direct written-order interpretation.
Public-barrier concurrency needs an additional information-order argument.
If Alice's binding precedes Bob's in source order, Bob's source policy can
condition on Alice's public default. A graph scheduler that runs Bob's private
binding first cannot supply that observation. Thus public default can affect
the arbitrary-profile terminal law itself, as well as the information available
to graph deviations. Keeping only the private binding commutation proof does
not retain the ordinary concurrent law or Nash statement.

The compiler must add the information dependencies introduced by possible
default. Ordering every potentially defaulting binding is a direct solution;
retaining more concurrency requires a separate information-preservation proof.
Restricting the ordinary statements to sequential graphs would be an explicit
loss of scope, not a strengthening.

The branch is suitable for a semantic replacement experiment. It is not ready
to replace the maintained tower: the replacement evaluator, graph and ledger
unification, ordinary law and equilibrium ports remain unimplemented. No paper
statement or axiom pin is changed.
