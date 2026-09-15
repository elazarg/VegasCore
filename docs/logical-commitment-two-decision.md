# Two decisions at a logical commitment boundary

This note describes a checked two-decision information-erasure experiment and
the obligations for applying it to a logical commitment boundary. The first
action is privately recalled. Between the actions, another binding's opening
becomes visible, either pending in an inbox or already included in the ledger.
The question is whether a richer-information response can be replaced by a
logical response while keeping the surrounding transition rules fixed.

The answer is yes under a controlled factorization condition at both stages.
It does not follow by applying a one-decision hiding argument twice. In
particular, a factorization which happens to hold under one baseline policy can
fail after changing the first action law.

## The finite experiment

Use the following types and kernels.

```text
mu       : FinDist Native1
observe1 : Native1 -> Logical1
first    : Native1 -> FinDist Action1
step     : Native1 -> Action1 -> FinDist Native2
observe2 : Native2 -> Logical2
second   : (Native1, Action1, Native2) -> FinDist Action2
finish   : (Native1, Action1, Native2) -> Action2 -> FinDist Result
```

The information retained at the second decision is the whole logical history

```text
recall(n, a, n') = (observe1(n), a, observe2(n')).
```

Thus `Action1` is private action recall, not a public field accidentally added
to `State.View`. For the logical commitment instance, `Action1` prepares a
chosen value or records an equivalent private commitment command. The
intermediate step exposes an opening claim `d` to the owner's inbox.
The concrete `observe2(n')` is a summary of the disclosed value and inclusion
status. Its corresponding logical view distinguishes a pending inbox claim
from one also recorded in the ledger with an acceptance receipt. The inclusion
status is retained, not treated as erased metadata.

The second policy may depend arbitrarily on the full native history. Its
logical replacement is allowed to depend on the recalled first action and the
visible pending claim. A representative second choice is whether to publish a
compatible opening or withhold and accept attributed settlement.

This experiment exercises two distinctions already represented by
`LogicalCommitment`:

- `State.observe` exposes a recipient's inbox separately from the public
  ledger and receipts, so visibility does not imply inclusion.
- candidate meanings are absent from `State.View`, so an owner's preparation
  value must be carried by command history or equivalent private memory.

## A sufficient two-stage factorization

Fix logical kernels

```text
logicalStep   : Logical1 -> Action1 -> FinDist Logical2
logicalFinish : (Logical1, Action1, Logical2) -> Action2 -> FinDist Result.
```

It is sufficient that, for every relevant native input and every action,

```text
(step n a).map observe2 = logicalStep (observe1 n) a

finish (n, a, n') b =
  logicalFinish (observe1 n, a, observe2 n') b.
```

The first equality must cover actions considered as deviations, rather than
only actions selected by one baseline policy. The second must hold on every
resulting supported history and for every second action. Environment and
opponent behavior between decisions is part of `step` and `finish`; the
logical kernels are fixed once and do not change with the owner's policy.

Under these hypotheses, condition the policies in chronological order. Let

```text
logicalFirst = conditionedPolicy mu observe1 first.
```

The joint observation/action law and the first factorization give the same
law of `(Logical1, Action1, Logical2)` on both sides. Let `nativeHistoryLaw` be
the native law after `first` and `step`, and set

```text
logicalSecond =
  conditionedPolicy nativeHistoryLaw recall second.
```

The second decision theorem and `logicalFinish` then give exactly the same
result law. The pair `(logicalFirst, logicalSecond)` is one behavioral policy
constructed from the fixed native policy; it does not select a continuation
after learning an erased state. Off-support logical histories may use the
total fallback supplied by `condOnFibre`.

`FinDist.exists_two_decision_policy_law` in
`GameTheoryExtensions/Math/Probability/SequentialDecisionObservation.lean`
proves this construction using the one-decision results. Its hypotheses are
action-total: the second factorization covers every first action at a supported
initial input, every supported successor under that action, and every second
action. The equality of intermediate retained-history laws is proved, not
assumed.

For a strategic backtranslation, the same logical environment kernels must
work for every focal alternative. A factorization asserted only on the support
of one fixed focal policy proves an outcome-law identity for that policy, but
does not keep the environment unchanged across deviations.

## Counterexample to policy-relative composition

Let a hidden bit `h` be uniform and let `observe1` erase it. After the first
action, expose the same opening claim `d` in both cases and leave it pending, so
`observe2` is also identical apart from the retained first action. Let the
fixed native environment include `d` at settlement exactly when the second
action `b` equals `h`; otherwise it withholds the claim and settles quit.

Under the baseline first policy `a = h`, recall carries enough information to
describe settlement as “include exactly when `b = a`.” A stagewise calculation
restricted to that baseline support can therefore appear to factor through
`(a, inbox = [d])`.

Now replace the first policy by the constant action `a = false`. Histories with
the same retained data `(a = false, inbox = [d])` occur at both hidden bits,
but the same second action has different settlement results. No single
`logicalFinish` on the retained history can equal the native environment in
both states. The apparent baseline factorization used a policy-specific
correlation between recall and hidden state; it was not an environment
factorization.

This counterexample is a mathematical argument here, not a checked Lean
theorem or a claim that the current pending-message runtime has this behavior.
It models the hazard posed by an
erased packet identifier, availability bit, phase, or copy count on which later
inclusion depends. If the owner also observes that metadata natively, erasing
it can produce the familiar strict value gap. Even when the owner does not
observe it, exact state-by-state kernel factorization still fails.

## What the existing commitment laws establish

`LogicalCommitmentAdmission` compares native candidate validation with the
graph-gated logical validator at inclusion time. `LogicalCommitmentEffects`
then identifies the selected handle, candidate meanings, and opening result of
that admitted step. These laws cover the semantic effect of an inclusion that
actually occurs.

They do not determine whether or when an exposed claim is included. They also
do not factor transport, receipts, clocks, timeout settlement, player
observations, or fixed opponent policies. Therefore they cannot supply either
`logicalStep` or `logicalFinish` for the experiment without an additional
runtime-relative proof.

`Action.RealizableAt` is likewise only unary provenance. It does not retain
pending-copy counts or reconstruct the transport schedule, so realizability of
each logical action is weaker than the controlled factorization above.

## Boundary between generic and compiled results

The two-stage conditioning argument is game-theory generic. It mentions only
finite laws, observations, actions, and controlled kernels. A reusable theorem
at that layer should retain the first action explicitly in the second
observation and should quantify the factorization over all relevant actions.

The checked instance in `InteractionTests/LogicalCommitmentSequential.lean`
uses two logical bindings with distinct owners. The first owner chooses a
Boolean candidate, then receives a disclosure from the second binding. An
arbitrary second response either claims an opening value or withholds; an
incompatible claim is rejected before attributed fallback. The instance uses
the actual `LogicalCommitment` transitions. The response remembers the chosen
value, not the private candidate catalog.

`two_decision_commitment_law` preserves the joint law of the two binding results
while erasing auxiliary metadata. The native response may remember and reuse
that metadata at both decisions. `pending_opening_view` and
`included_opening_view` check the distinct inbox, ledger, receipt, and result
projections used by the experiment. `disclosure_recoverable_from_view` supplies
one total decoder recovering the summary from those actual observer views.
This supplies no additional access to private state.

The checked negative test fixes a fair first choice and forgets it before the
opening response. Every independent randomized claim or withholding has
opening utility at most one half; recalling the choice attains one.
`forgetting_choice_strict_value_gap` establishes the strict comparison. This
is a failure of action recall, not of commitment hiding.

These are finite policy laws, not a new full game interpreter or a strategic
certificate for the candidate runtime. The second binding can remain pending
at the experiment's endpoint. Queue availability, service, deadline resolution,
and the choice of disclosure law are not implemented or justified by it.
The two bindings have different owners and do not exercise shared-candidate
interactions. No strict utility-gap result is asserted for erasing inclusion
status; the checked strict gap concerns private action recall.

A compiled multi-site application has additional obligations. Candidate
handles and owner memory are shared across sites; prerequisites determine the
admission gate; clocks can trigger settlement; and another site's pending
traffic can influence the fixed environment or an opponent. Sequential
composition is sound only if those joint effects are retained in the logical
history or their continuation law is proved independent of the erased data.
Composing separate per-site hiding results is not sufficient.

## Native fixed-segment instance

`InteractionTests/LogicalCommitmentNative.lean` proves the two-stage law for
actual candidate `MessageApplication` execution. One owner prepares a Boolean
candidate and its commitment is accepted. A fixed distribution chooses an
unauthenticated opening claim and whether it remains pending or is included
and rejected. The claim is delivered to the owner's inbox in both cases.
The owner's second response submits a claimed opening or withholds. The
continuation includes any submitted response and advances the actual deadline
clock. Matching claims open; mismatches and withholding publish the null
default with a timeout record.

`candidate_two_decision_policy_law` quantifies over both randomized responses.
The second response receives the actual native owner view plus the recalled
first action and auxiliary initial metadata, never the private catalog.
The proof derives the two action-total kernel equalities from these native
segments. It retains the pending claim separately from ledger inclusion, and
preserves the final published-value/timeout law. The disclosure distribution
and transport segments are fixed independently of both response policies.

This is a single-binding decision experiment. Its logical side is a small
observation/result kernel, not an execution of `LogicalCommitment.State` or a
new game interpreter. The other sender follows fixed background traffic;
there is no quantified opponent policy or native `EnvironmentPolicy` theorem.
The result does not erase arbitrary packet identifiers, deadline phases,
receipts or transport behavior, nor preserve the final raw observation.
The varying unauthenticated claim is not another honest binding's secret
opening. The experiment therefore tests the native factorization mechanism
without establishing the cross-site information theorem.

## Native policy-runner instance

`InteractionTests/LogicalCommitmentPolicyExecution.lean` realizes the same
single-binding experiment with the actual `MessageApplication.runPolicies`
runner. A fixed nine-invocation schedule calls the owner to prepare, submit a
commitment, and later open or withhold. The opening decision recovers the
prepared value from the owner's private-command history and receives the
actual owner view. The fixed background opponent submits one unauthenticated
claim. The environment includes the commitment, delivers the background
claim, optionally includes it, attempts inclusion of the owner's response,
and advances the clock. Its policy is unchanged when either owner kernel
changes, including when the owner withholds.

`runPolicies_two_decision_outcome` derives the resulting terminal law directly
from the runner. `runPolicies_logical_policy_law` then delegates to the checked
conditioning construction: for every pair of randomized owner kernels, there
are logical kernels with the same published-value/timeout law. They retain the
prepared value and pending-versus-included observation, but receive neither
the full native view nor the auxiliary metadata used to mix owner policies.
The background opponent, environment, schedule and logical transition kernels
are fixed independently of both owner kernels. The fixed disclosure itself
is a theorem parameter, not a fresh random draw shared secretly by the
opponent and environment.

This is a restricted-strategy law. The owner must follow the specified
preparation and submission interface at its non-decision steps; the theorem
does not quantify over arbitrary native `PlayerPolicy` values. Nor does it
cover arbitrary adaptive service, shared candidates across sites, or a
compiled opponent's private disclosure. Its logical side is the same finite
observation/result kernel, not a newly implemented game interpreter. The
result validates policy execution and information erasure for this bounded
interface; it does not yet replace a compiler proof.

## Compiler adoption test

The next discriminating test is a two-site native execution: the focal owner
prepares a candidate, another compiled binding exposes an opening, and the
focal owner opens or withholds. Fix the opponent policy, environment and
schedule before quantifying over the focal decision kernels. Use an actual
authenticated opening from the other binding, rather than the unauthenticated
background claim used by the single-site experiment.

Retain the joint logical observations of both sites, private action recall,
and pending-versus-included status. The output to preserve is the relevant
public pre-decision prefix together with the focal settlement value and
attribution. Derive the action-total kernel factorization from the native
execution. A failure after erasing another site's observed traffic identifies
an insufficient observation quotient; it does not establish strategic
impossibility for the runtime.

This prefix is needed by `candidateGraphRoundCoupling_timeout_settlement`,
which connects native timeout settlement to a legal graph realization at the
comparison point used by the source quitting condition. Preserving only a
terminal published-value/timeout law cannot replace that interface.

Adoption requires generalizing the successful fixture to a graph-wide
stopped-prefix law under one fixed admitted environment and unchanged
opponents, consuming the existing candidate admission/effect lemmas. It must
replace a named portion of `candidateGraphRun_native_prefix_law` without
reintroducing the whole native history as an unconstrained logical signal.
Until that simplification is demonstrated, the experiment remains independent
of the active compiler. Further local safety lemmas alone would not settle
the adoption decision.
