# Completing sequential-equilibrium preservation

The [checklist](se-proof-checklist.md) is the validation ledger. The
[stack](se-compilation-stack.md) states the games, utilities and backend
assumptions. The [asynchronous plan](se-schedule-generalization.md) records the
remaining general proof obligations. This plan orders the work needed to
integrate the explicit decision-packet semantics and finish preservation.

## Target and scope

Fix the program, initial law, service, observation rule, bounded response
interface, utilities and deposits before choosing a source equilibrium. Every
source sequential equilibrium must have a bounded raw-runtime sequential
equilibrium preserving the joint initial-parameter, public-result and realized
settlement law. Utilities depend on initial parameters and public results.

The fixed-calendar composition is
[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean).
Its source-to-permitted edge is
[SourceServiceEquilibrium](../Vegas/Game/SourceServiceEquilibrium.lean); its
permitted-to-raw edge is
[SourceServiceRawExtension](../Vegas/Game/SourceServiceRawExtension.lean).
The explicit decision-packet composition passes the warning-strict project
build, including the complete calendar capstone and its standard-axiom pins.
Dependency evidence and repository validation are tracked by the checklist.
The arbitrary-builder theorem remains open.

## Calendar comparison chain

Every selected resolution sends a packet: evidence-free FALSE withholding or
an authentic effective TRUE opening. Silence is waiting. The calendar requires
an actual decision at the final owner visit for bindings and resolutions alike.
Every actor therefore needs an opportunity in its roster.

[SourceServiceSiteKind](../Vegas/Game/SourceServiceSiteKind.lean) classifies a
native information site from its event, owner, recall and recorded bit:

| Site | Comparison |
| --- | --- |
| Public sample | `sample_comparison_eq` |
| Foreign binding | `foreign_binding_comparison_eq` |
| Foreign disclosure | `foreign_disclosure_comparison_eq` |
| Recorded own binding | `recorded_comparison_eq` |
| Unsent own binding | `unsent_binding_comparisons` |
| Recorded own disclosure | `recorded_disclosure_comparison_eq` |
| Unsent own disclosure | `unsent_resolution_comparisons` |

The first four equality cases and recorded disclosure preserve the complete
continuation law under every legal local alternative. Unsent bindings and
resolutions simulate the alternative exactly through one common mixture of
original source assessment comparisons. Missing opening material restricts
which TRUE decisions are effective; FALSE remains an explicit decision.

[SourceServiceOwnerComparison](../Vegas/Game/SourceServiceOwnerComparison.lean)
transports those continuation identities to the original source assessment.
The source sequence is fully supported and Bayesian. Its disclosure
normalization is an execution device; no equilibrium of the normalized source
game is assumed. [SourceServicePrefixFactorization](../Vegas/Game/SourceServicePrefixFactorization.lean)
and [SourceServiceBayes](../Vegas/Game/SourceServiceBayes.lean) retain the actual
native input, including observations and own recall.

The source-to-permitted assembly uses the local simulation limit theorem with
exact comparisons and zero simulation error. Original source regret is handled
by that theorem's source-sequence argument. Initialized law preservation comes
from [SourceServiceTimedLaw](../Vegas/Game/SourceServiceTimedLaw.lean).
The complete calendar source-to-permitted statement and its comparison callers
pass strict checking for this model. S2–S5 and the raw-runtime repair edge are
checked; the complete calendar capstone passes the project build.

## Calendar continuation repair

Repair must supply one implementable continuation policy shared across all
hidden histories of the deviator's information site. The actual evaluator
coupling must preserve initial parameters and public outcomes or supply enough
additional collection to dominate the base-payoff gain.

The final required visit needs an actual silence branch: silence followed by
deadline expiry leaves a public decision-miss marker. Derive that marker from
the real expiry transition. An arbitrary state's lack of an accepted packet
does not imply a public miss. Optional-window coupling applies only where
silence remains in the retained menu.

The reactive service's application-side intention cache is empty along actual
initialized traces. Internal repair helpers needing this fact receive it from
their evaluator history. The nonreactive client runtime also uses explicit
private remember commands; its intentions must be reconstructed from actual
owner recall before that table can be removed. Do not add an oracle or a cache
hypothesis to the public capstone.
The send-time proof devices can be removed after the decision semantics and
callers are verified.

The concrete block kernels, program and active continuations, evaluator
coupling, settlement dominance, restriction extension and raw-alias lift all
pass strict checking for this model. R1–R4 and E1 are checked through their
complete statements, rather than conditional helpers.

## Arbitrary-builder proof

The generic service is [AsyncServiceSpec](../Vegas/Game/AsyncServiceSpec.lean).
The contract gives a timely owner opportunity, protected inclusion and complete
play; readiness starts the timer. The general retained menu keeps deferrals.
Late unrecorded opportunities and persistent owner risk open the bounded raw
continuation menu.

The actual binding-response law now composes with protected completion,
retaining the transmitting draw and full stopped traffic. The native Bayes
law cancels the complete focal owner's recalled-action likelihood, including
earlier waiting. Foreign deferral probabilities remain in counterfactual
reach. A conditional escape estimate must compare against that actual
denominator; a small unconditional escape probability alone is insufficient.
Public misses are excluded from every history at source-compatible native
information by the shared public record. Hidden private risk remains distinct.
For waiting comparisons, a late canonical packet can still be accepted before
expiry without a charge, so the accepted branch needs source-continuation
control as well as the miss branch's real collection bound.
Protected binding completion also identifies the actual whole-program source
prefix and behavioral step through its derived residual. Original disclosure
memory, joint native-input likelihoods and source assessment transport remain
separate obligations.
Supported original resolution intentions now have exact protected packet
completion and typed-state agreement, with effective history kept distinct.
A single timely canonical transmission followed by owner silence also has an
actual accepted-action/public-miss dichotomy outside the protected window.
Its acceptance law can depend on the builder and the public packet content;
the dichotomy alone does not bound the value of waiting.

Continue in this order:

1. Join actual decision, inclusion, sampling and stopped traffic kernels into
   source-prefix/input likelihood laws, including earlier retained deferrals.
2. Derive source-relative conditional beliefs and escape bounds at native
   information sites. Clean-prefix probability equality alone is insufficient.
3. Compare protected decisions, waiting, late first attempts and departures
   under the actual audited utility.
4. Supply consistent rational continuation at free sites, including after
   collection of the one-time deposit has become certain.
5. Complete the source-to-risk-menu equilibrium embedding, general continuation
   repair, effective-menu extension and raw-alias lift.
6. Compose the arbitrary-builder capstone and derive the calendar corollary.

The watcher samples authentic evidence partially; observation and report
delivery may be correlated. Positive conditional coverage and a finite
challenge window are backend obligations. A concrete pending-message reporting
implementation must establish them. Public misses and packet collection are
separate mechanisms.

## Validation

Run one artifact-writing Lake build at a time. Targeted builds isolate proof
failures; the coherent checkpoint must pass `lake --wfail build`, the evidence
checker, module and documentation checks, central Lean-option checks and
repository tooling tests. The paper must pin the final capstone's standard
axioms. Commit and push each verified checkpoint, preserving unfinished work
outside its staged snapshot. No proof admission or compiler-fact hypothesis
may replace a missing implementation argument.
