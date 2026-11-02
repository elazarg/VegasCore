# Uniform semantic compilation of equilibrium clients

The [semantic compiler](../Vegas/Game/ClientCompiler.lean) accepts a
source setup, a certified runtime specification, and a supplied intended
equilibrium. It returns an assessment of the **bounded raw response-menu game**
and physical clients realizing that assessment. The SE certificate quantifies
over behavioral deviations within that finite menu. Arbitrary physical
`app.Policy` deviations that leave the menu are outside this result.

The compiler composes source-to-graph compilation, native equilibrium completion, raw-menu audit extension and physical response
decoding. The [ledger realization](../Interaction/ReactiveLedgerAssessment.lean)
supplies the information and continuation bridge for ledger-reading clients.

## Input and output

`Vegas.ClientSpec` packages the source and runtime premises:

* source well-formedness and private-input independence conditional on a signal
  determined by public initial inputs;
* finitely many players and intended-source histories;
* finite support for the physical initial law, scheduler decisions, application
  environment steps and pending-observation kernels;
* a finite response catalogue and candidate capacity;
* all-history opportunity, protected inclusion, completion and deadline margins;
* utility bounds, the exclusion floor and funded evidence coverage.

`FiniteNature` is the finite-support premise on nature kernels. Finite menus
and the fixed horizon then imply finitely many legal histories of the bounded
game. This does not assert finiteness of the unrestricted physical history
space.

The catalogue coverage premises are stronger than coverage of the equilibrium
strategy's support. `outputValues : bounds.CoversOutputValues` requires **every
value** of each binding or publication payload type to belong to a `Finset`.
Those value types must therefore be finite. The initial-input premise
`Vegas.EventGraphRuntime.MessageBounds.CoversInputValues` similarly covers
every value of each initial binding input type. A finitely supported strategy
over an unbounded integer bid type does not satisfy these premises. Terminal
payment values are distinct from binding and publication payload types. A
finite guard on an integer bid does not make its value carrier finite either.

The runtime operates on the source's compiled sequential graph. Its
specification is fixed before selecting the source equilibrium.
`Setup.IntendedSequentialEquilibrium` names the intended-game hypothesis in
[the source preservation layer](../Vegas/Game/IntendedPreservation.lean).

`Vegas.ClientSpec.compile` returns a `ClientCompilation` with:

* a bounded raw-menu assessment with consistent beliefs;
* whole-continuation sequential rationality against that menu's behavioral
  policies, including off-path decisions;
* no public defaults or audit charges on its supported paths;
* the exact joint full source-configuration/default-history and settled-payoff law.

The artifact exposes physical `clients` and projected
`ClientCompilation.ledgerClients` over the Interaction callback API. The latter
satisfy the exact `IgnoresLeakedFields` projection described below. Each callback law
is supported within a finite response menu. Physical policy realization does not enlarge the
assessment's deviation domain: its menu is
`Vegas.EventGraphRuntime.MessageBounds.rawMenu`, built from the configured bounded
submissions and known packets. Backtranslation of arbitrary out-of-menu
Interaction deviations is a separate target.

## Compiler correctness

`Vegas.ClientSpec.compile_correct` is the ordinary-client capstone.
`Vegas.ClientSpec.compile_ledger_correct` additionally combines the
ledger information restriction, bounded-menu SE, strategy agreement at every
legal bounded-menu decision and the initialized outcome law under no pending
delivery.

`ClientCompilation.clients_strategy` proves that restricting decoded
physical clients recovers the selected behavioral strategy exactly.
`ClientCompilation.clients_stateLaw` identifies the physical execution
state law with the assessment's state law. Its `ClientCompilation.clients_outcomeLaw` composes
that identity with source preservation, retaining the full source configuration and default history jointly with the settled payoff vector.

`ClientCompilation.clients_sequentiallyRational` states the incentive
guarantee directly for physical policies: at every information set, the
assessment's belief average of the actual physical continuation payoff cannot
increase under any `app.Policy` satisfying the menu's `Admissible` predicate.
Admissibility requires menu coverage at every legal decision history, including
off-path histories; it imposes no condition on inconsistent callback inputs.
This is the physical form of the same bounded-menu guarantee, with no extra
service, observation or prior premise.

`ClientCompilation.clients_noDefaults` and
`ClientCompilation.clients_noCharges` transfer clean-path guarantees
to supported ordinary physical runs. They require no empty-observation
premise: arbitrary finitely branching pending-observation kernels satisfying the specification
remain allowed.

For valuation plus the setup's executable receipts, the
[monetary capstone](../Vegas/Game/PaymentPreservation.lean) applies to **every
supplied `ClientCompilation`**. Its cash law uses the same assessment and the
same audit, not a separately selected completion. The companion
`ClientCompilation.clients_programPayments_preserved` identifies actual physical
client receipts jointly with the fixed initial-state, terminal-state and public
readers. In particular, it applies to the exact clients returned by
`spec.compile intended equilibrium`. Once the artifact is supplied, the cash
proof needs no additional source-equilibrium premise.

For interfaces delivering no pending observations:

* `ClientCompilation.ledgerClients_agree` proves callback-law identity
  at every initialized legal raw history, including arbitrary earlier
  responses. This identity does not extend the SE deviation domain.
* `ClientCompilation.ledgerClients_strategy_at_history` identifies the
  represented strategy at every legal bounded-menu decision, including
  zero-probability decision histories.
* `ClientCompilation.ledgerClients_continuation` identifies complete
  physical continuation laws from legal bounded-menu histories.
* `ClientCompilation.ledgerClients_sequentiallyRational` compares the
  actual ledger clients against every admissible physical continuation policy,
  using the same beliefs at on-path and off-path information sets.
* `ClientCompilation.ledgerClients_finish_eq_clients` identifies the
  initialized ledger and ordinary physical runs. The ledger outcome and
  clean-path lemmas follow from the ordinary-client results.

The generic continuation theorem applies to every bounded-menu behavioral
profile, including unilateral alternatives. It uses the protocol runner,
finite-menu restriction, policy decoder and recorded-response origin theorem.
The compiler instantiates it with a common consistent equilibrium completion;
no game-specific client policy is an input.

## Observable laws and coverage

[Observable closure](../Vegas/Game/ClientObservables.lean) exports
`ClientCompilation.clients_postprocessLaw` and its ledger counterpart.
Any common stochastic observation of the certified full-configuration/payoff pair
has exactly the intended law. Deterministic readers are the pure-kernel case;
the observation kernel itself needs no finite-support premise.

`Vegas.ClientSpec.intended_outcomeLaws_subset` states the coverage
conclusion as set inclusion: every intended SE joint law belongs to the clean
bounded-runtime SE laws. Additional runtime equilibria and their outcome laws
are not characterized by this inclusion.

[Funding monotonicity](../Vegas/Game/ClientFunding.lean) is packaged as
`Vegas.ClientSpec.withDeposit`: every pointwise larger deposit produces
another certified specification for the same source, runtime and evidence
service. It normalizes the declared observation-rate lower bound to be
nonnegative, without adding a hypothesis or changing the actual observations.
Recompilation preserves the intended law; its off-path completion can change.

[Utility linearity](../GameTheoryExtensions/Analysis/Protocol/UtilityLinearity.lean)
applies to one fixed assessment and continuation runner: nonnegative playerwise
linear combinations of utilities preserve sequential rationality when that
assessment is rational for each component. The equilibrium theorem retains its
consistency witness. Finite bounded-menu histories supply integrability. This
does not mix different equilibria or assert that compiling different utilities
selects a common completion.

## Ledger observation scope

`Interaction.MessageNetwork.ObservationRule.DeliversNothing` states that every
player and pending pool receives the empty selected-identifier set with
probability one. The same predicate applies directly to `leaks` and to
`app.observePending`.

`IgnoresLeakedFields` states invariance under clearing the leaked-message field from the
current view and each recorded pre-response view. It retains application views,
receipts, own actions and emitted envelopes. Thus its invariance compares
inputs with those retained fields fixed; it is not independence from every
effect of a private pending delivery.

For example, a fixed forwarding request can name a guessed message identifier.
If that pending message was privately delivered, packet materialization can
attach its authentic certificate. The sender's own emitted envelope then
retains that certificate even after the leaked fields are erased. A later
projected callback can read it from own-output recall. This behavior is checked
in [the pending-observation regression](../VegasTests/PendingObservationPrivacy.lean).

Under `DeliversNothing`, the leaked fields of every actual current and recalled
view are empty. The projection is then the identity at every initialized legal
history, which yields the stated ledger-client physical realization and
continuation laws. The periodic service satisfies this premise. A realization
claim for informative pending delivery requires a separate argument about the
information retained in actions, emitted packets and application observations.

## Semantic construction and executable synthesis

The compiler is a Lean semantic function using classical selection from the
common-limit preservation theorem. It supplies a complete mathematical
strategy. Computing numerical strategy coefficients and generating client code
require effective finite input representations and a constructive certified
completion backend.

[The compiler regression](../VegasTests/ClientCompiler.lean) supplies
Odds–Evens service, audit and source certificates to the generic compiler for
every supplied intended equilibrium. It also checks ordinary-client clean
runs and the fair assessment's exact joint outcome law. The
[scenario fixtures](sequential-client-scenarios.md) are operational diagnostics;
their manually prescribed candidate is distinct from the certified strategy.
