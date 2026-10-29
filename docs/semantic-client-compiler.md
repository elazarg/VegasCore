# Uniform semantic compilation of equilibrium clients

The [semantic compiler](../Vegas/Game/RecoveryClientCompiler.lean) accepts a
source setup, a fixed certified runtime specification, and any supplied
intended equilibrium. It returns a compiled artifact containing the selected
runtime assessment and its preservation certificate. Its physical clients are
defined uniformly from that artifact. No game-specific client policy is an
input to compilation.

The compiler reuses source-to-graph compilation, the permanent-exclusion
equilibrium completion, raw audit extension and physical response decoding.
The [ledger realization](../Interaction/ReactiveLedgerAssessment.lean) supplies
the information and continuation bridge for ledger-reading clients.

## Input and output

`Vegas.RecoveryCompiler.Specification` packages the hypotheses of the existing
preservation capstone: source well-formedness, private-input independence given
an existing public signal, finite source and physical histories, supported wire
values and candidate capacity, all-history opportunity/inclusion/completion,
deadline margins, utility bounds, the exclusion floor and funded evidence
coverage. Its runtime operates on the original source's compiled sequential
graph. The specification is fixed before selecting the source equilibrium.

`Vegas.RecoveryCompiler.compile` takes that specification, the intended
assessment and its equilibrium proof. It returns a `Compilation` with:

* a complete raw-runtime assessment, including consistent beliefs;
* a certificate of whole-continuation sequential rationality;
* no exclusions or audit charges on its supported paths;
* the exact joint typed-source-readout and settled-payoff law.

The artifact exposes ordinary physical `clients` and pending-independent
`ledgerClients`. These are policies over the actual Interaction callback API,
with access to contract state, private values, own response recall and receipts.
The ledger variant erases pending observations throughout recall.
Each callback law has finite support in the bounded physical response menu.

## Compiler correctness

`Vegas.RecoveryCompiler.compile_correct` is the ordinary physical-client
capstone. `Vegas.RecoveryCompiler.compile_ledger_correct` combines the ledger
information restriction, sequential equilibrium, agreement at every legal
decision and the initialized source outcome law under no pending delivery.

The strategy decoder is the existing finite-menu decoder, rather than a new
interpreter. `Compilation.clients_strategy` proves that restricting the decoded
physical client recovers the selected behavioral strategy exactly. The compiled
assessment is therefore the assessment implemented by these clients.

`Compilation.clients_stateLaw` identifies the complete physical execution-state
law with the assessment's state law. `Compilation.clients_outcomeLaw` composes
this identity with the source preservation certificate. It retains the full
typed terminal readout jointly with the settled payoff vector.

For interfaces delivering no pending observations, ledger correctness is
stronger than agreement on honest supported paths:

* `Compilation.ledgerClients_agree` proves physical response-law agreement at
  every initialized legal raw history, including arbitrary earlier responses.
* `Compilation.ledgerClients_strategy_at_history` identifies the represented
  client strategy with the selected assessment, including at zero-probability
  decision histories.
* `Compilation.ledgerClients_continuation` identifies the complete physical
  continuation law from every legal bounded-menu history and sufficient fuel.
* `Compilation.ledgerClients_outcomeLaw` gives the initialized source law for
  the actual ledger clients.
* `Compilation.ledgerClients_noExclusions` and
  `Compilation.ledgerClients_noCharges` transfer the clean-path guarantees to
  supported physical ledger-client executions.

The generic continuation theorem applies to every bounded behavioral profile,
including unilateral alternatives. It is independent of source syntax,
utilities and equilibrium. Its proof reuses the actual protocol runner,
finite-menu restriction, policy decoder and recorded-response origin theorem.
The source compiler then instantiates it with its certified assessment.

The compiler does not mandate a hand-selected fallback such as fair play after
all unfamiliar observations. The common equilibrium completion selects the
entire response law, including off-path choices and beliefs, before the policy
is exposed. A separate posterior proof for each game is therefore not required
from a compiler user.

## Ledger observation scope

Ledger-client agreement assumes the supplied observation kernel returns the
empty pending sample for every player and pending pool. This is an information
premise of the interface, not a restriction on opponents' actions or a change
to execution semantics. It already holds for the maintained periodic service.
The ordinary physical clients retain the preservation theorem's arbitrary
pending-observation scope. Erasing informative delivered pending data without
this premise requires a separate information-invariance result.

## Semantic construction and executable synthesis

The compiler is a uniform Lean semantic function. Its completion backend uses
classical selection from the existing common-limit preservation theorem. The
output supplies a complete mathematical strategy, not an algorithm that
computes numerical strategy coefficients or generated Python code.

Executable synthesis is a separate refinement. It needs effective finite input
representations and a constructive, certified completion backend, followed by
code generation for the selected policy. Defining the semantic compiler does
not discharge that task. The source-to-graph compiler and physical client
realization proofs remain reusable for such a backend.

## Regression consumer

[The compiler regression](../VegasTests/RecoveryCompiler.lean) supplies the
existing Odds–Evens service, audit and source certificates to the generic
compiler. It quantifies over every supplied intended equilibrium, then
specializes to the fair assessment and its exact joint outcome law. It supplies
no game-specific commitment or failure-response construction.

The [scenario fixtures](sequential-client-scenarios.md) remain useful operational
diagnostics. Their manually prescribed candidate is distinct from this
compiler's certified selected strategy.
