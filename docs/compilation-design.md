# Compilation design

VegasCore compiles one checked sequential source artifact into an event graph
and then into focused native public-message applications.

## Artifact boundary

Every compiler output retains the code needed by its consumer: typed fields,
node identities, dependencies, guards, rational probability tables, and payoff
expressions. Hashes and source maps can record provenance, but they do not
replace a semantic correspondence proof.

For an edge from source artifact `s` to target artifact `t`, keep four
obligations distinct:

- execution: target steps decode to source steps or justified stuttering;
- observation: target-visible information is simulated by the declared source view;
- strategy: admitted target choices can be translated without unavailable information;
- outcome: decoded terminal results and utilities satisfy the stated law.

An edge may prove only a subset. Support preservation is not progress, and
conformance tests are not refinement.

## Active lowering

The event graph is the shared dispatch artifact. Native compilation installs
handlers for the retained binding, release, and timeout applications over the
`Interaction` pool. Correctness is stated against actual graph reachability
and source reconstruction, avoiding a parallel operational machine hierarchy.

Probability tables denote exact finite laws. A concrete entropy mechanism,
cryptographic commitment scheme, adaptive delivery service, or blockchain
backend would be a further artifact with its own proof edge.

## Current boundary

The fixed windowed block service has a checked whole-program honest law and an
arbitrary randomized unilateral deviation-mixture theorem. Its public-outcome
guarantee and same-error approximate-Nash equivalence are genuine compiler
results under the theorem's eligibility, roster, fallback, and relay premises.

The pending-message development generalizes the service, checkpoint, and prefix
infrastructure. The first-poll source law, delivery/reaction acceptance, and a
paired delivery/reaction segment are checked. Unrestricted binding and
public-choice heads now have complete delivery-block successor theorems:
recipient delivery, reaction polls, deadline-aware clocking, and
unchanged-relay expiry are all in the actual schedule, with a source successor
and next checkpoint. Conditional resolving handlers now have a complete
delivery-block successor theorem as well: both ordinary and copied accounting
constructors use resolved-binding provenance to establish expiry eligibility
under the same schedule. The four block successors compose into source
coverage for every complete repeated delivery execution and terminal graph
completion. Whole-prefix policy extraction, randomized extension, and the
whole-program law remain open; source coverage does not by itself establish
adaptive fairness.

The pending-message model has an explicit strategic boundary. `deliver`
places the selected packet in the recipient's pool, and the recipient policy
sees that pool. The source observation carried by a `ProfilePoint` contains no
pending-payload pool. Thus two executions can agree on the source view while
giving a recipient different delivery inputs; the `PolicyAgreement` relation
then fails at its pool component. A delivery-level strategic theorem needs a
separate hiding/equivalence premise (for example, a cryptographic projection
that erases payload content), or an explicitly richer source observation. The
checked delivery coverage theorem does not assume either premise. The generic
`GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash`
theorem proves the corresponding mechanism-design step: once a runtime quit
law is shown to be supported entirely on the source quit, any strict source
improvement over quit refutes the compiled target equilibrium. The active
delivery model has not yet established that law; its reaction policy still
admits commands beyond waiting or quitting, and some pending payloads are
intentionally visible.

No active theorem establishes general adaptive scheduling equivalence,
censorship resistance, cryptographic hiding, gas behavior, or EVM execution.

## Source and ownership constraints

Fallback behavior belongs to the source language. A timeout may select a source
choice only when the checked source artifact declares that alternative and its
guard. Compilation must not invent a nullable result, termination, or default
merely to make a runtime resolve. Ownership is likewise preserved: ordinary
choices remain owner-authorized; permissionless expiration is a separately
declared resolution action; binding openings must match the recorded binding
origin and verifier.

Feature passes must compose over one application plan. Binding, chance,
ordinary public choice, conditional publication, and their optional timeout
handlers retain separate eligibility evidence. A later conditional publication
may reuse an earlier binding only through a certified origin and its own source
guard. Combining features requires preservation of allocation uniqueness,
read availability, cache freshness, completed-prefix shape, and handler
noninterference.
