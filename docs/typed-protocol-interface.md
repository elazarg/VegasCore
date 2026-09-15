# Typed ordered protocol

## Interface and status

The typed protocol retains every event-graph operation and hosts it in the
shared public-message application runner. It has no homogeneous-value,
no-sampling, or universally-accepting-guard restriction. This is an operational
model and adapter, not a general source correspondence or Nash theorem.

The implementation boundary is:

| Module | Responsibility |
| --- | --- |
| `Vegas/Protocol/Code.lean` | Typed operations, field layout, and separate initial inputs |
| `Vegas/Protocol/Graph.lean` | Total erasure of graph metadata and retained executable expressions |
| `Interaction/OrderedProtocol.lean` | Runtime-general ordered commitment, opening, chance, and resolution transitions |
| `Vegas/Protocol/Application.lean` | Tagged values and graph guard/chance evaluators for that runtime |

`Interaction` imports no Vegas concepts. The adapter imports graph definitions,
not the source compiler. Source compilation and strategic composition belong
above this edge. `MessageApplication` supplies the existing submission,
delivery, inclusion, receipt, and policy machinery; there is no additional
policy runner.

The public program counter determines which application operation can take
effect. It does not prohibit off-order submission, pending observation, replay,
malformed traffic, or attempted inclusion. Baseline compilation follows the
source-certified canonical order. Parallel admission requires its own proof.

## Code, setup, and stores

Public code contains initial-field types and owners, operation types, declared
reads, guard expressions, chance distributions, and disclosure origins.
Initial values are separate dependent inputs, not public code constants.
Operation fields follow the initial fields without compressing their indexes.

Runtime values are tagged. A wrong-tag opening is possible traffic and fails
validation; it is not a member of a legal source-action subtype. Candidate
identity is separate from source-site identity. Players can prepare several
candidates, and accepting a previously unprepared candidate freezes it as
unopenable in the ordinary opaque mode.

The runtime keeps distinct stores for immutable bound material, effective
operation results, and public disclosures. It also retains captured guard
contexts and candidate meanings. Player observations contain their own setup
and bound values. Environment observation excludes these private components;
the surrounding message runner exposes the pending traffic it specifies.
Observation definitions alone are not a joint information-flow theorem.

## Validation and failure

In ordinary opaque/manual mode, commitment inclusion does not test the guard
or require an openable candidate. Opening checks the current site, authenticated
sender, accepted candidate, commitment verification, tag, and retained guard.
The Vegas adapter evaluates the guard on its captured binding-time inputs.
Those inputs may contain private fields: this is an explicit ideal verification
capability, not a claim that an ordinary public contract can read them.

Rejected attempts do not advance the application counter. They remain
retryable and may be transport-visible. At expiry, a configured resolution can
publish its designated value and advance. Neither the existence of that value
nor its type proves that this transition implements source quitting.
The adapter does not choose defaults on the programmer's behalf.

The intended compiler interpretation is that failed opening and invalid opening
resolve to the source-declared quitting behavior. That interpretation is not
yet supplied generally by the Lean source rules:

- `SmallStep.commit` admits only values satisfying the guard in the owner's
  commitment-time view.
- `SmallStep.reveal` copies the original sealed value without a failure branch;
  the original binding remains in scope.
- `ConditionalOpening` expresses a separate optional copy of an original
  secret. Declining that copy preserves the original secret.

Delaying a check over the same value and immutable inputs preserves its Boolean
result. It does not by itself prove that all failed executions correspond to
one legal source continuation. In particular, treating failed publication as
if the original secret had always been a null value can invalidate a later
guard that used that secret. An already published dependent value cannot simply
be retracted. The [mathematical note](ordered-protocol-argument.tex) gives a
counterexample to this per-cell replacement rule, not to all possible compilers.

The revised source/runtime relation specifies the original private value, the
validated `Result` publication, subsequent decisions, and explicit settlement.
Failure is itself a source choice, including for unsatisfiable guards; ordinary
failure-free feasibility is optional rather than a well-formedness premise.
Ordinary public and payoff expressions must eliminate `Result` explicitly, so
failure neither supplies a fabricated payload nor wins a comparison vacuously.
This relation is under construction and must not be bypassed by a global
"resolution is source-correct" field.

The [deferred-guard specification](deferred-guards-semantics.tex) develops a
candidate source interpretation in `Interaction.GuardedPublication` and
`Interaction.BoundPublication`. It separates pending publication, resolved
failure, and ordinary typed values. Relations wait for their dependencies;
if a publication would close a false relation, that publication fails while
earlier publications and private bindings remain unchanged. The checked laws
cover consistency, write-once publication, failure attribution under owned
pending dependencies, and successful publication of any satisfying ordinary
assignment. Heterogeneous partial-disclosure tests and an informed-failure
matching-pennies Nash example check that the component is nonvacuous.

These components do not change the current `Vegas.Core` rules or this typed
adapter. Source expressions, observations, chance, and settlement still need
one integrated semantics and a compiler correspondence. In particular, the
adapter's ideal evaluation of private guard inputs is not an implementation
of deferred public validation.

The generic runtime also has certified-binding and recovery modes. These are
explicitly stronger ideal capabilities: they check a hidden candidate before
acceptance and can disclose the same immutable value without its owner's
cooperation. They are useful comparison models, not properties of ordinary
hiding and binding, not established indispensable requirements, and not the
selected implementation of quitting. Their availability must never silently
replace the intended deferred-validation compiler contract.

## Chance and initial disclosure

A chance operation obtains its retained conditional kernel from the effective
declared snapshot and publishes the sampled value in the same transition.
An unavailable snapshot or kernel stutters without drawing. A successful draw
advances the counter and records the result, so later ticks cannot resample
that site. The capability carries a checked typed-support property; rejecting
ill-typed draws and retrying is not a valid way to implement a source kernel.

Initial private fields are supplied through an ideal typed setup. Their owners
can use them in guards. An initial-origin reveal reads that supplied value
automatically when enabled. This models availability of the source's
deterministic input disclosure; it does not prove availability on a concrete
ledger. A host which instead lets a player withhold it needs an explicit source
failure interpretation, just as for commitment-produced disclosures.

Neither chance nor initial disclosure has a fabricated quitting default.
Concrete entropy, private setup, and verification require their own realizations.

## Proof obligations and acceptance

Local laws establish candidate immutability, rejection behavior, setup
separation, and the conditional chance transition. These laws do not establish
a whole-program honest law or deviation backtranslation.

The model-readiness test exercises heterogeneous values, a genuinely rejecting
guard with private and public inputs, initial-origin disclosure, dependent
chance, competing/unopenable candidates, retries, and deadline resolution in
the shared runner. Passing operational tests alone does not settle the source
failure interpretation above.

For the source compiler edge, prove:

1. Successful operations realize the corresponding typed graph step, including
   the correct guard context and chance law.
2. Authorized resolutions implement the programmer's source alternatives while
   preserving relevant prior knowledge and public effects.
3. Honest policies have the exact source outcome law under named, deadline-relative
   service and capability assumptions.
4. Arbitrary unilateral native policies admit a causal source comparison with
   unchanged opponents and an environment fixed across the comparison.
5. Every unilateral target policy has the exact law of a causal mixture of
   source deviations under canonical order, unchanged opponents, and the same
   fixed admissible adaptive environment.

The coupling in the fourth item must have the claimed source marginal law.
A supported source witness is insufficient for expected-utility or Nash
reasoning. Extra observations must be handled jointly with information already
present, not by separate marginal hiding claims.

The [road ahead](a-road-ahead.md) states the full compiler milestones. Until the
source failure interpretation and these laws are proved, this adapter is not a
replacement for the restricted backend's strategic certificate.
