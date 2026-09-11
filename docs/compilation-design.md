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
paired delivery/reaction segment are checked. An unrestricted binding head now
has a complete delivery-block successor theorem: recipient delivery, reaction
polls, deadline-aware clocking, and unchanged-relay expiry are all in the
actual schedule, with a source successor and next checkpoint. Whole-prefix
pure extraction, randomized extension, and the whole-program law remain open.
These are the next compiler proof, not a narrower substitute.

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
