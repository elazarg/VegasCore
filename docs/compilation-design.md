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

The event graph is the shared dispatch artifact. The strict native edge in
`Vegas.Compile.SealedCompiler` installs one sealed-message rule per graph node
over the `Interaction` pool. Commit packets carry only an opaque handle;
opening packets carry the claimed value and are accepted only after the
corresponding commitment. Correctness is stated against actual graph
reachability and source reconstruction, avoiding a parallel operational
machine hierarchy.

The former `ApplicationPlan` public-choice image was a fused optimization
experiment, not a commitment-preserving lowering. Its source and proofs are
archived outside the build roots; it is outside the active compiler claims.

Probability tables denote exact finite laws. A concrete entropy mechanism,
cryptographic commitment scheme, adaptive delivery service, or blockchain
backend would be a further artifact with its own proof edge.

## Current boundary

The event-graph edge now has a checked strategic theorem at its narrow exact
frontier. `Vegas.EventGraph.Strategic.deviation_law` and its Nash corollary
compare the graph's full behavioral presentation with the canonical
declared-read policy presentation. Under declared-read information locality
and one ready commitment per player, every canonical unilateral replacement
has the exact law of one behavioral graph replacement (not merely a mixture),
for every profile and every observation utility. This theorem is deliberately
graph-level: it does not identify the written-order `sourceGameForm` with the
graph game, and it does not instantiate a message runtime.

The strict sealed-message edge has checked whole-run source reconstruction and
ideal-service hiding laws. Its whole-program strategic preservation theorem is
not yet proved. `SealedCompilation.StrategicCertificate` packages the exact
honest-law and finite-mixture obligations needed for the Nash transfer; no
runtime is granted that certificate by construction.

The active pending-message model has an explicit strategic proof obligation.
`deliver` places the selected packet in the recipient's pool, and the recipient
policy sees that pool. This extra observation is not automatically a strategic
counterexample: inclusion still checks the graph prerequisites, so a pending
opening cannot produce its graph step early. The edge must prove a causal
backtranslation showing that a message selected before inclusion is equivalent
to the corresponding source action at the first source point where its value is
observable. A runtime that lets an accepted action depend on a payload before
that point, or a scheduler that uses private payload data to alter the source
visible future, would require a stronger source observation or a separate
impossibility result. The generic
`GameTheory.GameForm.MixtureSimulationOn.compiled_quit_profile_not_isNash`
theorem proves the mechanism-design step once a runtime resolution law is
supported entirely on the source quit. The sealed kernel's rejected packet is
only a stutter; classifying it as quit is a timeout/resolution theorem.

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

Feature extensions must compose over the same graph artifact. Each new runtime
detail—timeouts, public delivery, cryptographic commitments, ledger admission,
or VM execution—adds a separately typed target and a proof edge. It may not
silently fuse source nodes or invent source outcomes; the edge must state its
observation, progress, and strategic obligations explicitly.
