# Native public-message runtime

`Interaction` supplies the active runtime model: a public message pool,
principal-scoped commands, polling histories, receipts, delivery/inclusion
choices, and an explicit ideal commitment service.

`Vegas/Compile/SealedCompiler.lean` connects checked source programs and their
event graphs to this model. The strict edge emits one rule per graph node, so a
commit and its later reveal remain separate protocol phases. Retained game
adapters expose bounded native policy games for the sealed-message
applications.

The former fused application image and its proofs are archived under
`archive/fused/`; they are not an active compiler edge or evidence for
commitment hiding or public in-flight-message results.

Finite supported native runs,
including replay of observed messages, decode to reachable graph prefixes.
Terminal decoded prefixes reconstruct written-order source executions and
matching decoded public results. Ideal hiding results concern the declared
ideal service and observation boundary.

## Strategic results

The preceding source-to-graph edge has an instantiated simulation:
`WFProgram.sourceGraphSimulation` preserves the full source outcome law and
exactly backtranslates arbitrary declared-read graph policies. Its Nash and
epsilon-Nash corollaries are end-to-end to that graph runner, not to this
message runtime. It supplies the source side of the pending-message proof.

The actual pending-message round game has a constructed source/native coupling
and same-error Nash preservation and reflection under timely service, normal
utility agreement, and explicit conditional timeout-checkpoint comparisons.
Those program-specific comparisons remain obligations. The generic GameTheory
`MixtureSimulationOn` separately gives exact-law transport when a target
supplies its honest and deviation-mixture fields; merely assuming that generic
interface is not an instantiated sealed-compiler result. The old fixed-windowed
theorem is archived and is not a theorem for the strict compiler edge.

## Pending-message and timeout boundary

The active runtime retains pending messages, recipient-local polling, public
receipts, delivery/inclusion choices, reactions, deadlines, and replay. The
strict compiler's operational theorems cover arbitrary finite native actions
through these mechanisms and reconstruct every terminal decoded prefix in the
written-order source semantics. The timed sealed adapter adds a public clock
and explicit expiration transitions while retaining the same source-prefix
guarantee.

The current delivery model deliberately exposes a recipient's delivered pool
to its policy. This is not, on its own, a strategic leak. A delivered opening
is still only a pending packet; the application cannot accept it until the
graph prerequisites are included. The missing invariant is causal rather than
syntactic: a policy may prepare a future message after inspecting a pending
opening, and the backtranslation must show that the same action can be chosen
at the corresponding source reveal point, while malformed or never-included
openings produce no earlier source step. The environment already sees the
pending pool and may base delivery and inclusion on its payloads. Its policy
does not see the ideal service's hidden values. Backtranslation must handle
the former observations; access to the latter would be a stronger information
model and would require a separate argument or an impossibility theorem.
Source-level quitting discharges a separate branch only after the runtime's
resolution edge supplies a quit law. If the runtime permits selective quitting
using extra information, its utility must be compared with feasible continuation
with the existing commitments fixed, at that finer information. An ex ante
comparison with always quitting is insufficient. The generic selective-stopping
bound proves a loss of at least `margin * probability_of_quitting` when the
continuation advantage is at least `margin` on every supported stopping state.
If the action is instead an ordinary source deviation, its exact simulation
requires no incentive assumption.

The native `SealedTimeout.resolved_policy_utility_bound` covers arbitrary
randomized policy continuations of a locked disclosure checkpoint, assuming
resolution. Its utility observes only the fixed opening or expiration. The
compiled two-player regression gives an exact selective-withholding threshold
in that actual runtime. Neither result constructs a whole-program source
strategy or supplies settlement. In particular, the current timeout adapter
freezes protocol acceptance and does not resolve a missing initial commitment.

The compiled release barrier is stronger than checking the arriving opening:
`SealedFragment.opening_barrier_trace` fixes every earlier commitment at the
first opening-ready snapshot and preserves those values through the complete
policy trace. Pending-message observations cannot rewrite those values.

Still open are whole-prefix extraction of a pure source deviation, linear
extension to arbitrary randomized deviations, and the final whole-program
honest/deviation laws. The intended endpoint is an
arbitrary randomized unilateral deviation-mixture theorem, source guarantee,
and same-epsilon Nash equivalence, followed by public adaptive scheduling under
explicit information-flow and deadline-fairness assumptions.

Local timeout and release handlers describe what happens when the relevant
message is submitted and included. They do not prove adaptive service progress.
Malformed traffic, withholding, and scheduling choices therefore remain part
of the runtime behavior. Censorship tolerance, eventual inclusion, concrete
cryptography, and blockchain realization require additional models and proofs.
