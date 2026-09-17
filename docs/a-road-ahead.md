# A road ahead

This is a non-binding implementation roadmap. The [active tower](active-tower.md)
records checked results; this document describes the next target boundaries.

## Goal and established boundary

Compile the complete checked source language to executable protocols, preserving
at least Nash equilibrium under explicit runtime capabilities. Ethereum is a
grounding target, not the owner of runtime-general concepts.

The checked chain is:

```text
SourceProgram → dependency-driven EventGraph → public pending-message application
```

It preserves honest outcome laws and simulates every unilateral native deviation
by a finite mixture of source deviations against unchanged opponents. The mixture
is chosen before the private initial draw. Same-error epsilon-Nash equivalence
holds at compiled profiles, and source-outcome lower bounds transfer without any
assumption about the adversary's preferences.

The target uses ideal opaque commitments, authenticated commands, the declared
public chance kernels, and a concrete finite adaptive epoch service. It permits raw
submissions, competing candidates, failed openings, replay, delivery before
inclusion, and adaptive wire choices. It does not implement cryptography, gas,
transaction execution, ledger finality, or unrestricted fair scheduling.

Every source constructor is covered, including heterogeneous values, rejecting
guards, initial secrets, and dependent chance. Failure and disclosure are source
choices. No quitting-dominance premise is needed for this exact barrier-preserving edge.

The [source contract](source-semantics.md), [source rationale](source-design-rationale.md),
[source/graph edge](source-graph-edge.md), and
[message proof guide](event-pending-deviation.md) specify these boundaries.

## Scheduling and the refinement direction

Concurrent and sequential compilation use the same graph and native runtime.
Sequential compilation adds predecessor barriers rather than supplying another
executor. The [EventGraph design](event-graph-design.md) states the operational
and strategic correspondence.

Adding barriers is a compiler transformation, not an assertion that every host
which admits concurrency already enforces sequential completion. The useful
closure property is that a backend capable of honoring the graph's declared
predecessors can execute either compilation mode.

Further target levels should add meaningful operational structure while
realizing the higher-level execution, observation, and strategic contracts.
A single universal ordering of all features is not assumed. Complication-specific
proofs may be independent where their contracts genuinely compose.

## Next target: transaction and block execution

Add an independently executable host with authenticated callers, transaction
identities, nonces, atomic application state changes, rejection/revert receipts,
block-derived clocks, and an explicit finality boundary. Distinguish submission,
delivery, inclusion, and finalized effects. Keep arbitrary transaction traffic
and adaptive ordering visible to the permitted observers.

The application semantics should remain a parameter of this host. Vegas lowering
then supplies the handler implementation and its refinement, rather than baking
Vegas guards or source syntax into the ledger model.

The proof must establish:

- representation and observation correspondence for actual reachable executions;
- backtranslation of arbitrary transactions, including malformed and repeated ones;
- a service condition strong enough to protect unchanged players before expiry;
- a composed outcome/deviation or utility simulation, with every new premise
  attributable to the target model.

Do not require a separate intermediate language merely to choose a queue policy.
Alternative services can implement one host interface. Conversely, separate
state-machine edges are appropriate when they add meaningful operational
structure, such as atomic transactions or finalized blocks.

Exit test: a theorem over the real transaction runner, composed to the source
without excluding a source constructor or assuming the desired whole-run law.

### Protocol/host proof interface

The current `EventGraphRuntime` executes the typed graph through the shared message
runner, and its strategic proof is graph-relative. A separate sealed-protocol
language is not required for that result.

When implementing another host, investigate a smaller reusable interface between
graph-directed protocol rules and transport, commitment, clock, and chance
services. It should retain typed payloads, owners, binding origins, public
validation dependencies, disclosure prerequisites, and failure results.
Candidate preparation, commitment acceptance, visible opening submission,
validation, and resolution remain distinct events even when a host combines
some transitions.

The proof interface must relate observations and legal policies as well as
states. Several host steps may implement one graph action, but delivery cannot
be erased as an unobservable step: seeing a pending opening can change a later
decision. Local execution and information laws must justify the extracted graph
policy against unchanged opponents. The whole-run deviation law is a conclusion,
not an assumed field of a purported local correctness contract.

Separate safety from progress. A semantic deadline-relative service contract
should admit both the concrete reserved service and a ledger implementation;
sample-once chance and stable accepted candidate identities remain separate
obligations. Introduce utility-dependent comparisons only for edges that need
them, rather than weakening an available exact outcome-law certificate.

Use a small rule or simulation interface if it suffices. Add another executable
representation only if its independent semantics makes a real compiler edge
simpler. The acceptance test is reuse of the graph-level strategic argument by a
second host, covering every source constructor and arbitrary native deviations.
A shorter theorem statement alone is not evidence that the interface helps.

## Executable code and VM refinement

Compile the graph/application artifact to identifiable executable code. Separate
computable lowering and representation from noncomputable strategy-analysis
witnesses. Prove storage layout, encoding/decoding, expression evaluation,
dispatch, handler execution, linking, and deployment against the chosen VM.

An arbitrary semantic expression interface is not automatically executable.
A concrete backend must implement its operations and account for finite word
sizes, encodings, resource limits, and failed execution. Instruction-level code
proofs are ingredients, not a replacement for the whole application edge.
Test the executable path from serialized checked input to generated artifact;
elaborator evaluation of a concrete example does not establish that path.

Exit test: the strategic theorem names deployed code and its execution host.
Independent instruction vectors and differential execution tests should help
detect proofs against an incorrect VM specification.

## Realizing ideal services

Keep each capability explicit and require it only where the program uses it.

| Capability | Implementation obligation |
| --- | --- |
| Commitments | Hiding and binding in an appropriate computational model; authenticated openings; no leakage through compliant failed-opening packets. |
| Private setup | Realize the joint initial law and its observations before play. Refusal to establish setup is a separate pre-play mechanism. |
| Chance | Realize the declared conditional law, once, with the required availability. Marginal fairness alone is insufficient. |
| Progress | Supply service before the relevant deadline and under the stated finality rule. Eventual fairness after expiry is insufficient. |
| Costs | Specify who pays fees and how resource failures affect state; interpret costs in source outcomes or bound their utility effect. |

Ideal commitments need not be byte strings at every layer. Opaque handles are the
right interface until an encoding or concrete cryptographic implementation is
being verified. Public EVM storage does not itself realize private candidate
memory; the lower edge must implement that capability explicitly.

Computational security, service failure, and finality errors generally lead to
approximate laws. Turning probability error into incentive error requires an
appropriate bounded utility or discrepancy condition. State those assumptions
instead of silently treating the exact ideal theorem as a concrete security proof.

## Extending guarantees and feature combinations

An artifact's game is induced by its operational semantics and observation
interface. FOSG or another presentation can support analysis; it is not a separate
compiler destination that substitutes for the actual runtime.

Add complications as separate edges when that makes their contracts local, or as
orthogonal parameters when one carrier supports them naturally. Composing two
feature proofs requires the second theorem to apply after the first feature has
been added. Two marginal non-leakage statements are not enough: a random bit
`R` and `R xor secret` each hide the secret individually but disclose it together.

Parallel admission, coalitions, and utilities over native traces are distinct
extensions. The existing unilateral theorem fixes the environment policy across
comparisons; it is not a builder/player coalition theorem. An outcome-law
certificate transports utilities of the decoded source result, not arbitrary
preferences over timing, fees, receipts, or message traffic.

A future edge that adds an informed quitting opportunity may require a stronger
incentive condition. For example, play with fair payoff `+2/-2` has expectation
`0`, exceeding an ex-ante quit payoff `-1`. Learning the payoff before deciding
whether to quit gives expectation `(2 - 1)/2 = 0.5`. Ex-ante quit dominance does
not control this added information. The current source already has strategic
disclosure/failure, so this example is a test for a *new* target capability, not
an omitted hypothesis of the checked theorem.

Similarly, an accepted-event set is not a sequential source prefix: independent
events may finish out of order, and a sealed commitment does not publish its
value. A concurrent lowering needs its own causal and information certificate.

## Engineering acceptance criteria

Each new edge has its own executable carrier, observation interface, strategy
space, compiler, and strategic certificate. Keep source-specific code in Vegas,
message/service semantics in Interaction, generic game theory in GameTheory,
and chain/VM machinery in separate target libraries.

The richer Vegas (elazarg/vegas) frontend should produce the checked source artifact through
a specified elaboration boundary. The `Vegas.Language` surface-syntax prototype is not
yet that verified frontend; extending the minimal source with its entire syntax
is not a prerequisite.

Keep one implementation of each compiler edge. Delete superseded paths rather
than retaining compatibility aliases or passive source copies. Keep
`Paper.lean` to direct delegations for capstones and important lemmas.

At a milestone, report source coverage, target depth, strategic conclusion,
assumptions, and the next unproved edge. Require the complete warning-free build
and standard axiom audit. Supporting lemma counts and coverage checks alone are
not a compiler-correctness result.
