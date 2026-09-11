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

The strict sealed-message edge currently has support-level source
reconstruction and ideal-service hiding laws. Strategic preservation for
pending messages and public scheduling is not yet proved. The active strategic
interface is `SealedCompilation.StrategicCertificate`; once a runtime supplies
its honest and deviation-mixture fields, the generic GameTheory theorem gives
same-error Nash preservation and reflection. The old fixed-windowed theorem is
archived and is not a theorem for the strict compiler edge.

## Pending-message and timeout boundary

The active runtime retains pending messages, recipient-local polling, public
receipts, delivery/inclusion choices, reactions, deadlines, and replay. The
strict compiler's operational theorems cover arbitrary finite native actions
through these mechanisms and reconstruct every terminal decoded prefix in the
written-order source semantics. The timed sealed adapter adds a public clock
and explicit expiration transitions while retaining the same source-prefix
guarantee.

The current delivery model deliberately exposes a recipient's delivered pool
to its policy. A source view does not contain that pending-payload pool, while
the runtime policy input does. Accordingly, source-view equality alone cannot
establish the `PolicyAgreement` invariant after delivery: the paired runs must
also agree on the delivered pool (or the runtime must provide a hiding
projection). This is the information-flow condition still needed before a
whole-prefix deviation simulation can be instantiated for public in-flight
messages. Source-level quitting discharges a separate branch only after the
runtime's resolution edge supplies a quit law. The sealed kernel treats
malformed traffic as a stutter; a timeout or other resolution rule may then
classify that run as the source quit, but that classification is a separate
proof obligation. The reusable transfer theorem is proved in
`GameTheoryExtensions.Core.QuitTransfer`.

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
