# Native public-message runtime

`Interaction` supplies the active runtime model: a public message pool,
principal-scoped commands, polling histories, receipts, delivery/inclusion
choices, and an explicit ideal commitment service.

`Vegas/Compile/SealedSource.lean` connects checked source programs and their
event graphs to this model. Retained game adapters expose bounded native policy
games for the sealed-message applications.

Finite supported native runs,
including replay of observed messages, decode to reachable graph prefixes.
Terminal decoded prefixes reconstruct written-order source executions and
matching decoded public results. Ideal hiding results concern the declared
ideal service and observation boundary.

## Fixed windowed block service

The generated fixed service is a complete checked strategic endpoint, not only
a local handler result. Its coordinatewise compiled profile has the source
public-result law. Every arbitrary finite-support, history-dependent randomized
unilateral raw policy is matched, against unchanged opponents, by a finite
mixture of legal source deviations with the same joint completion and public
terminal-result law. Consequently source public-outcome lower bounds transfer,
and compiled profiles preserve and reflect epsilon-Nash with the same epsilon.

The exact premises matter: initial controller reads are public; generated
bindings have valid origins; required fallback handlers are source-certified;
the player roster is duplicate-free and covers decision owners; and deviation
simulation has a distinct unchanged relay. The theorem classifies compiled
profiles, not every equilibrium of the larger runtime game. The service has a
fixed block structure, not adaptive pending-message delivery.

## Pending-message adaptive service

The active target retains pending messages, recipient-local polling, public
receipts, delivery/inclusion choices, reactions, deadlines, and replay in the
strategic observation surface. Checked infrastructure currently includes:

- service, checkpoint, and completed-prefix generalization;
- the source law for the first poll;
- preservation of an accepted request across a delivery/reaction round;
- the paired delivery/reaction segment used by the intended extraction;
- complete unrestricted-binding and public-choice delivery blocks, including
  recipient delivery and reaction slots, source successors, next checkpoints,
  and deadline-aware progress from an unchanged relay.
- complete ordinary and copied conditional delivery blocks, including the
  resolved-binding provenance needed for expiry eligibility, source successors,
  next checkpoints, and deadline-aware progress from an unchanged relay.
- source coverage and terminal completion for every complete repeated delivery
  execution assembled from those four block successors.

The current delivery model deliberately exposes a recipient's delivered pool
to its policy. A source view does not contain that pending-payload pool, while
the runtime policy input does. Accordingly, source-view equality alone cannot
establish the `PolicyAgreement` invariant after delivery: the paired runs must
also agree on the delivered pool (or the runtime must provide a hiding
projection). This is the information-flow condition still needed before a
whole-prefix deviation simulation can be instantiated for public in-flight
messages. Source-level quitting does not discharge it.

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
