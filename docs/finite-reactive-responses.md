# Finite semantic responses

## Boundary and assumptions

A finite runtime instance specifies which messages players can send. Its menu
must include deviations and signaling, independently of the prescribed source
profile and utilities. Private strategy memory and computation have no size or
cost bound. Fresh hidden commitment meanings are semantic data: choosing one
changes the future behavior of that handle.

[ReactiveFiniteResponses.lean](../Vegas/Pending/ReactiveFiniteResponses.lean)
constructs a complete finite menu **relative to the existing packet syntax and
explicit message bounds**. A `MessageBounds` value supplies a finite raw-value
alphabet and a range of prepared handle serials. With finitely many players,
the construction includes every packet constructor over these domains.

| Component | Admitted choices |
|---|---|
| Event address | Every event of the graph, regardless of readiness or method |
| Handle | Every principal, every initial input slot, every prepared serial below the bound |
| Commitment packet | Every event/handle pair, including invalid ownership or event kind |
| Opening packet | Every event/handle/value combination, including incorrect openings |
| Withholding packet | Every event, including premature or redundant calls |
| Malformed packet | Every raw value in the declared alphabet |
| Effective private opening | No opening, or any raw value in the alphabet, regardless of the event's expected type |
| Replay | Every locally known envelope, without a separate identifier cutoff |
| Silence | Always available |

The exact membership theorem is `MessageBounds.menu_mem`: an action is legal
if and only if it satisfies the displayed bounds and is a normal form. This
supplies all bounded response syntax, not just compiler outputs. It does not
validate any packet or promise inclusion or acceptance.

These are explicit model premises. They are not a byte encoding or decoder for
a concrete blockchain. The packet language already uses graph event addresses;
unknown byte-level addresses and method identifiers require a separate encoding
analysis. The value alphabet also bounds effective hidden submission meanings;
it is not merely a public packet-size constraint. An encoding theorem must
justify its treatment of those meanings and of malformed traffic.

The interaction horizon is another substantive premise. It bounds network and
service opportunities, including passive observations and reactions. Contract
timeouts alone do not imply it. See the
[sequential-equilibrium design](sequential-equilibrium-design.md#finite-public-behavior).

## Removing ineffective private distinctions

[ReactiveResponseNormalization.lean](../Interaction/ReactiveResponseNormalization.lean)
provides an application-independent certificate. Submission normalization
depends only on the sender and its application view; it is idempotent and must
preserve both the exact public packet and the entire application effect.
Unavailable replays normalize to silence. Replay availability is reconstructed
from own emitted packets, passive foreign leaks and the ledger.

The Vegas instance in
[ReactiveNormalization.lean](../Vegas/Pending/ReactiveNormalization.lean)
removes private opening metadata unless the packet can register a fresh owned
prepared handle. An arbitrary annotation on a malformed packet, or a new
annotation on an already fixed handle, cannot affect that registration. Neither
annotation becomes a separate action in the normalized menu.

Fresh opening material remains unchanged, including a value of the wrong type
for the addressed event. A fresh submission with no material remains an
irrevocably unopenable commitment. The exact packet remains unchanged, even when
the application will reject it. Malformed and rejected packets can still be
observed in flight, replayed, included and used as public signals under the
chosen observation rule and scheduler. No leak or scheduling rule is altered.

`SubmissionNormalization.effects` proves that a single original response and
its normal form produce the same application state, network state, receipts,
scheduler recall and other players' recall. It assumes the native input-recall
invariant, which connects replay knowledge to the network's actual inputs.

**The sender's raw-action recall is deliberately outside that equality.** A raw
game can record an unavailable identifier or an ignored annotation. The finite
semantic game permits only normal forms in its legal histories. The checked
one-step theorem is not a whole-policy quotient theorem or an equilibrium
equivalence between those two presentations. Private implementation realization
alone does not establish such an equivalence either. Additional universally
ineffective distinctions, if found, need their own semantic analysis.

## Compiler and assessment status

[ReactiveNormalPolicy.lean](../Vegas/Pending/ReactiveNormalPolicy.lean) proves
that normalization fixes the compiler's entire response law at every input,
including its recovery policy. Every supported compiled response is a normal
form. This theorem does not assume a service schedule or a finite value domain.

Fitting those responses into a chosen finite instance additionally requires
coverage of source values and enough prepared serials. A theorem for all source
profiles needs coverage of every legal source choice, not just the finitely many
values sampled by a particular profile. An unbounded source value domain needs
an explicit domain restriction or a justified encoding abstraction. The raw runtime's
fresh-handle theorem uses an unbounded supply and does not prove coverage by a
chosen finite range. A compiler must discharge these obligations; silently
replacing an out-of-bounds response by waiting would change its behavior.

For each bounded instance and scheduler horizon, the generic finite-history and
assessment theorems apply. The
[regression fixture](../VegasTests/ReactiveFiniteResponses.lean) checks malformed
signaling, wrong-method/foreign-handle openings, retained wrong-type commitment
meanings, unopenable commitments, ignored private material and replay coverage.
It also instantiates finite histories and a consistent Bayes assessment for the
complete bounded menu.

That assessment randomizes uniformly over every legal choice. Its consistency
does not assert optimality. The remaining compiler obligations are source-law
correctness, coverage by the finite instance, one common tremble sequence with
convergent off-path beliefs, and target continuation incentives under those
beliefs. Native sequential-equilibrium preservation remains open.
