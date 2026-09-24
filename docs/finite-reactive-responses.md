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

## Compiler coverage

[ReactiveNormalPolicy.lean](../Vegas/Pending/ReactiveNormalPolicy.lean) proves
that normalization fixes the compiler's entire response law at every input,
including its recovery policy. Every supported compiled response is a normal
form. This theorem does not assume a service schedule or a finite value domain.

[ReactiveFiniteCompiler.lean](../Vegas/Pending/ReactiveFiniteCompiler.lean)
proves coverage for **every source policy at every legal decision history**,
including histories generated by earlier deviations, under two certificates:

1. The raw-value alphabet covers every value of each binding or publication
   output type. `MessageBounds.CoversOutputValues` is this sufficient static
   condition. It does not depend on utilities or one prescribed strategy's
   sampled values. Private-input and chance types require no extra wire choices
   unless an event can bind or publish them.
2. The prepared-candidate range contains at least `H` serials per player, where
   `H` is the scheduler horizon.

The value criterion is deliberately sufficient, not a characterization of all
encodable programs. A more precise certificate could use proved reachable-value
ranges, including the initial input law and every legal deviation. That range
analysis is not implemented. An unbounded source binding domain requires an
explicit restriction or a justified encoding abstraction before a finite
alphabet can cover every legal choice. Finite support of one strategy's random
law does not supply a uniform bound for all strategies.

The capacity certificate follows from checked accounting:

- [ReactiveResponseBudget.lean](../Interaction/ReactiveResponseBudget.lean):
  at any active decision, the player's previous response count is strictly
  below `H`. The activation has already consumed its scheduler opportunity.
- [ReactiveCandidateBudget.lean](../Vegas/Pending/ReactiveCandidateBudget.lean):
  every occupied prepared serial appears among that owner's previous commitment
  submissions. At most one serial is mentioned per response, so the least fresh
  serial is at most the previous response count. Hence it is below `H` at every
  active decision. Large previously chosen identifiers do not change this bound.
- [ReactiveBoundedHandles.lean](../Vegas/Pending/ReactiveBoundedHandles.lean):
  accepted handles remain within the packet domain at every legal finite-menu
  history. Replays and passive leaks preserve packet bounds, and inclusion can
  install only the handle carried by a submitted packet.

The proofs allow arbitrary earlier responses, malformed traffic, repeated
submissions, and arbitrary schedulers and observation rules. They impose no
local preparation cost. `H` is a sufficient capacity, not a claim of minimum
capacity for every program or service. After all opportunities have been spent,
the theorem does not promise a further fresh handle inside that range.

## Exact finite-game representation

[ReactiveMenuPolicy.lean](../Interaction/ReactiveMenuPolicy.lean) represents a
raw policy as a behavioral policy of a finite-menu instance. Construction
requires an admissibility certificate covering **all legal histories**.
At every such history the response law is unchanged. The total function also
has a default at inputs where coverage fails; admissibility proves those inputs
cannot occur at a legal decision. No reachable out-of-bounds response is
replaced by silence or another action.

`MessageBounds.compileFinitePolicy` supplies the actual reactive compiler's
certificate from the value and capacity premises. Its checked continuation
theorem, `MessageBounds.compileFinitePolicy_run`, preserves the complete history
law from every legal finite-instance prefix and for every evaluation fuel.
It includes recovery at off-path prefixes and the actual remaining clock.
The underlying generic theorem also applies to arbitrary covered policies.
This represents the reactive compiler faithfully; source-to-reactive correctness
and optimality are separate obligations. It does not identify the finite game's
deviations with all deviations in the unbounded raw game.

## Assessment status

For each bounded instance and scheduler horizon, the generic finite-history and
assessment theorems apply. The
[regression fixture](../VegasTests/ReactiveFiniteResponses.lean) checks malformed
signaling, wrong-method/foreign-handle openings, retained wrong-type commitment
meanings, unopenable commitments, ignored private material and replay coverage.
It also instantiates finite histories and a consistent Bayes assessment for the
complete bounded menu, proves coverage of every Boolean source policy after
arbitrary histories, and applies fully mixed perturbations to the actual
compiled profile. It also instantiates consistent completion of that compiled
profile. Separate checks retain fresh slots through replay and foreign
references, and demonstrate possible exhaustion after the allotted responses.

The uniform assessment randomizes over every legal choice. More generally,
[ReactiveConsistentAssessment.lean](../Interaction/ReactiveConsistentAssessment.lean)
proves that **every** profile of the finite instance has a sequentially
consistent belief completion. Positive uniform-reference perturbations supply
Bayes assessments; one common subsequence converges at all sites. This preserves
the prescribed strategy exactly and makes no claim of full-sequence convergence
or effective belief synthesis.

[ReactiveFiniteConsistency.lean](../Vegas/Pending/ReactiveFiniteConsistency.lean)
applies this construction to the actual compiler and recovery under the value
and capacity certificates. Its beliefs need not agree with a source assessment
or make the compiled continuations optimal. The remaining compiler obligations
are source-law correctness and finding a consistent completion that preserves
continuation incentives. Concrete backend encoding and progress assumptions
still need justification. Native sequential-equilibrium preservation remains open. The
[selective-association separation](selective-association-proof-contract.md)
proves that claims and evidence naming only accepted source bindings are
insufficient for the stated native service, even with the full declared
finite response menus and whole-policy continuation deviations.
