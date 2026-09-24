# Pending binding proposals around a source game

## Status and boundary

This is a design candidate for `C(G, k)`, not an approved implementation plan or
a proved source-to-native SE correspondence. It retains capabilities that a
direct operational proof must address. Neither its sufficiency for general
source programs nor its minimality among possible SE-preserving abstractions
is established.

The core program `G` keeps its typed commitments, ordinary disclosure choices,
guards, private inputs, and publication results. The analysis service adds
**pending proposals to bind a named source commitment**. Creating such a proposal
requires sending a binding request. There is no standalone seal operation and
no `failure(value)` result.

A proposal certificate says `proposal p contains v`. Public acceptance can
later establish `source binding b uses p`. Together these observations establish
the named binding without another delivery of the certificate. The certificate
alone does not assert that `b` has been bound. This is the capability exercised
by [selective association](selective-association-proof-contract.md).

## Concrete data

Use one pending communication interpretation, with these components:

| Component | Meaning |
|---|---|
| Source state | The existing setup/program state, including the original private inputs. |
| Operation names | Static source declaration names identifying binding and publication operations; a request can mention an operation of the wrong kind. |
| Proposal references | Owner-scoped opaque names from an explicitly finite alphabet. Initial commitments have distinguished references; fresh proposal names have a declared creation permission. |
| Proposal meanings | `CommitmentCandidates Player Label Value`: fresh, permanently openable to one value, or permanently unopenable. Only the owner observes its private meanings. |
| Accepted associations | A public partial map from source binding names to proposal references. A reference can be accepted for at most one binding. |
| Service state | The public clock, current opportunities, and source-operation activation/deadline information specified by `k`. |
| Network and recall | Existing `MessageNetwork` pending messages, recorded messages, known messages, and the existing reactive observation/own-action recall. |

`Value` is a declared finite alphabet of tagged semantic values, using an
existing dependent value type where possible. It can include values unsuitable
for a particular source binding type. Such a proposal produces the ordinary
binding failure when accepted there. Its independently disclosed contents
remain a communication observation. The program cannot inspect those contents
through its failed binding.

References are semantic identities, not native serial-number encodings.
Their equality and reuse remain observable. The implementation must map all
admitted native identities into this alphabet. References to non-binding initial
inputs or another owner's initial slot cannot silently become fresh creatable
proposals: they must remain uncertifiable references, or be removed by a proved
quotient. A private initial input does not initialize a certificate.

Reuse `Interaction.CommitmentCandidates`, `MessageNetwork`, `ReactiveApplication`,
and finite response menus. Keep source rules in `Vegas.Source`; native encoding
and the correspondence belong in `Vegas.Pending` and `Vegas.Compile`. No new
generic service hierarchy is needed. The source interpretation must not import
or invoke `EventGraphRuntime.handle`.

## Messages and one player response

A public message contains its authenticated author, a semantic message reference,
one of the following bodies, and optionally a possessed proposal certificate:

| Body | Intended meaning |
|---|---|
| `tryBind(operation, proposal)` | Ask to associate this immutable proposal with a source binding. |
| `tryPublish(operation, proposal, claimedValue)` | Ask to disclose the associated binding using the supplied opening claim. |
| `tryWithhold(operation)` | Ask to execute the source withholding choice. |
| `claim(value)` | Communicate without requesting a game transition. |

Each activation offers silence, submission of one message, or rebroadcast of
one known immutable message. Rebroadcast preserves the original author;
the current broadcaster obtains no authority to act as that author.

For a binding request naming a fresh creatable proposal owned by the sender,
the same response privately chooses an opening value or permanent
unopenability. The meaning is fixed before the message enters the network.
For an existing reference, the response cannot overwrite the meaning. Foreign
references cannot create or alter another owner's proposal. These rules apply
even when the addressed operation is unready, belongs to another player, or is
not a binding operation.

An owned reference with no creation permission cannot acquire an opening this
way. If still fresh, its first binding request freezes it as unopenable. This
preserves the distinction between preparing an allowed fresh proposal and merely
mentioning an initially unused reference.

A response may attach an owned certificate or one already observed. Issuance
can use the proposal just created in that response. A claim-only message may
carry existing evidence, but cannot create a proposal. Thus creating evidence
consumes a binding-request transmission and retains that request's actual risk
of being accepted. A wrong-kind destination can make a request certainly
ineffective for a particular program; that is not a universal free-seal
capability.

The source menu need not expose ineffective private opening material or failed
certificate queries. Removing those native response names requires an instance
of the checked private-response-alias SE theorem. Public false opening claims,
wrong destinations, reference identities, and rejected requests remain visible.
They are not erased merely because the game state is unchanged.

## Recording and game transitions

The service `k` fixes finite opportunities, partial observation kernels, public
recording, and time progression before utilities are chosen. Passive observation
reveals only foreign pending messages and supplies no private delivery report to
the scheduler. A recorded message remains observable even if its request fails.
Each envelope is recorded at most once; resubmission uses a fresh identity.

Recording first exposes the message and its evidence. Separately, the source
interpreter checks its semantic request against `G`:

- A binding request takes effect only at the named enabled binding operation,
  by its owner, within its service window, with an available binding and an
  unused proposal reference. The source commitment step receives the proposal's
  typed value or ordinary failure. Acceptance records the association.
- A publication request takes effect only at the named enabled publication
  operation, by its owner, using the binding's associated reference and a valid
  opening claim. It executes the existing source disclosure step and its actual
  guard. Publication failure does not retract supplied evidence.
- A withholding request executes the existing withholding action only at the
  matching enabled publication operation.
- A claim or rejected request causes no source game transition. Wrong-kind,
  wrong-owner, premature, late, and invalid-opening requests remain messages.
- A deadline may execute only the source interface's admitted default action:
  binding forfeiture or withholding. It does not introduce a new result value.

These clauses are specified from source operations and the ideal commitment
contract. Their agreement with native authorization and handling is a theorem
obligation. A sequential source cursor is adequate only after proving that the
chosen graph and service complete operations in that source order, including
expiry and every earlier deviation. The first instance must use a matching
order or dependency chain and establish that property. General graph cuts
cannot be discarded on this basis: independently enabled native operations may
complete in a different order.

## What abstraction does this provide?

The current native `Raw` already consists of a semantic type tag and value;
`Payload` already contains binding requests, opening claims, withholding, and
uninterpreted claims. Replacing those constructors by the four bodies above
does not itself provide a stronger abstraction. Replacing a handle by an opaque
proposal name also keeps its equality and reuse behavior; it does not erase
identity as a signal.

The checked private-response-alias theorem does provide one stronger
abstraction: ineffective private opening material and unavailable forwarding
requests can be normalized while lifting sequential equilibria against every
raw continuation deviation. All public packets, pending competition, timing,
and raw own-action recall remain covered by that theorem. It does not remove
the candidate catalogue or application state.

Replacing the compiled graph's game state and handler implementation by the
original source transition and named source store is the substantive additional
proposal here. Utilities would still factor through original types and public
results, and the programmer would write the same program. That correspondence
has not been proved for this service. Even omission of an inert native state
field requires the appropriate invariant and observation argument; it should
not be counted as an already established source abstraction.

It retains proposal identity, delayed acceptance, competition, deadlines,
pending observation, and rejected-message signals. Consequently it is richer
than cheap talk around immediate source moves. Its proposal catalogue and
association map deliberately resemble the corresponding native state: they
describe the strategic meaning of those parts. Calling that resemblance a
proof that blockchains cannot be abstracted further would be unjustified.

This is a defensible *semantic pending-request abstraction*, provided the source
step is independently implemented and the packet/state correspondence is
proved. It offers a modest abstraction over the native commitment service, not
a theorem about the original game with communication details hidden. A source
implementation that merely renames every native field and delegates rejection
to the native handler would fail this design objective.

No stronger general erasure is currently justified under the existing scheduler
and observation interfaces. Removing proposal identities, receipts, service
positions, or competing pending requests needs a proof that their observable
distinctions can be represented elsewhere or have no strategic effect. Neither
anonymity of inclusion nor equal terminal game results supplies that proof.
In particular, the discrepancy is not confined to early disclosure: an old
request authored by the player can constrain that player's own later choices.
The existing operational examples do not establish that every one-way SE
translator must retain all this state. Necessity and sufficiency at a more
abstract boundary remain open questions, and should be addressed before adding
this proposed model.

## First positive instance

Use the existing deferred-guard source program. Alice has utility zero; Bob's
nonzero payoff rewards matching Alice's original private type when her secret
publication fails. Alice's prescribed early binding proposal carries evidence
of her initial secret commitment. Bob may notice it while pending. Alice then
binds and discloses the dummy value, and ordinarily discloses her secret even
though its deferred guard rejects publication. Bob's final ordinary disclosure
choice is the guess. No opening is automatic.

For the first service instance, use a finite ambient prelude with Alice's
submission and Bob's passive-observation activation, followed by the existing
recurring owner service with **zero wire steps between an owner response and
its reserved inclusion**. Partial pending observation occurs in the prelude;
this instance does not promise reactions inside the protected visits. Claims,
forwarding, replay, competing proposals, and invalid requests remain legal.
There is no guarantee that every claim is recorded before a later decision.

The zero-wire restriction addresses a concrete obstruction: if an older
conflicting binding packet is included after a fresh corrective response, it
can irrevocably install the old value before reserved inclusion consumes the
fresh packet. Dependencies do not exclude an old request that was already
ready. Removing the intervening wire step excludes that race, but does not
undo bindings completed earlier or restore expired windows. Those facts belong
to the current source service state and must constrain its continuation.

The positive assessment must specify behavior after every earlier own deviation.
Bob uses a posterior-optimal guess when it remains controllable; after an
irreversible earlier guess his payoff is already fixed. The prescribed outcome
gives Bob authenticated knowledge and the intended matching payoff. Proving
that prescription is an SE requires all of the following:

1. **Independent source rules and C:** setup/type preservation; communication
   leaves `G` unchanged; accepted requests and expiry project to the actual
   source steps, including guarded failure.
2. **Complete observations:** candidate evidence, public associations, partial
   pending views, author/broadcaster identity, receipts, and own recall agree
   under the encoding at every legal prefix. Previously received certificates
   acquire named meaning without a new leak draw.
3. **Actual recovery bounds:** every ready uncompleted operation has a timely
   owner visit; sufficiently many proposal names remain after every allowed
   earlier response; a fresh valid response really wins the immediate reserved
   selection. Already completed operations are never treated as recoverable.
4. **All deviations:** every normalized native response has a semantic source
   response, including wrong-type proposals and failed requests. Erase only
   proved private aliases. Translate whole continuation policies at arbitrary
   information sites, not only prescribed service prefixes.
5. **Nonvacuous assessment:** construct one common fully mixed consistency
   sequence and prove Alice's indifference and Bob's continuation optimality at
   every source information site. Earlier Bob messages must be proved harmless
   to a still-available correction, or optimized explicitly. Prescribed-path
   knowledge alone does not establish sequential rationality.
6. **Transfer:** prove exact source-to-normal-native continuation and belief
   correspondence, plus initialized type/result law. Compose with the checked
   normal-menu-to-raw-menu SE theorem. That theorem supplies the final private
   alias step, not this source correspondence.

This instance is a deliberately restricted positive target. Extending it to
wire inclusion between responses requires a new correspondence proof accounting
for competing old requests; it is not justified by padding the schedule or by
asserting a corrective opportunity.
