# What the ideal commitment runtime permits

## Main finding

The runtime attaches some capabilities to **player identity**, whereas ordinary
cryptographic operations depend on **possession of material**. It supports
recommitting a learned value and forwarding a previously received certificate.
It does not represent a player using someone else's complete opening witness
or signing key acquired through communication or correlated initial knowledge.
Calling the response menu "full" means full for this ideal interface; it does
not establish that the interface includes every feasible cryptographic action.

The missing refinement obligation is closure under the operations enabled by
the material a player actually possesses, regardless of its origin. This is
broader than copying unknown commitments or malleability. Non-malleability
does not stop a player who receives a valid opening witness from using the
opening algorithm, or a player who receives a signing key from using the
signing algorithm. No concrete cryptographic refinement currently connects
these possession-based capabilities to the ideal runtime.

This identifies a modeling boundary, not a contradiction in the checked
theorems. The generic game-theoretic results remain valid. An initialized
unilateral-deviation theorem may protect the fresh secrets of prescribed
opponents; sequential rationality also concerns legal continuations after
off-path sharing. Those are different proof obligations, detailed below.

Three checks are separate: who authored an envelope, whether its application
call is accepted, and whether carried evidence authenticates a hidden value.
An authored envelope can contain false claims and a rejected call. Inclusion
still records its payload and receipt.

## Capability inventory

Both Vegas applications use the candidate catalog in
[CommitmentCandidates.lean](../Interaction/CommitmentCandidates.lean).
A handle is an owner/slot pair. Its meaning is fresh, openable to one raw value,
or permanently unopenable. The operational owner restrictions come from the
Vegas adapters, not from an unforgeable Lean constructor for handles.

| Attempt | Actual capability and boundary |
| --- | --- |
| Invent a handle, including a foreign or not-yet-created handle | Permitted in payload syntax. The finite raw menu includes every handle within its declared bounds, independently of possession. Sender-owned fresh commitments without supplied opening material become permanently unopenable; foreign references neither allocate nor freeze the foreign catalog. |
| Submit an invalid, mistyped, premature, or competing commitment | Permitted. Some invalid candidates are accepted as failed bindings; malformed calls and calls failing authorization/readiness are rejected. Failure is not equivalent to being unable to send the packet. |
| Recommit a known or leaked value as oneself | Permitted by supplying the value for a fresh own handle. Its value can depend on the entire legal observation and private input. This covers value correlations, but does not give a private input any cryptographic capability merely because its encoding is intended to denote a witness or key. |
| Authenticate a foreign opening from its plaintext value alone | A foreign owner request cannot create evidence, even when the value is correct. Plaintext alone need not supply the decommitment randomness in a concrete scheme, so learning a value and learning a complete witness must remain distinct. |
| Authenticate a foreign opening using its complete valid witness | No witness-possession operation exists. The foreign owner request is still rejected; the sender can only forward evidence from an already known packet. The same gap applies when the complete witness was initially correlated with the sender's private input. |
| Use an already received authentic certificate | Permitted by forwarding its known message identifier. The certificate can accompany an unrelated or rejected application call. This transferability begins with modeled packet possession, not arbitrary prior possession of equivalent raw material. |
| Sign as Alice after Alice shares her signing key | Not represented. Bob's fresh response always has Bob as authenticated author. There is no signing-key input, credential store, or distinction between the strategic actor and the account whose signature authenticates the message. |
| Copy another player's handle into one's own binding call | Transmittable, but rejected: the accepted binding's event owner, authenticated sender, and handle owner must agree. Changing the owner component denotes a different candidate; it does not copy the original meaning. |
| Replay another player's observed envelope | Permitted without changing its author or payload. Replay does not make its commitment belong to the broadcaster. Newly copying its call into one's own submission gives a new authored envelope. |
| Commit to a related unknown value by transforming opaque commitment material | Absent. There is no operation on commitment bytes, relation constructor, or transfer of an existing hidden meaning to another candidate. A newly openable own candidate receives an explicit raw value. |
| Fabricate claims or malformed application messages | Permitted within the modeled alphabet, including false evidence requests whose calls still transmit. A false request does not fabricate a valid certificate. Raw byte strings outside the declared alphabet are not the packet carrier. |

The key declarations are:

- [EventApplication.lean](../Vegas/Pending/EventApplication.lean):
  `Payload`, `Vegas.EventGraphRuntime.privateStep`,
  `Vegas.EventGraphRuntime.submitStep`, `handle`,
  `submitStep_lookup_other`, and `submitStep_commitment_fixed`.
- [EventPlayerAction.lean](../Vegas/Pending/EventPlayerAction.lean):
  `Submission.register` and `takeAction_commitment_fixed`. Registration supplies
  a value only for a sender-owned prepared handle. The command-policy runtime
  instead exposes the corresponding private preparation operation.
- [ReactiveRuntime.lean](../Vegas/Pending/ReactiveRuntime.lean):
  `reactiveApplication` composes registration, freezing, and packet emission in
  one response; `reactiveBinding_result` checks successful and failed creation.
- [ReactiveFiniteResponses.lean](../Vegas/Pending/ReactiveFiniteResponses.lean):
  `MessageBounds.packets`, `MessageBounds.calls`, `MessageBounds.submissions`,
  and `MessageBounds.rawMenu` enumerate the bounded response domain.

Catalog immutability is stronger than a value merely being mathematically
determined by commitment bytes. In particular,
`CommitmentCandidates.lookup_prepare_freeze_of_fresh` proves that later learning
an opening cannot revive an own handle submitted without opening material.
The model therefore also excludes some commitments to values unknown to their
current author, rather than merely excluding equivocation.

## Witness possession, certificate issuance, and authentication

[OpeningEvidence.lean](../Vegas/Pending/OpeningEvidence.lean) makes the distinction
exact. `WitnessedSubmission.emit` can issue a certificate from a true fact only
when the fact's handle owner is the acting player, or copy a certificate from
an already known packet. `WitnessedSubmission.emit_foreign` applies even when
the foreign fact is true. `WitnessedSubmission.emit_origin` characterizes these
two origins. The menu accepts a foreign evidence request; emission strips its
certificate while preserving the call.

There is no separate decommitment-witness type. `Raw` carries a typed value,
and the candidate catalog privately decides verification. Thus this ideal
interface avoids turning guessed foreign values into a verification oracle,
but also has no rule saying that possession of a complete valid witness enables
public verification. Encoding such a witness in a private input would not
change the ownership check. `MessageNetwork.known` consists of own outputs,
learned network packets, and the ledger; `Execution.initial` starts with an
empty network and does not install a separate private evidence endowment.

Consequently the following cases must not be identified:

1. Bob knows Alice's plaintext value but lacks her decommitment witness.
2. Bob possesses that complete witness, whether initially or through a leak.
3. Bob has received a modeled certificate in a network packet.

Case 3 is represented. The model distinguishes case 1 from evidence, but does
not supply case 2's independent capability. Publicly verifiable commitments
normally permit anyone holding the complete witness to demonstrate the
opening. The contract may still require Alice's signature to accept a game
move; that authorization rule does not prevent Bob from demonstrating the
same fact to another player outside the contract.

The raw [MessagePool.lean](../Interaction/MessagePool.lean) record gives sender
labels no cryptographic meaning. The actual command-policy interface derives
fresh sender labels from the invoked principal; the reachable `Authorship`
invariant in
[MessageApplicationAuthorship.lean](../Interaction/MessageApplicationAuthorship.lean)
connects retained envelopes to that principal's submitted payload history.
The reactive counterparts are `MessageNetwork.submit`, `MessageNetwork.replay`
in [MessageNetwork.lean](../Interaction/MessageNetwork.lean), and
`Execution.respond` in
[ReactiveApplication.lean](../Interaction/ReactiveApplication.lean). Replays
preserve the original author and record the current broadcaster separately.

Fresh submission still identifies the strategic actor with the authenticated
author. After receiving Alice's secret signing key, Bob cannot create an
Alice-authored envelope in this interface. Ordinary signing instead takes the
key as an input: possession enables its use. This follows directly from the
signing and verification algorithms, for example
[RFC 8032, Sections 5.1.6–5.1.7](https://www.rfc-editor.org/rfc/rfc8032.html#section-5.1.6).
Using a deliberately shared key does not break the signature scheme. A concrete
refinement must distinguish authenticated account identity from strategic
control, or justify a restriction on key possession for the theorem being
proved. Authentication alone supplies neither justification.

There is also a packet-verification boundary. An arbitrary reactive opening
call can request no certificate even when its raw value is correct. The
pending packet then carries a value claim without modeled opening evidence;
its envelope still has an authenticated author. A successful inclusion receipt
supplies evidence through
[ReactiveOpeningEvidence.lean](../Vegas/Pending/ReactiveOpeningEvidence.lean).
The prescribed `disclosureSubmission` attaches evidence to emitted openings.
A concrete opening packet may already contain publicly checkable witness
material before inclusion; its interpretation must account for that ability.

These are ideal-oracle limits, not claims that information sharing defeats all
cryptography. Plaintext, randomness, complete witnesses, signing keys, and
issued certificates enable different operations. Nor does every correlation
reveal a secret: the relevant question is what the particular correlated
information lets the recipient compute or verify.

## Related commitments without knowing the opening

Consider an untagged concrete backend that accepts the same commitment string
under Alice's and Bob's transaction identities. Alice commits a hidden bit;
Bob copies that string before Alice opens. After Alice publishes the opening,
Bob uses the same opening for his accepted commitment. Neither hiding nor
binding has been violated: Bob learned the bit only at opening, and both copies
have the same fixed value. Authenticated transactions do not prevent this.

**Illustration, not a checked Vegas theorem:** in hidden matching pennies,
pay Bob 1 for matching Alice and -1 otherwise, with opposite Alice payoffs.
Require both commitments before opening and let a prescribed, uniformly
randomizing Alice open first. Independent guessing gives Bob expectation zero;
copying Alice's commitment and then reusing her opening gives Bob 1 whenever
the backend accepts both copies. This can threaten initialized Nash/security
preservation already, before any sequential-equilibrium question arises.

The current representation excludes exactly this operation. A Bob-authored
call containing Alice's handle fails `handle`'s ownership check. Relabeling it
to Bob addresses a fresh, different catalog entry, which
`Vegas.EventGraphRuntime.submitStep` freezes
as unopenable when Bob supplies no value. A later Alice opening cannot change
that entry. These are operational facts about the ideal runtime, not a proof
that a byte-level commitment implementation prevents copying.

Resistance to creating related hidden commitments is the subject of
non-malleable commitments, a stronger requirement than ordinary commitment
security. The distinction and commitment applications originate in
[Dolev, Dwork, and Naor](https://epubs.siam.org/doi/10.1137/S0097539795291562);
[Lin and Pass](https://eprint.iacr.org/2010/483.pdf) explicitly discuss relating
unknown committed values and identities of concurrent commitment interactions.
Tag-based definitions distinguish the tags of the honest and adversarial
commitments; see Section 2 of
[Bitansky and Lin](https://eprint.iacr.org/2018/613.pdf).

A backend must prove the particular relation-resistance property its strategic
simulation needs. Binding the player, event/session, and protocol context into
commitment verification is a candidate defense against literal copying; mere
labels outside verification do not supply it. A full non-malleability or
knowledge/extraction argument may require additional assumptions. No specific
construction, sufficient cryptographic assumption, or necessity theorem is
established here.

Preventing unknown-value relations does not solve the witness-possession or
shared-key cases above: there the recipient has the actual material required
by the intended operation.

## Compiled opponents and arbitrary native continuations

For an initialized unilateral-deviation theorem, the other players follow
their prescribed compiled policies. A concrete compiler might sample fresh
independent opening randomness and signing keys and keep those secrets private.
That could justify protecting their credentials against the one deviator under
an appropriate computational assumption, even though the general runtime
allows a player to share its own credentials. The initialization law, secrecy
invariant, simulation, and allowed adversary must be stated and proved; none
is supplied by an owner label. The copy-unknown attack also shows that secret
protection alone need not establish the required simulation.

Sequential equilibrium demands optimality at every relevant native information
set with beliefs justified by one common perturbation sequence. If sharing a
witness or key is a feasible native action, off-path histories and trembles can
make its recipient more capable even when the prescribed execution never
shares it. Initially correlated credential possession, when allowed by the
initial law, has the same consequence without a prior message. A proof cannot
continue to deny those operations solely because the recipient has a different
player label. It must account for possession or prove a suitable refinement
that accounts for its strategic effects.

These observations leave both possibilities open: stronger compiler invariants
may suffice for a particular initialized Nash theorem, and a richer capability
model may admit sequential results under an appropriate service contract.
Neither follows from the present ideal-interface proofs alone.

## Which results depend on these choices?

| Result | Dependence on commitment capabilities |
| --- | --- |
| Generic zero-sum security/value theorems and finite L1 saddle existence | None: they concern the given game form and utility. Changing the target can change whether the required native Nash profile exists. |
| The paper's source-to-pending Nash certificate and its zero-sum value corollary | They quantify over the ideal policy menu. Catalog opacity, immutable meanings, principal-based authorization, and excluded unknown cross-owner recommitments are part of that target. A concrete initialized refinement may exploit secrecy of prescribed opponents, but is unproved. The existing theorems are not invalidated internally by this missing bridge. |
| The proposed zero-sum NE-to-SE repair theorem | A theorem about a fixed finite perfect-recall game, independent of commitments. It cannot repair a failed source-to-native Nash/security edge caused by copying or malleability. |
| The checked selective-disclosure SE separations | Their attack uses the owner's ordinary ability to reveal authentic evidence, not forging another owner's handle. Their universal claim nevertheless depends on the complete modeled menus and information fibers, including certificate soundness and origin; it has not been transported to arbitrary added cryptographic operations. |
| The checked no-leak native SE | It admits the full bounded raw response menu, including malformed calls, known replay and evidence forwarding. Its evidence-origin argument uses the ideal issuer and empty passive observation. Correlated initial witness possession, shared signing keys, or additional public verification are not silently covered by that quantifier. |

For the exact native comparison, see
[SelectiveAssociationRestrictedSeparation.lean](../VegasTests/SelectiveAssociationRestrictedSeparation.lean)
and [ReactiveEvidenceOrigin.lean](../Vegas/Pending/ReactiveEvidenceOrigin.lean).
The conceptual disclosure problem remains whenever a player can transfer a
verifiable opening. Its current numerical payoff separation is a checked
result for the specified ideal game; impossibility claims are not automatically
monotone when strategies and information are enlarged.

In particular, `foreign_certificate_published` in
[ReactiveEvidenceOrigin.lean](../Vegas/Pending/ReactiveEvidenceOrigin.lean)
derives ledger visibility of foreign certificates under empty passive
observation from the issuer/forwarding interface. It is not a theorem that a
foreign witness can only become known by appearing in the ledger. Changing
the initial endowments or derivable capabilities requires revisiting its use
in the no-leak proof.

The next runtime theorem must state its ideal functionality and quantifiers
explicitly. A future cryptographic bridge must account for malformed bytes,
strategic control of authenticated accounts, shared or correlated secret
material, context binding, unknown-value correlations, opening verification,
and concurrent observations. The audit changes no runtime semantics. Further
cryptographic mechanisms and computational-equilibrium questions remain in
[cryptographic-runtime-future-work.md](cryptographic-runtime-future-work.md).

The design consequence is to audit preservation against the capabilities
players gain from communication, correlation, and shared control. A theorem
simulating one deviator against prescribed opponents does not automatically
simulate joint deviations or preserve laws conditional on off-path information.
Each stronger strategic claim must identify the capabilities and joint laws it
actually quantifies over; this audit introduces no additional runtime layer.
