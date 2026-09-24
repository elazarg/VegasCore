# Communication and evidence around a source game

## Design objective

Keep the game program about binding choices, publication, guards, and results.
Give strategic analysis an explicit account of the communication and evidence
available to its players. Implement that account once per service, rather than
requiring a program to describe packets, inclusion, or cryptographic encodings.

An ordinary commitment has two distinct consequences: it binds a choice and it
gives its owner evidence that can be disclosed. Guard rejection can prevent a
value from becoming an accepted game publication. It cannot retract evidence
already delivered to another player.

The implementation therefore keeps `PublicationResult` unchanged. An
authenticated rejected opening supplies an observation alongside a failed
publication. A `failure(value)` constructor is unnecessary for representing
that observation. Whether the game itself should inspect such a value is a
separate language feature; equilibrium analysis does not require it to do so.

## The programmer-facing abstraction

There are three inputs to strategic analysis:

1. **Game rules:** the existing source program and setup distribution.
2. **Communication service:** opportunities to communicate, delivery audiences,
   and the evidence supplied by the chosen commitment service.
3. **Assessment:** players' strategies and beliefs, including responses after
   unexpected communication.

The commitment interface supplies the evidence capability. It is not an
instruction that the programmer inserts between statements. Strategies can
refer to source facts such as "Alice's commitment named `bid` binds 7". They do
not inspect commitment handles or transaction receipts.

A useful diagnostic should identify the fact and decision whose incentives
conflict, for example: "Bob's continuation assumes Alice's bid is unknown,
but Alice can disclose evidence of that bid before Bob chooses." Producing
such diagnostics automatically remains an analysis task, not a checked
decision procedure in this implementation.

## Claims, certificates, and game results

| Object | Meaning | Effect on the game state |
|---|---|---|
| Claim | A message the sender is free to make, including a false one | None |
| Certificate | Transferable evidence of a particular immutable binding | None |
| Game action | An action admitted by the existing source game | Existing source transition |
| Opening observation | A certificate emitted by a disclosure action | None in addition to that action |

The distinction between claims and certificates is semantic. The abstract
service admits a certificate only if its sender possesses it or previously
received it. This is an ideal evidence assumption; a cryptographic realization
needs computational unforgeability and an appropriate equilibrium definition.
The interface does not claim that raw strings become impossible to transmit.
An attempted forgery must be represented as a claim or other uncertified
observation by a concrete correspondence proof.

The Vegas instance certifies successful commitment bindings. An unopenable
binding provides no opening certificate. A private initial input supplies no
certificate merely by being a private input. Explicit correlations in setup
can allow a commitment certificate to establish a private input indirectly,
as in the checked disclosure counterexample.

Certificates remain available after resolution. A receiver may forward them.
No possession restriction turns an unsupported claim into a certificate.
Public and private delivery are distinct: a private recipient can learn a
fact without its becoming a public game result or a public announcement.

## Concrete semantic service used for the experiment

`Interaction.CommunicationInterface` extends an existing information game.
Its parameters include a claim alphabet and a public finite roster of players.
Before each underlying game transition, each roster entry supplies one optional
communication opportunity. A player can remain silent, make a claim, or send
possessed evidence to one recipient or to everyone. Delivery is immediate at
that semantic opportunity. Repeated roster entries allow multiple exchanges.
Terminal game states stop the execution.

The service has these explicit restrictions:

- Communication is bounded and synchronous. The roster is common knowledge.
- Opportunities occur before each underlying transition, including setup and
  chance transitions; nobody has setup evidence before setup occurs.
- The phase and opportunity position are observable. Private message contents
  and recipient choices are observed only by the sender and recipient.
- Everyone remembers the observations and own actions available at each public
  round. There are no strategic scratch-memory writes or local computation
  costs.
- Finite-horizon sequential analysis additionally requires finite legal menus.
  A finite roster alone does not make an infinite claim alphabet finite.

This is a concrete experiment with an explicit communication service. It is
not a claim that the existing pending-message runtime supplies synchronous
private delivery, nor that real timeouts bound all off-chain communication.
Different delivery or opportunity services need their own game interpretation
and correspondence proof. Allowing more communication is not assumed to make
sequential-equilibrium preservation easier or conservative.

## Checked separation properties

The implementation proves:

- Every admitted certificate is true throughout every legal communication
  history, including after arbitrary forwarding and deviations.
- A received certificate is true at every compatible history in the
  receiver's information set. This conclusion is independent of assessment
  beliefs or equilibrium behavior.
- A fact fixed throughout an information set has a point-mass law under every
  belief on that set.
- Communication leaves the underlying game history unchanged. A game step
  projected onto the underlying state has exactly the original transition law.
- An underlying horizon of `n` and roster length `r` give horizon
  `n * (r + 1)` for the extension. The bound is proved for arbitrary legal play.
- Observation and own-action recall satisfies the library's perfect-recall
  predicate. Decision information sets consequently satisfy its history
  antichain condition.
- The source evidence service is sound for every source program: bindings
  persist through source transitions, and disclosure emits a certificate of
  the binding even if deferred validation rejects its publication.

These are semantic and information guarantees. They do not establish an
equilibrium compiler theorem.

The actual deferred-guard game is instantiated in
[`VegasTests.CommunicationDisclosure`](../VegasTests/CommunicationDisclosure.lean).
Its checked public history retains the original failed publication and exposes
the opening certificate. A second checked history privately discloses the same
certificate before the first source command. The setup correlation then fixes
the original private type at every compatible history: `belief_type` proves
that every belief has the point-mass type law. No `failure(value)` constructor
is used in either history.

| Checked obligation | Module |
|---|---|
| Knowledge and arbitrary-belief consequence | [Knowledge](../GameTheoryExtensions/Protocol/Knowledge.lean) |
| Observation history and perfect recall | [ObservationRecall](../GameTheoryExtensions/Protocol/ObservationRecall.lean) |
| Claims, evidence transfer, selective visibility | [Communication](../Interaction/Communication.lean) |
| Protocol, information-local menus, recall | [CommunicationProtocol](../Interaction/CommunicationProtocol.lean) |
| Legal histories and exact game-step projection | [CommunicationHistory](../Interaction/CommunicationHistory.lean) |
| All-history soundness and knowledge | [CommunicationKnowledge](../Interaction/CommunicationKnowledge.lean) |
| Arbitrary-play horizon and decision antichains | [CommunicationBounded](../Interaction/CommunicationBounded.lean) |
| Source evidence and adapter | [CommitmentEvidence](../Vegas/Source/CommitmentEvidence.lean), [source Communication](../Vegas/Source/Communication.lean) |

## Preservation target and remaining obligations

For a fixed source communication service, the desired theorem starts from an
assessment in the extended source game, including its communication behavior.
It must produce a sequential equilibrium in a corresponding runtime game and
preserve the initialized law of original types and public game results.

The compiler and backend certificate must still establish:

1. Which native observations correspond to claims, certified facts, and public
   announcements, including invalid packets and rejected application calls.
2. Which abstract communication opportunities represent native transmissions
   and passive observations, and with what delivery law and timing.
3. Continuation incentives at every native decision information set, including
   histories reached after multiple deviations.
4. A common consistent belief construction from fully mixed approximations.
5. Finite legal menus, or a separately justified extension of the equilibrium
   machinery, for the admitted communication alphabet.

There is also a concrete compiler obligation. The current reactive policy's
[`reactiveResolutionPacket`](../Vegas/Pending/ReactivePolicy.lean) consults the
publication verdict and substitutes withholding
when validation would fail. That implements the original result-only
interpretation. Under the evidence interpretation, an openable source
disclosure emits a certificate even on rejection; its compiler must implement
that observation as well. The raw target already permits the authenticated
rejected opening used by the checked native witness. This note supplies no
proof that changing the prescribed packet preserves the other compiler laws.

The existing Nash theorem retains its stated target and service assumptions.
It is not automatically a theorem about every communication extension. The
unrestricted sequential-preservation impossibility for the original source
observations also remains valid. The proposed source semantics changes the
information game to address its disclosure mismatch; it does not refute that
theorem.

## Ownership and alternatives

| Layer | Responsibility |
|---|---|
| `GameTheoryExtensions` | Knowledge in information sets, belief consequences, observation recall |
| `Interaction` | Claims and evidence, audiences, communication opportunities, protocol extension |
| `Vegas.Source` | Source commitment facts, possession, persistence, opening observations |
| `Vegas.Pending` and `Vegas.Game` | Native evidence decoding and eventual strategic correspondence |

The design deliberately keeps game results and observations separate. An
alternative that annotates only failed publication results would still need an
account of private or earlier disclosure. An alternative that reproduces the
native message machine as the source semantics would give programmers the
wrong level of abstraction. An alternative that silently makes all private
values public would remove information structures the language is meant to
describe.

Communication extensions of games are standard; their timing and equilibrium
guarantees require explicit analysis. See Geffner and Halpern,
[Communication games, sequential equilibrium, and mediators, Section 2.2](https://arxiv.org/html/2309.14618v3).
That paper is background, not a proof of the service correspondence proposed
here. Cryptographic services that change possession or disclosure capabilities
are discussed in [cryptographic future work](cryptographic-runtime-future-work.md).
