# Cryptographic services for game-oriented source semantics

## Scope and decision

Advanced cryptography is **future work**. The current commitment runtime and
sequential-equilibrium investigation use exact idealized semantics. This note
records which stronger services could support simpler source games, the
assumptions they would require, and the obligations a future compiler would
have to prove. It introduces no source syntax, implementation, or new
equilibrium definition. None of the cryptographic constructions below is
formalized in VegasCore.

The intended direction is to specify the strategic service a game needs and
prove that a backend provides it. A game author should not have to program a
proof system, a decryption committee, or transaction recovery. The author must
still see a limitation when it changes the available moves, observations,
termination guarantees, or incentives. These are distinct properties; a single
"secure commitment" option would obscure the distinctions.

## The disclosure issue that motivates this work

The [sequential-equilibrium investigation](sequential-equilibrium-design.md)
includes a program in which Alice's initial commitment is bound to her private
type. Alice can publish a correct opening, the native handler authenticates it,
and a deferred game guard nevertheless records publication failure. The source
observation reports failure without the value. The native observation contains
the authenticated value. An opponent may therefore have different optimal
continuations. The linked investigation owns the proof status; this note makes
no additional native preservation or impossibility claim.

There are three different promises a cryptographic service might provide:

1. **Validity:** every accepted commitment denotes an admissible value.
2. **Recovery:** the value can become available without further help from its owner.
3. **Controlled disclosure:** validation reveals only the information specified
   by the game, including when validation rejects.

Obtaining one does not supply the other two. In particular, forced recovery
addresses withholding, whereas the witness above involves additional disclosure.

### A boundary that stronger cryptography does not remove

The following is an elementary operational argument, rather than a new
cryptographic impossibility theorem. Suppose:

- Alice knows an opening `(value, randomness)` for a public commitment;
- anyone can authenticate it with the public verification algorithm; and
- Alice can send its encoding to Bob before his relevant decision.

Alice can send that pair, and Bob can run the verifier. This uses the intended
opening algorithm and needs no cryptographic attack. Rejecting the message as a
game move does not make Bob forget the message. Thus no replacement for the
commitment's hiding assumption alone removes this behavior while retaining
these three premises.

An application timestamp check changes when a call can be accepted. It does
not prevent copies of its plaintext argument from reaching another player.
An alternative backend can change a premise: keep opening material outside
Alice's control, avoid publicly transferable authentication, or close a
communication channel. Each alternative needs an explicit model and proof.
Knowing a private value and being able to authenticate it publicly are different
capabilities. A mere unverified claim need not have the strategic effect of an
authenticated opening. A service which keeps a secret unknown even to Alice
also changes the original game when Alice was meant to know that secret.

## Candidate services

The table gives our assessment for VegasCore. The sections below provide the
supporting constructions and their limitations.

| Service | What it could simplify in the source | Remaining obligation or cost |
|---|---|---|
| Commitment with a zero-knowledge validity proof | Only valid values can be accepted into the game | Prove the right predicate against the right commitment; malformed submissions and silence remain possible |
| Verifiably recoverable commitment | Opening after acceptance need not depend on the owner | Recovery availability, latency, who learns the value, and proof that recovery yields the same value |
| Timed commitment based on sequential computation | Recovery can avoid a permanently trusted decryption party | Sequential-work assumptions, hardware advantage, start time, solver work, and result delivery |
| Threshold release or a time beacon | A committee can release after a specified condition or time | Privacy threshold, availability threshold, key generation, clock or finality assumptions, and delivery |
| Private validation with zero knowledge or secure computation | An honest execution can reject without publishing the witness | Public predicate results still leak; aborts and voluntary disclosures need separate treatment |
| Penalties for abort or disclosure | Some deviations may be unattractive for specified utilities | Detectability, enforceable collateral, utility bounds, and continuation incentives |

### 1. Require a proof that an accepted value is valid

A commitment can be accompanied by a zero-knowledge proof of an opening
satisfying a relation. For example, Bulletproofs provides proofs for ranges of
committed values and arithmetic circuits without a trusted setup; its short
proofs do not imply constant verification work. This is a concrete starting
point for bounded bids or other refinement predicates.
[Bünz et al., *Bulletproofs*](https://eprint.iacr.org/2017/1066.pdf).

A candidate acceptance relation is:

```text
there exist value and randomness such that
  commitment = Commit(value, randomness)
  and Valid(value, public_context).
```

This is a proposed interface, not an implemented definition. The proof must
refer to the exact stored commitment and context. Cryptographic soundness would
justify the validity of accepted commitments, up to its stated error against
the allowed adversaries. A proof of knowledge can additionally support an
extraction argument; it does not guarantee that the owner retains the opening
or ever submits it. Neither property establishes truthfulness about an
unverifiable private type.

Admission soundness also differs from privacy of adversarially chosen messages.
A player can deliberately encode information in its chosen value, randomness,
proof bytes, or submission time whenever those choices support an observable
distinction. A future information-preservation proof must account for those
channels. An honest prover's zero-knowledge guarantee alone does not exclude
them.

Deferred guards require care. A predicate on a known public context can be
checked at commitment. A predicate on future choices cannot generally be
certified as true before those choices are fixed. Once all dependencies are
bound, a proof can relate several commitments, but its prover must have the
required witnesses or use a distributed protocol. Rejecting a commitment
upfront because its eventual guard cannot hold changes the current deferred
semantics; it is a language design decision, not a transparent optimization.

**Effect on the disclosure witness:** ordinary Boolean validity already holds
there. Proving it does not hide a later valid opening. Moving the deferred
condition into admission could exclude that execution only by changing which
source plays are admitted.

### 2. Make an accepted commitment recoverable

Verifiable encryption couples encryption with proofs about the encrypted
data. Camenisch and Shoup give constructions for verifiable encryption and
decryption of discrete logarithms, with applications including key escrow and
fair exchange. This supplies a model for proving that an encrypted recovery
payload agrees with a public commitment.
[Camenisch and Shoup, *Practical Verifiable Encryption and Decryption of Discrete
Logarithms*](https://eprint.iacr.org/2002/161).

For a game backend, acceptance would need evidence that the recovery ciphertext
contains the same valid value as the commitment. Merely posting ciphertext
bytes is insufficient. Recovery should yield a verifiable result, and its
decryption authority must be specified: one trusted service, a threshold of
services, or a timed construction. After an accepted submission, the owner
could cease participating without retaining a veto over the result, provided
the recovery service and delivery assumptions hold.

This does not force a player to join or submit an acceptable commitment in the
first place. It also does not specify whether recovery reveals the raw value
to everyone or supplies it privately to a computation. Recovering every raw
value publicly can increase the mismatch with a source that hides rejected
values.

### 3. Timed commitments and time-lock computation

Boneh and Naor's timed commitments explicitly include forced opening without
the committer, together with verification during commitment that recovery will
work. Their privacy bound is against receivers with bounded parallel running
time, while the forced-opening algorithm has its own upper time bound. Their
construction relies on a sequentiality assumption; the primitive also permits
the committer to open normally.
[Boneh and Naor, *Timed Commitments*, Section 2](https://www.iacr.org/archive/crypto2000/18800237/18800237.pdf).

For VegasCore this suggests an automatic-resolution service after acceptance.
Its contract must connect computational work to the game's clock. Sequential
steps alone do not establish a wall-clock or block-height deadline: hardware
speed, when computation can start, available honest solvers, and inclusion of
their result all matter. Someone must perform and finance recovery work. These
are service assumptions and engineering obligations; VegasCore currently
models none of them as cryptographic guarantees.

A verifiable delay function makes a delayed computation's output efficiently
checkable. It does not by itself define a valid encrypted message or a complete
commitment protocol.
[Boneh et al., *Verifiable Delay Functions*](https://theory.stanford.edu/~dabo/abstracts/VDF.html).
Possible construction research includes
[Ambrona et al., *Timed Commitments Revisited*](https://eprint.iacr.org/2023/977),
which presents alternative definitions and constructions. Comparing them for
a backend is deferred.

**Effect on the disclosure witness:** timed recovery removes an owner's later
veto if its assumptions hold. It leaves voluntary early opening by an owner
who knows the opening available. Recoverability and earliest authorized
disclosure are separate promises.

### 4. Threshold release and a time beacon

The `tlock` construction combines identity-based encryption with threshold BLS
signatures. A future beacon round identifies the encryption target; publication
of that round's signature supplies the decryption material. It has an
implementation using drand, so this is a concrete candidate for externally
scheduled release rather than only a theoretical possibility.
[Gailly et al., *tlock: Practical Timelock Encryption from Threshold BLS*](https://eprint.iacr.org/2023/189).

The documented trust boundary includes a threshold coalition's ability to
produce future signatures and decrypt early. The complementary availability
obligation is that sufficient participants actually produce the scheduled
signature and that users can obtain it. Mapping beacon time to game deadlines
and obtaining a timely ledger transition are additional backend obligations.
[drand, *Timelock Encryption*](https://docs.drand.love/docs/timelock-encryption/).

A game-specific decryption committee could instead release after an agreed
ledger event. The proposed interface would distinguish the threshold needed
to compromise confidentiality from the participation needed for availability,
and state which event/finality evidence authorizes release. It would also need
proofs that admitted ciphertexts encrypt valid committed values. We have not
selected or analyzed such a protocol.

**Effect on the disclosure witness:** threshold release does not stop an
encryptor publishing plaintext and encryption randomness that it retained.
It also does not implement permanent secrecy of rejected values when its
release rule makes every ciphertext publicly decryptable. Private evaluation
before selective output requires an additional protocol.

### 5. Validate privately and publish only the prescribed result

One possible source service takes committed inputs and publishes
`Accept(value)` or `Reject`, revealing the value only in the accepted branch.
A prover who knows the inputs could prove the appropriate branch in zero
knowledge. When the witnesses belong to different players, secure multiparty
computation (MPC) is a candidate for computing that result jointly. Both are
future designs requiring a full specification of output and abort behavior.

Hawk is a close language/compiler precedent: programmers write private smart
contracts and a compiler generates cryptographic protocols. Its practical
construction uses a manager entrusted with privacy of the inputs it receives;
proofs constrain correctness. This demonstrates a useful separation of
programming abstraction and explicit backend trust, without supplying our
sequential-equilibrium theorem.
[Kosba et al., *Hawk*, Sections I and IV](https://faculty.washington.edu/zkwen/articles/kosba16hawk.pdf).

For MPC, confidentiality, correctness, fairness, and guaranteed output delivery
need separate guarantees. Fairness means that if corrupted parties receive
output, honest parties do too. Guaranteed output delivery additionally prevents
corrupted parties from blocking honest output. These guarantees are distinct
in general multiparty settings, and arbitrary functionalities cannot always
provide them without an honest majority. A choice of MPC must state its actual
network and corruption assumptions.
[Cohen and Lindell, *Fairness versus Guaranteed Output Delivery in Secure
Multiparty Computation*](https://eprint.iacr.org/2014/668).

Fully homomorphic encryption supports computation on encrypted inputs; a
complete game service must additionally arrange valid inputs, correct
evaluation, authorized output decryption, and availability. Encryption alone
does not supply those obligations.
[Gentry, *A Fully Homomorphic Encryption Scheme*](https://crypto.stanford.edu/craig/craig-thesis.pdf).

Trusted execution environments offer another private-evaluation route. Ekiden
studies this integration with blockchains and explicitly treats hostile
scheduling, rollback, key management, and compromised hardware. A proposed
TEE backend would need a hardware/attestation trust model and an availability
argument; private execution alone does not ensure that its host returns output.
[Cheng et al., *Ekiden*, Sections II-III](https://arxiv.org/pdf/1804.05141).

**Effect on the disclosure witness:** these tools can remove the protocol's
need to publish a rejected witness. That is a useful improvement. They do not
establish that a deviating owner cannot publish independently verifiable
opening material through an available channel. A simulation argument must
represent that deviation and its subsequent observations, or explain precisely
which premise of the disclosure argument the service changes. Privacy
guarantees for honestly supplied inputs are insufficient for this purpose.

### 6. Economic enforcement and deposits

Penalties can compensate for aborts or discourage them under explicit utility
assumptions. Bentov and Kumaresan formalize secure computation where aborting
after obtaining output incurs a predefined monetary penalty, using an abstract
payment functionality realized with Bitcoin.
[Bentov and Kumaresan, *How to Use Bitcoin to Design Fair Protocols*](https://www.iacr.org/archive/crypto2014/86160326/86160326.pdf).

For VegasCore, a penalty should appear in the game's outcomes and utilities.
It cannot justify deleting a legal deviation for all utilities: a player whose
benefit exceeds the penalty may still choose it. Sequential analysis must also
check the continuation after a breach, including a breach that occurs only off
the prescribed path. An enforceable penalty for disclosure additionally needs
observable evidence and an adjudication rule. Punishing disclosure does not
erase an opponent's knowledge once disclosure happened.

The [enforcement investigation](disclosure-enforcement-design.md) separates
an abstract penalty's incentive effect from its realization by observations,
accountable reports and escrow. It also considers punishing deviations from
the compiled communication protocol, while retaining legal source choices.
The checked shared-randomness experiment shows why permitting the correct
public message distribution does not alone exclude signaling to a recipient
with additional private information. The native observation experiment shows
why ledger access does not alone supply a monitor of pending certificates.
Neither experiment assumes a private communication channel outside the model.

## Cryptography and the equilibrium definition

A cryptographic backend needs an explicit computational security parameter,
allowed adversaries, and error notion. Ordinary exact information sets and
unrestricted deviations cannot simply be reused while informally describing
encryption as opaque. Conversely, computational restrictions do not imply that
we must charge players a utility cost for every local computation.

Halpern, Pass, and Seeman define computational extensive-form games and a
computational sequential-equilibrium notion using computationally consistent
partitions, polynomial-time deviations, negligible error, and completely mixed
approximations. Their representation hypotheses yield an equilibrium
preservation theorem. Their theorem is a relevant starting point; it does not
automatically cover our additional network activations and service semantics.
[Halpern, Pass, and Seeman, *Computational Extensive-Form Games*, Definitions
3.4 and 4.4, Theorem 4.5](https://www.cs.cornell.edu/home/halpern/papers/kuhn.pdf).

The recorded question about a possible "pseudo sequential equilibrium" is
therefore meaningful future work. That phrase remains a working question, not
a selected definition. The investigation should specify:

- how indistinguishability of observations replaces exact information;
- which deviations, auxiliary information, and correlations are admitted;
- how the security parameter and the limit of fully mixed perturbations interact;
- which conditional continuation events require optimality, particularly when
  their probabilities are negligible;
- what utility bounds make a negligible cryptographic error strategically small;
- how composition with other games and communication channels is handled.

Conditioning is a concrete concern. Two distributions can disagree only on an
event of probability `epsilon` yet disagree completely after conditioning on
that event: put the entire discrepancy inside the event. Thus an unconditional
small-error statement alone does not establish a conditional small-error
statement. A computational continuation theorem must supply the missing
probability or conditioning hypotheses.

The exact native disclosure obstruction must be rechecked against any selected
computational definition. An accepted opening is efficiently readable, but a
definition may impose different obligations at histories reached only through
negligible perturbations. It would be inaccurate either to call the exact
disclosure argument a computational impossibility theorem, or to claim that changing
equilibrium definitions cryptographically conceals the revealed value.

### Can verification costs justify ignoring disclosures?

A further research question is whether a player can rationally ignore
unsolicited opening claims because checking them costs more than the useful
information they provide. This could support a game-specific abstraction even
when disclosure remains physically possible. It is a proposed research route,
not a preservation result or a premise of the current ideal semantics.

Computational feasibility and economic cost are separate assumptions. A
polynomial-time restriction alone does not charge a utility cost for running an
allowed verifier. Halpern and Pass study explicit computation costs, including
sequential choice with costs and the possibility of rational forgetting.
[Halpern and Pass, *Algorithmic Rationality: Game Theory with Costly
Computation*](https://arxiv.org/abs/1412.2993),
[Halpern and Pass, *Sequential Equilibrium in Computational
Games*](https://arxiv.org/abs/1412.6361).

The investigation should distinguish verifying one bounded, relevant opening
from processing an adversarial stream of purported openings. A recipient can
limit the messages it processes; distrust of a sender alone does not establish
that checking a selected message is unprofitable. The sender can have incentives
to disclose truthfully, and the recipient's stakes can justify the check.
An argument that ignoring evidence is dominant would need to compare against
every allowed opponent strategy. An equilibrium-specific argument can use the
specified strategies and beliefs, but sequential preservation must also cover
the required continuations after unexpected messages.

Any such abstraction must state its utility scale. A fixed verification cost
cannot justify ignoring useful evidence uniformly over arbitrarily large
stakes. The research target should therefore specify bounded utilities or a
particular class of games, rather than assuming costs restore the current
utility-independent preservation claim.

A candidate approximate-preservation theorem would bound the improvement
available from extra communication after accounting for processing costs.
Its premises must cover selective checking, bounded processing, outsourcing
or shared verification where available, and information conveyed without
verification, including claims and timing. Utility bounds, cost accounting,
and the treatment of rare continuation events belong in its statement.
Neither this cost argument nor an appropriate computational equilibrium
definition has been selected or formalized. Private computation remains free
in the present implementation.

## Requirements for a future service interface

The following is a design checklist, not a proposed collection of syntax flags.
Before simplifying a source action, its backend certificate should state:

1. **Admission and meaning:** which accepted messages bind which typed values,
   the validity relation, and what happens before successful admission.
2. **Knowledge and authentication:** who knows a value or opening, who can
   convince whom of it, and what publicly transferable evidence exists.
3. **Release:** who can initiate it, who can prevent it, who learns what, and
   whether it depends on owner cooperation, computational work, or a service.
4. **Progress:** deadline semantics, thresholds, data availability, recovery
   labor, inclusion assumptions, and behavior if an assumption fails.
5. **Observations after deviations:** rejected inputs, proofs, timing, aborts,
   voluntary disclosure, and extra communication.
6. **Strategic guarantee:** the chosen equilibrium notion, utility class,
   adversary class, and the continuation and consistency simulation obligations.

These obligations have natural project owners. `Interaction` should describe
service operations, observations, communication, and progress. `Vegas` should
specify the corresponding game capabilities and discharge compilation
obligations. Generic computational game and equilibrium definitions belong in
`GameTheoryExtensions` until an independently agreed library design exists.
No change to the `GameTheory` submodule is proposed by this note.

## Deferred work and evaluation order

The smallest plausible cryptographic experiment is a commitment with a proof
of a simple value predicate. A separate experiment should compare a verifiable
timed commitment with threshold recovery, using the same abstract release
interface. Only then should a private guard-evaluation service be considered,
with explicit output and abort semantics.

For each experiment, compare the source-visible benefits against setup trust,
committee participation, proving and verification work, recovery latency,
ledger bandwidth, and availability requirements. A construction's existence
does not establish that its assumptions or costs suit a deployment. This note
selects no cryptographic library and makes no current performance claim.

The present decision is to keep advanced cryptography out of the implementation
and complete the exact strategic analysis first. The source can then expose the
capabilities its present runtime requires while making room for proved stronger
services. A future backend may remove a particular failure or disclosure case
only when its certificate and equilibrium theorem justify doing so.
