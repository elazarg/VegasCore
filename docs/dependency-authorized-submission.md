# Requiring completed dependencies before authoring an executable message

## Status

This is a candidate runtime contract, with a research assessment of possible
blockchain mechanisms. It is not implemented, and no positive SPE theorem
under this contract is claimed. The
[early-opening counterexample](early-opening-and-spe.md) motivates the question.

The distinction is between checking dependencies when a call executes and
requiring evidence that was unavailable when the call was first authored.

## Proposed contract

For every envelope that completes event `e`, all predecessors of `e` must have
completed before that envelope's first authenticated submission. Completion
is monotone in the ideal ledger; reorganizations would require a different
contract or a finality boundary.

Players may still transmit arbitrary packets. A packet authored without the
required authorization remains unusable for completing the event, even after
the dependencies complete. Rebroadcast preserves that fact. Producing a newly
authorized envelope requires another player submission; the network cannot
silently add the missing evidence to an existing envelope.

One possible ideal implementation issues an unforgeable public certificate
when the dependencies complete. An executable packet authenticates the event,
payload, dependency context, and certificate together. A predictable event
number or counter does not establish the required unavailability before
completion. A certificate attached outside the authenticated message would
also leave open the possibility of a relayer completing an early instruction.

The certificate concerns completed predecessor instances in this execution.
A certificate from a different game instance or a different accepted binding
must not authorize this event's packet.

## Effect on the checked witness

The existing witness submits both a withholding packet and an opening before
the commitment event completes. Under the proposed contract neither could
later complete the disclosure event without a new authenticated submission.

The conditional argument is direct: disclosure has commitment as a predecessor.
If the old withholding envelope could complete disclosure, the contract would
imply that commitment had completed before its submission. The witness's
prefix has no completed commitment, contradicting monotone completion. The
same reasoning excludes the early opening from later successful execution.

Thus this exact witness would be excluded by the proposed contract. This is
an argument from a proposed assumption, not an additional checked Lean result
or a proof of SPE preservation.

## Blockchain mechanisms

### Execution timing is weaker

An application check of the current block height, timestamp, or completed
dependencies restricts execution. A transaction can contain such a check in
advance and be submitted for later execution. Solidity exposes block height
and timestamp as execution-context values.
[Solidity block and transaction properties](https://docs.soliditylang.org/en/latest/units-and-global-variables.html#block-and-transaction-properties).

Bitcoin time locks provide a concrete illustration. BIP-65 describes outputs
that cannot be spent until a specified time, and explicitly discusses refund
transactions constructed in advance. This supplies an execution constraint,
without the proposed restriction on advance authorship.
[BIP-65](https://github.com/bitcoin/bips/blob/master/bip-0065.mediawiki).

### Signed references to ledger history

Solana's transaction message contains a recent block hash, and its signatures
cover the serialized message. This is a concrete example of authenticating a
ledger reference together with the requested operation. Requiring that the
reference establish completion of *these particular dependencies* would be
an additional application/protocol condition; ordinary recency alone does
not establish it.
[Solana transaction structure](https://solana.com/docs/core/transactions/transaction-structure).

Solana's original whitepaper also discusses including a previously observed
hash in an event to constrain where that event can appear in the history.
This is a conceptual precedent for the proposed causal restriction, not a
proof about the current deployed protocol or our game semantics.
[Solana whitepaper, Section 4.5](https://solana.com/solana-whitepaper.pdf).

Ethereum provides access to historical block hashes, including the history
contract specified by EIP-2935. That supplies a verification ingredient for
an application requiring a signed reference to a suitable block. It does not
by itself prove when a player learned the reference or authored the packet.
[EIP-2935](https://eips.ethereum.org/EIPS/eip-2935).

### Assumptions still needed for a concrete construction

The candidate implementation would authenticate a block or finality
certificate establishing dependency completion, together with the requested
operation. Its correctness argument would need to address:

- **Availability:** the sender cannot obtain suitable evidence before the
  dependency-completion boundary used by the model. A block producer may know
  a candidate block before public dissemination; knowledge of a block and
  finality are different boundaries.
- **Authentication:** early instructions cannot be completed by attaching a
  certificate outside the sender's authenticated payload.
- **Prediction and forgery:** a cryptographic construction gives computational
  guarantees. The exact unforgeability assumption of an ideal Lean model
  would need a separate computational justification.
- **Ledger persistence:** the verified dependency context remains the one
  used by the application, accounting for the chosen finality/reorganization
  assumptions.
- **Progress:** obtaining and using the evidence leaves the promised response
  opportunities before deadlines. It may impose additional block latency.

None of these obligations is discharged by calling a block hash a clock.

## Scope and architecture

This condition need not change source syntax or expose block hashes to game
developers. A small experiment can separate the layers:

| Layer | Candidate responsibility |
|---|---|
| `Interaction` | Generic authenticated-envelope provenance and immutable authorization evidence |
| `Vegas.Pending` | Which event dependencies the evidence must establish, and packet acceptance |
| `GameTheoryExtensions` | Reusable continuation-transfer results, if the resulting simulation can be proved |
| Concrete backend | Realization using a ledger certificate and signatures |

Pending-message observation remains available. Even an invalid early opening
can disclose its plaintext; authorization restricts its application effect,
not what an observer can learn from the bytes. This proposal does not establish
an information-flow theorem.

Full SPE preservation remains a separate task. Among its outstanding issues
are competition between simultaneously ready events, competing packets for
the same event, irreversibly unopenable bindings, deadlines, and correspondence
of proper subgames. First test the ideal authorization contract against the
counterexample and continuation obligations before expanding the core language
or committing to a particular blockchain mechanism.
