# Ledger-reading honest clients

The [uniform semantic compiler](semantic-client-compiler.md) supplies certified
clients for every supplied intended equilibrium. This note analyzes a manually
prescribed diagnostic policy and the additional belief argument needed to
identify that particular policy with an equilibrium. The generic compiler
uses the preservation theorem's selected completion instead.

The client uses contract state, ledger packets and receipts, its private game
values, and its own submission history. Its callback applies the ledger
projection to explicit leaked-message fields. Other players may deviate. This
is the deployment target for the
[explicit Odds–Evens client](../Vegas/Examples/OddsEvensLedgerClient.lean).

## What the honest client must remember

At each callback, the client checks its exclusion status and owned ready event.
If it has already submitted a packet for that event, it waits for a receipt or
the next contract state. This uses its own recorded action, even before ledger
inclusion. It needs neither a pending-pool query nor a retry heuristic.

Otherwise, Even chooses a fair bit at its commitment. Odd reads certificates
from the ledger, matching them against Even's accepted binding handle and
checking the Boolean type. A matching certificate selects the opposite bit;
without one, the candidate chooses fairly. At either opening, the client uses
the stored private value through the existing canonical service decision.
It sends one ordinary opening and continues after the opponent's exclusion.
Its own exclusion returns silence.

The [ledger projection](../Interaction/ReactiveLedgerPolicy.lean) also removes
pending observations from each historical view. Removing only the current
observation would still allow a policy to recover a pending message from its
saved history. The projection retains own actions and output and makes the
candidate's action law invariant under changing the removed fields with all
retained fields fixed. Own emitted envelopes can themselves retain evidence
materialized after a private pending delivery. `IgnoresLeakedFields` therefore does
not assert independence from every causal effect of pending information. The
generic physical-realization theorem uses `DeliversNothing`, so these private
deliveries do not occur in that theorem's initialized histories.

## A disclosure already on the ledger

The opponent's commitment submission can request an owned certificate for the
very candidate it registers. Certificate issuance follows registration in the
same atomic response. The application accepts the commitment; its handler
does not reject attached evidence. The count audit separately forbids evidence
on a commitment. The recipient can read the authentic certificate from the
included envelope without incurring an audit charge on its own normal packets.

This variant fits the existing periodic service's ordinary command order:

| Cycle | Relevant operation |
| --- | --- |
| 1 | Even submits the certificate-bearing commitment. Odd has no ready event yet. |
| 2 | Pending processing includes and accepts Even's commitment. Odd's event becomes ready. |
| 3 | Odd's ordinary callback sees the certificate in the ledger before choosing its bit. |

The packet operations, readout and informed client branch are checked in
[the scenario tests](../VegasTests/RuntimeScenarios.lean). The calendar table
uses the existing scheduler's checked command order; a combined initialized
rounds-trace theorem for this table has not been added. The same scheduler's
all-history opportunity, inclusion and completion proofs are unchanged.

An early opening supplies a second route. Before inclusion the ledger reader
returns no bit. After rejection and ledger inclusion it returns the authentic
bit, despite unchanged contract state. Both reader results are checked.

## Rationality reduces to specific game questions

For a valid committed bit in Odds–Evens, successful opening pays at least 74
for every publication result of the opponent. Own publication failure pays 0.
These inequalities are checked for both players and include opponent failure.
Under timely protected service, they explain the incentive to finish an
ordinary valid opening and the survivor's payout of 200 after the other's exit.
The comparison concerns base utility; raw traffic and audit incentives remain
governed by the separate enforcement result.

At Odd's commitment, condition on Even subsequently publishing successfully.
Let `p` be the posterior probability that Even's accepted bit is true. Then

* choosing false has value `74 + 52 p`;
* choosing true has value `126 - 52 p`;
* choosing fairly has value `100`.

The checked finite payoff calculation shows that fair play is optimal among
these choices exactly when `p = 1/2`. An authentic opening fixes `p` to zero or
one and makes the opposite bit optimal. In the intended fair game, hiding the
first bit supplies the unbiased posterior. At unusual ledger histories,
absence of a matching certificate alone does not prove an unbiased posterior.
The [ledger evidence theorem](../Vegas/Examples/OddsEvensClientPosterior.lean)
shows that a matching read determines the stored bit on every initialized
service history. At any Odd decision site with such a read, the posterior
on the stored commitment is a point mass for every assessment, including
at sites reached only after deviations. The same module proves an unbiased
posterior at the periodic service stop immediately after the first ordinary
commitment. The two fixed-bit runs have identical distributions of Odd’s
whole observation and recall, and each stores its prescribed bit. Mixing
these runs with a fair coin leaves the bit fair conditional on every
positive-probability observation at that stop.
The [first ready callback theorem](../Vegas/Examples/OddsEvensReadyCommitment.lean)
identifies the decision in the initialized periodic run of the handwritten clients.
The selected command activates Odd with its second commitment ready. Every
previous Odd callback selected no turn. Conditioning on any supported full
view and recall after activation and before Odd responds gives probability
one half to each of Even’s two successful commitment values.
More generally, fix the distribution of Even’s publication across Odd’s
choices and allow Even to fail. The [payoff criterion](../Vegas/Examples/OddsEvensCommitmentPayoff.lean)
shows that a fair coin maximizes Odd’s base payoff over every randomized
successful commitment exactly when the probabilities of successful true and
successful false are equal. Failure pays Odd 200 for either choice. This also
covers certain failure, where conditioning on success would be undefined.
There is also a [selective disclosure example](../VegasTests/RuntimeScenarios.lean).
Even registers a fair bit and always requests a certificate for true on the
same submission. The native commitment succeeds for either bit. Under this
sender policy, conditioning on the complete Odd view without a certificate
puts probability one on false. This calculation conditions on the specified
deviation; sequential consistency instead requires a common perturbation of
the candidate strategy profile.
A consistency argument must justify the candidate's fair fallback, or identify
ledger cases requiring a different response.

Thus an explicit client still needs a belief proof, even when every action
reads only the ledger. Observed messages, timings and handle choices can affect
beliefs. Their interpretation belongs in the compiler's correctness argument;
the deployed client executes the resulting fixed decision rule.

## The theorem target for an honest implementation

A history is compatible with player `i`'s client when each recorded action of
`i` lies in the support of the client's law at that recorded decision, using
its preceding own recall. Opponents' actions are unrestricted. This includes
failures and disclosures caused by opponents, while excluding prior actions
that the compiled player would never have taken.

For Odds–Evens, every supported client response belongs to the concrete
bounded menu at every legal decision compatible with that player's own prior
responses. Choosing silence after an incompatible own response gives a total
admissible policy. Both statements allow opponents to deviate within the menu.
See the [client admissibility proofs](../Vegas/Examples/OddsEvensClientAdmissibility.lean).

The desired compiler interface supplies an explicit client for each intended
equilibrium, and a consistent sequential-equilibrium assessment agreeing with
that client at every compatible decision of each player. At other decisions,
the assessment may select a rational completion. This retains the ordinary
equilibrium notion and gives a concrete implementation throughout every
history the honest player can encounter against deviations.

The semantic compiler's ledger clients agree with their selected assessment
at every legal raw history under no pending delivery, including every
compatible history described here. Agreement with the manually prescribed
Odds–Evens candidate remains a separate obligation. Full source failure
subgames can require program-specific continuation choices. The distinction
already arises when Even's first commitment includes a forbidden certificate.
Odd can have followed its client on every prior callback and still face a new
decision after Even's violation. The audited extension selects a continuation
for that site. Identifying its action with the executable client's choice
requires an additional proof. The always-open
payoff argument above uses the actual Odds–Evens settlement rule.

## Scope of pending information

The concrete service delivers no pending packets to players. Ledger-reading
therefore uses all network information supplied to the honest client. The
generic preservation theorem also permits observation rules that deliver
private pending packets. A claim that the same client remains sequentially
optimal while ignoring those extra signals would require a separate argument.
For example, a pending certificate can reveal an accepted bit before the
recipient commits, even when the ledger has not yet disclosed it. The
protected-inclusion premise covers permitted traffic, so it does not by itself
force a forbidden revealing packet onto the ledger before that decision.

The [executable Odds–Evens decision](../Vegas/Examples/OddsEvensExecutableClient.lean)
takes a decoded turn, an optional authenticated bit and a coin. Feeding it a
fair coin and encoding its decision gives exactly the candidate’s packet law
at every callback and recall. An [executable raw decoder](../Vegas/Examples/OddsEvensClientInput.lean)
reads these inputs from the actual typed callback and own recall, with
pointwise equality to the model decoder on every input. For the allocator, a
[bounded search](../Vegas/Pending/BoundedCanonicalSlot.lean) using a player's
recall length agrees with the canonical slot at every initialized service
history. The [executable callback](../Vegas/Examples/OddsEvensClientOutput.lean)
returns the complete raw packet action from the typed view, own recall and a
coin. This includes forwarding an available opening certificate and remaining
silent after an earlier submission. Its fair-coin distribution equals the
prescribed action distribution at every initialized history.

The [execution theorem](../Vegas/Examples/OddsEvensClientExecution.lean) allows
either or both players to install this callback. For every scheduler, number
of rounds and choice of the remaining players’ policies, the complete
execution distribution agrees with the corresponding run of the prescribed
clients. This includes packets, receipts, private recall and the application
state at intermediate rounds.

When both handwritten clients are used, [the honest-prefix theorem](../Vegas/Examples/OddsEvensHonestCommitment.lean)
shows that the ledger contains no matching certificate before the second
commitment finishes, for any scheduler. At Odd’s unsent commitment the
candidate therefore uses a fair coin. Sequential rationality,
agreement with that specific policy and its complete initialized outcome law
remain open. They are not premises of the uniform semantic compiler.
