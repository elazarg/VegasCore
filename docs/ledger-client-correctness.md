# Ledger-reading honest clients

The client uses contract state, ledger packets and receipts, its private game
values, and its own submission history. It ignores pending messages throughout
its recall. Other players may deviate. This is the deployment target for the
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
candidate's action law invariant under changing the removed observations.

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
[the scenario tests](../VegasTests/RecoveryScenarios.lean). The calendar table
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

The desired compiler interface supplies an explicit client for each intended
equilibrium, and a consistent sequential-equilibrium assessment agreeing with
that client at every compatible decision of each player. At other decisions,
the assessment may select a rational completion. This retains the ordinary
equilibrium notion and gives a concrete implementation throughout every
history the honest player can encounter against deviations.

The existing preservation capstone supplies an assessment and exact supported
outcome law. Agreement with the ledger client on all compatible decisions
remains an additional obligation. Full source failure subgames can require
program-specific continuation choices; the always-open payoff argument above
uses the actual Odds–Evens settlement rule.

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

The implemented candidate performs no pending inspection. Its current checked
results are information factorization, repeat and exclusion behavior, concrete
ledger observations and conditional payoff comparisons. Sequential rationality,
the compatible-history agreement theorem and the complete initialized client
outcome law remain open.
