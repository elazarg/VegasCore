# Client decisions after runtime irregularities

The strict contract removes many operational decisions. It also permits useful
information to arrive in a rejected packet. The following scenarios use the
existing Odds–Evens program, sequential graph, six-tick deadlines and forced-exit
application. The [checked scenarios](../VegasTests/RecoveryScenarios.lean) reuse
the actual submission, emission, inclusion, expiry and automatic-completion
operations.

| Situation | Contract behavior | Consequence for the player |
| --- | --- | --- |
| The opponent delays within its deadline | Expiry before tick six leaves the state unchanged. | A delay alone supplies no reason to abandon the game. |
| A premature opening is included | The call is rejected and its receipt records failure. The game state and excluded set stay unchanged. | Rejection alone supplies no reason to exit. The packet's information remains observable. |
| The opponent misses its commitment deadline | The opponent is permanently excluded. The survivor can still open; the excluded owner's later opening automatically fails. | Finishing pays the survivor 200. Voluntary exit would pay 0. |
| The player itself has been excluded | Its base utility is fixed at the declared exit value, here 0, for every remaining horizon and activation status. | Additional messages cannot improve that base utility and can create audit liability. Silence is the natural fallback. |
| An accepted commitment is opened prematurely with an authentic certificate | The opening lacks its event's readiness token and is rejected, while the certificate remains visible in the ledger. | A player that has yet to commit can use the disclosed bit. Its ordinary response packets remain permitted by the audit rules. |

## The informative rejection

Even commits bit `e` with its normal opaque handle. Before Odd commits, Even is
activated again and sends a certified opening addressed to Even's later reveal.
Odd's commitment is a predecessor of that reveal, so the opening has no readiness
token. Inclusion rejects the call, leaves the application state unchanged and
puts the signed packet in the ledger. Odd's next observation contains the
certificate for the handle that already won Even's commitment.

The tests check both bit values, certificate issuance, the absent token, the
accepted commitment and rejected-opening receipts, the unchanged application,
and Odd's ledger observation. They also check the subsequent native handlers
for all four pairs of commitment bits and their exact typed terminal readout.
Both of Odd's ordinary packets satisfy the count verdict in the full signed
traffic list, even with Even's premature and repeated opening present.

If Even subsequently reveals its committed bit, Odd's choices have these values:

| Odd's response | Odd's payout |
| --- | --- |
| Commit the opposite bit and later open | 126 |
| Draw a fresh fair bit and later open | 100 in expectation |
| Commit the same bit and later open | 74 |
| Voluntarily exit | 0 |

These comparisons condition on the stated continuation. The tests establish
that the continuation is admitted by the native handlers. A claim about
optimality against an entire runtime assessment also needs its continuation
strategies and beliefs.

No pending-pool observation is needed for this example: the rejected packet is
public after inclusion. Authentication matters. The useful signal identifies
the immutable value of the accepted handle; an unsupported claim or a
certificate for a different candidate supplies different information.

## An explicit ledger-reading candidate

[The client](../Vegas/Examples/OddsEvensLedgerClient.lean) sends each ordinary
packet once, requests its valid opening when ready, continues after the
opponent's exclusion, and stops after its own exclusion. At Odd's commitment it
reads authentic ledger certificates for Even's accepted handle. A matching
Boolean certificate selects the opposite bit; otherwise it uses the intended
fair strategy. Calls and certificates for other handles supply no value to
this reader.

The [ledger policy interface](../Interaction/ReactiveLedgerPolicy.lean) removes
pending observations from the current view and every recorded earlier view.
Its checked factorization theorem ensures that the candidate's decision law
is independent of those observations. Private values, own actions and emitted
packets, contract state and receipts remain available. Own submission recall
suppresses retries before receipt, so monitoring a pending packet is unnecessary.

An opponent can also attach an authentic certificate to its original commitment
submission. The native call accepts that commitment while the count audit
marks its certificate-bearing packet forbidden. The checked recipient reads
the bit from the ledger and requests the opposite commitment. This variant
needs no extra activation between acceptance and Odd's ordinary turn.

The client proof target concerns histories consistent with the focal player's
own policy, while allowing opponents to deviate. A full equilibrium assessment
may separately complete histories involving that player's own earlier errors.
The [client correctness analysis](ledger-client-correctness.md) states this
target precisely and isolates its remaining belief obligation. The complete
sequential rationality of this candidate is open.

## Verification scope

The tests check individual operations and finite continuations of the actual
application. The early-opening schedule includes an extra activation of Even
before Odd's first commitment. The existing periodic Odds–Evens scheduler has
a fixed activation order and is left unchanged. Proving a complete scheduler
that realizes this prefix and satisfies the all-history service contract is a
separate obligation. These scenarios therefore do not constitute a new
sequential-equilibrium counterexample or contradict the preservation capstone.

The [instance guide](sequential-se-instances.md) describes the existing complete
service and equilibrium result. The [open-problems guide](sequential-se-open-problems.md)
records the broader runtime and evidence assumptions.
