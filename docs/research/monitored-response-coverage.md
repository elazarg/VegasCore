# Response coverage in the monitored two-reveal fixture

This audit concerns the actual fixed runtime and the C → W menu extension in
[the compilation plan](../se-compilation-stack.md). C implements withholding by
silence followed by expiry; successful opening carries its matching certificate.
W restores ordinary players' effective responses and fixes Watcher's reporting
response at every input. Utilities are arbitrary declared tables over publication
results, with nonnegative liability charges computed from that table before
choosing an equilibrium. The source family has two reveals, a fair private
Boolean for Alice, Bob's initially committed value true, and valid initial
bindings. It retains both opening and withholding at both source decisions.

## Bob's retained decision

The checked retained-history prerequisite is that each C Bob history has the
`quietBob bit` state: Alice's ambient response and Watcher's response were silent,
the pool and ledger are empty, and Bob has no earlier output. The explicit
checkpoint and its classification of **all** C Bob histories are proved in
[`MonitoredGuessingRestrictedSupport`](../../Vegas/Examples/MonitoredGuessing/RestrictedSupport.lean).

| Response at that checkpoint | Actual effect | Certificate route and status |
| --- | --- | --- |
| Silence | No packet; Bob fails at expiry. | Legal C withholding. `Restricted.silent_bob_service` is checked in `MonitoredGuessingRestrictedExecution.lean`. |
| Canonical opening with matching evidence | Reserved inclusion succeeds; Bob publishes true. | Legal C opening. Actual inclusion and clean ledger audit checked. |
| Another Bob-addressed packet, accepted | Included packet/receipt is visible to Alice. Examples: explicit withholding, certified withholding, valid opening without its certificate. | Requires enforcement because arbitrary paired continuations may react to the new transcript. Concrete accepted-packet regressions and persistent ledger audit checked in `MonitoredGuessingConformance`. |
| Another Bob-addressed packet, rejected | Reserved inclusion still records the packet and failed receipt. | Uniform inclusion, unit liability and persistence through arbitrary later policies are checked in `MonitoredGuessingBobConformance`. |
| Packet addressed to Alice | Bob's reserved selector ignores it. It remains pending; Bob fails at expiry. | `MonitoredGuessingBobIgnored` proves the same terminal result/Bob-net-payoff law as silence when continuations agree on Alice's matching input. |
| Untagged malformed packet | Same unselected-pending behavior. | Covered by the same checked input theorem. No rejection receipt exists because this packet is never selected. |
| Known replay | No known envelope exists at this checkpoint. | `quiet_bob_response_cases` excludes replay using actual raw menu membership. Non-retained Bob sites belong to completion, not this comparator obligation. |
| Ineffective private material or certificate requests | Normalization preserves emitted packet and application effects. | Existing normalization handles ignored opening material, failed owned certificate requests and certificate-free forwarding. The final alias edge restores raw syntax. |
| Different request with the canonical emitted packet | No new public marker. | `effective_bob_response_cases` proves that normalized canonical emission is a legal C response; no invisible request distinction is charged. |

The application protects other owners' candidate catalogues:
`Submission.register_other` and `submitStep_playerView_other` prevent Bob's
private registration from becoming a hidden channel into Alice's local catalogue.
Thus ignored traffic need not mean an ignored application-side mutation; the
ownership laws are part of its harmlessness proof.

## Monitoring and the important scope limit

The existing passive Watcher activation occurs **before** Bob's response. It
provides no pending-message detection probability for Bob. The checked
ledger audit detects included Bob packets using original envelope authorship;
its checked persistence is evidence preservation, not an escrow theorem.

In this exact fixture Alice samples no pending packets. The checked
[`wrong_address_alice_input_law`](../../Vegas/Examples/MonitoredGuessing/BobContinuation.lean)
runs actual reserved selection, tick, expiry, grant and activation, and proves
exact equality of her next recall and full view with the C silent branch. It
quantifies arbitrary submission contents, private registrations and policies.
This is a substantive property of the observation rule, not a consequence of
compiler correctness or rational behavior. The checked terminal comparison in
[`MonitoredGuessingBobIgnored`](../../Vegas/Examples/MonitoredGuessing/BobIgnored.lean)
uses this input equality and proves equality of the joint result/Bob-net-payoff
law for arbitrary continuations agreeing on Alice's mixed legal response there.

If a later decision maker can read those pending packets, that argument fails.
For example, a Bob-authored packet addressed to Alice can serve as a public
marker in her passive sample while avoiding Bob's inclusion slot and every
current Watcher slot. Paired source continuations can withhold after both legal
Bob choices while the target continuation opens only after that marker. A table
rewarding Bob for Alice's opening defeats every uncharged legal comparator.
This is a conditional obstruction to the uniform certificate, not a claim that
sequential-equilibrium preservation itself is impossible.

The general reveal class therefore needs either an operational monitoring/service
change covering later readers or another proved comparison. A two-channel design
must bound the union of attributable ledger evidence and pending reports at each
departure; it cannot assume a sampling bound conditioned on eventual non-inclusion.

## Operational certificates and equilibrium composition

All five receiver obligations have checked operational proofs: retained control,
ignored-traffic terminal law, canonical-emission classification, persistent
liability for addressed extras, and the arbitrary-table range bound. The latter
uses Bob's whole-outcome payoff range as his deposit, through
[`MonitoredGuessingBobDeterrence`](../../Vegas/Examples/MonitoredGuessing/BobDeterrence.lean).
The checked `bob_continuation_comparison` in
[`MonitoredGuessingRestrictedBobComparisons`](../../Vegas/Examples/MonitoredGuessing/RestrictedBobComparisons.lean)
instantiates the generic action-restriction inequality. It quantifies over every
C Bob site, every hidden history at that site, every extra W choice, and all
extending continuation profiles. Its comparator is legal silence. The only fuel
premise is that execution can finish the remaining service; the fixed calendar
discharges it. No continuation equilibrium or rationality premise is used.

The suffix proof reuses `final_response_owner_local` in
`MonitoredGuessingFinalComparison.lean`: equal Alice recall/view plus
`FinalResponseLocal` invariants give equal final application views for the same
response. The ignored-traffic theorem supplies the input equality. Remaining
trace obligations are discharged by
[`MonitoredGuessingBobContinuationTrace`](../../Vegas/Examples/MonitoredGuessing/BobContinuationTrace.lean).
Alice has no earlier emitted packet on this prefix, so the unique-event-output
condition is vacuous. This covers silence/opening and their prescribed mixtures
using the actual service implementation.

The comparator must be fixed by Bob's information and action, and valid at each
embedded source history for **all** extending continuation profiles. Showing
only that Bob's decoded publication is the same does not meet that requirement.

Initial Alice extras are bounded by the monitored whole-outcome range calculation.
Every raw final Alice response instead has a legal opening/silence comparator
determined by her own information and that response. The latter preserves the
terminal result and cannot add a charge relative to the raw response; it does
not assert equality of public packet histories. These are the checked
`initial_continuation_comparison` and `final_continuation_comparison` interfaces.
Watcher has no extra choice in C → W. Its choices are restored separately using
utility zero at every state, then proved private-response normalization restores
the bounded raw menu.

## Economic and abstraction boundaries

For each ordinary player, let R be the declared table's maximum minus minimum
over every publication-result pair, including failure. The fixed deposits are
2R for Alice and R for Bob. The first uses the actual one-half passive sampling
rule and prescribed reporting; the second uses certain reserved inclusion of
Bob-addressed traffic. Both bounds cover irrational source continuations and
zero-range tables. They give weak deterrence, sufficient for an equilibrium
extension, not strict compliance or equality of all equilibrium sets.

Every native edge uses the same `Enforcement.comparisonStateUtility`: declared return
minus the specified collectible liability. Legal C play has zero liability and
returns the literal source table. Raw normalization preserves this utility and
the joint type/result/net-payoff observation. The result does not supply an
escrow implementation, reporting costs, transfer resistance, or coalition
incentives. Watcher's prescribed reporting is rational by indifference; it is
not guaranteed in every native equilibrium. Its declared table entries must all
be zero for that final extension.

The runtime still uses ideal authenticated envelopes and opening evidence,
finite response bounds, and the fixed activation/inclusion calendar. Initial
validity is supplied by the actual setup encoding, not by a proved on-chain
setup protocol. The result does not establish these assumptions for a
cryptographic implementation where players can share signing or opening secrets.

The fixed source-to-C policy translation preserves the joint observation/payoff
law for every source profile. Native
completion at newly reachable information sites may depend on the whole source
assessment. Accordingly the preservation direction is every source SE has a
native SE extension in one fixed game, not a universal playerwise translation
of off-path native behavior. A once-collected charge is adequate for the proved
response classes here; the result does not justify repeated departures after a
sanction is sunk in a longer game.

Omitting source withholding or unusable commitments would be a further theorem.
A deadline can make missed disclosure attributable, but the player must have a
timely honest opportunity and the liability must survive aborts, refunds, and
skipped opening paths. Passive packet sampling cannot detect silence. This
fixture proves neither that stronger enforcement contract nor validity of fresh
commitments, and currently keeps every source withholding choice.
