# Response coverage in the monitored two-reveal fixture

This audit concerns the actual fixed runtime and the C → W menu extension in
[the compilation plan](../se-compilation-stack.md). C implements withholding by
silence followed by expiry; successful opening carries its matching certificate.
W restores ordinary players' effective responses and fixes Watcher's reporting
response at every input. Utilities are arbitrary declared tables over publication
results, with separately stated, nonnegative liability charges.

## Bob's retained decision

The intended retained-history prerequisite is that each C Bob history has the
`quietBob bit` state: Alice's ambient response and Watcher's response were silent,
the pool and ledger are empty, and Bob has no earlier output. The explicit
checkpoint exists; its classification of **all** C histories is still required.

| Response at that checkpoint | Actual effect | Certificate route and status |
| --- | --- | --- |
| Silence | No packet; Bob fails at expiry. | Legal C withholding. `Restricted.silent_bob_service` is checked in `MonitoredGuessingRestrictedExecution.lean`. |
| Canonical opening with matching evidence | Reserved inclusion succeeds; Bob publishes true. | Legal C opening. Actual inclusion and clean ledger audit checked. |
| Another Bob-addressed packet, accepted | Included packet/receipt is visible to Alice. Examples: explicit withholding, certified withholding, valid opening without its certificate. | Requires enforcement because arbitrary paired continuations may react to the new transcript. Concrete accepted-packet regressions and persistent ledger audit checked in `MonitoredGuessingConformance`. |
| Another Bob-addressed packet, rejected | Reserved inclusion still records the packet and failed receipt. | The same ledger audit can detect it. Uniform inclusion/audit law for the complete syntactic class remains to be assembled. |
| Packet addressed to Alice | Bob's reserved selector ignores it. It remains pending; Bob fails at expiry. | Exact equality of Alice's next recall and full view with the C silent branch is checked in `wrong_address_alice_input`. Whole suffix comparison remains. |
| Untagged malformed packet | Same unselected-pending behavior. | Covered by the same checked input theorem. No rejection receipt exists because this packet is never selected. |
| Known replay | No known envelope exists at this checkpoint. | `quiet_bob_response_cases` excludes replay using actual raw menu membership. Non-retained Bob sites belong to completion, not this comparator obligation. |
| Ineffective private material or certificate requests | Normalization preserves emitted packet and application effects. | Existing normalization handles ignored opening material, failed owned certificate requests and certificate-free forwarding. The final alias edge restores raw syntax. |
| Different request with the canonical emitted packet | No new public marker. | Prove that a normalized response at this empty-known checkpoint is the canonical C action; do not charge an invisible request distinction. |

The application protects other owners' candidate catalogues:
`Submission.register_other` and `submitStep_playerView_other` prevent Bob's
private registration from becoming a hidden channel into Alice's local catalogue.
Thus ignored traffic need not mean an ignored application-side mutation; the
ownership laws are part of its harmlessness proof.

## Monitoring and the important scope limit

The existing passive Watcher activation occurs **before** Bob's response. It
provides no pending-message detection probability for Bob. The proposed new
ledger audit detects included Bob packets using original envelope authorship;
its checked persistence is evidence preservation, not an escrow theorem.

In this exact fixture Alice samples no pending packets. The checked
[`wrong_address_alice_input_law`](../../VegasTests/MonitoredGuessingBobContinuation.lean)
runs actual reserved selection, tick, expiry, grant and activation, and proves
exact equality of her next recall and full view with the C silent branch. It
quantifies arbitrary submission contents, private registrations and policies.
This is a substantive property of the observation rule, not a consequence of
compiler correctness or rational behavior. It does not yet state the terminal
law under every paired continuation profile.

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

## Remaining proof gates

1. Classify every retained C Bob history as the actual quiet checkpoint.
2. Compose the checked ignored-traffic next-input equality with a whole suffix
   law for every paired continuation profile.
3. Complete canonical-emission/alias classification at that checkpoint.
4. Prove unit ledger liability for every other Bob-addressed submission,
   including accepted calls, and compose the existing persistence theorem.
5. Apply the arbitrary-table range certificate using additional collectible loss.

The intended suffix route reuses `final_response_owner_local` in
`MonitoredGuessingFinalComparison.lean`: equal Alice recall/view plus
`FinalResponseLocal` invariants give equal final application views for the same
response. The ignored-traffic theorem supplies the input equality. Remaining
work constructs actual final traces or those operational invariants for its
supported executions and the C silent checkpoint. Alice has no earlier emitted
packet on this prefix, so the unique-event-output condition is vacuous. This
route covers silence/opening and their prescribed mixtures without a duplicate
special expiry implementation.

The comparator must be fixed by Bob's information and action, and valid at each
embedded source history for **all** extending continuation profiles. Showing
only that Bob's decoded publication is the same does not meet that requirement.
