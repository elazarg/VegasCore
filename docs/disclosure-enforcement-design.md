# Enforcing a disclosure policy around an abstract game

## Candidate placement and status

An optional layer below the ordinary source could add ambient communication,
a disclosure policy and escrow transfers while retaining source syntax.
Unexpected communication remains legal and visible; the intended theorem
extends source equilibria while preserving initialized game results and net
payoffs. This layer is a candidate, not part of the production compilation
tower. There are two distinct proof obligations:

```text
ordinary game
    -- equilibrium extension using bounded gains and credible enforcement -->
game with ambient communication and escrow
    -- observations, feasible reports, account control, delivery, transfers -->
native implementation
```

The checked finite experiment below supplies the first edge for one game,
using automatic enforcement. The second must implement its information and
enforcement powers: inspecting the true execution history requires more than
a blockchain monitor's view.

## What is prohibited, what is evidenced, and who pays

The policy should identify an accountable event, such as prematurely sending
opening material. Knowledge alone does not identify that event: it may come
from initial correlation, deduction, a guess or authorized disclosure.
Knowledge also differs from possession of transferable opening evidence.

A proposed report has three logically separate obligations:

1. Its evidence establishes the relevant fact and its association with this
   game or with a protected candidate later selected by this game.
2. It establishes a prohibited release at the relevant time, and identifies
   the escrow account whose declared obligation was breached.
3. Its successful adjudication actually debits that escrow and determines any
   reporter payment, with replay and duplicate claims settled consistently.

An `OpeningFact` records a candidate and its value. It does not establish
transmission time, an attributable policy breach, or a collectible claim.
The commitment owner need not be the sender; account authentication need not
identify strategic control after key sharing. The
[capability audit](ideal-commitment-capabilities.md) records the required
treatment of shared witnesses and keys.

**Sending liability** needs origin and timing evidence. **Custody liability**
charges a designated custodian when material becomes available early; it needs
exclusive initial custody or an explicit allocation of risk. That charge does
not establish who sent the material. Initially shared witnesses and dealers
capable of manufacturing reports make the distinction consequential.

Zero false positives must cover every permitted source action and deviation,
with its intended source payoff. Normal compiled openings enter the network
before ledger inclusion, so pre-inclusion transmission alone is insufficient
evidence of a violation. An unpenalized selected equilibrium path does not
establish preservation of the source deviation game.

## The upper incentive edge

For a fixed player information set `I`, compare an arbitrary continuation
deviation with a legal continuation that omits its prohibited disclosures.
Suppose a coupling identifies the first prohibited episode `V`, and the
expected increase in ordinary game utility is at most

```text
G(I) * Pr(V | I).
```

This comparison requires a source-compatible replacement strategy and an
actual outcome-law argument. A bound on terminal utility range can bound the
loss after a coupled first divergence; it does not construct the coupling.
Other permitted deviations must already be covered by source rationality.

If the deviation's expected additional net enforcement loss is at least

```text
p(I) * D(I) * Pr(V | I),
```

then the total gain is at most `(G(I) - p(I) * D(I)) * Pr(V | I)`.
Here `D(I)` is the remaining enforceable loss, net of refunds, bounties returned
to the deviator, and any modeled costs or side payments. This elementary
subtraction is an incentive bound, not yet an SE-preservation theorem.

[Enforcement.lean](../GameTheoryExtensions/Analysis/Enforcement.lean) checks
the underlying comparison bounds. `regret_eq` uses the difference between
deviation and prescribed sanction probabilities; `regret_le` specializes to
an unsanctioned prescribed plan. `isSequentiallyRationalAt_of_sanction` applies
the bounds to every whole-policy deviation at an actual assessment information
set. These theorems construct neither a monitor nor consistent beliefs.

Detection must hold **conditional on the deviator's information and chosen
continuation**. An average monitoring rate fails if the player can disclose
only when the monitor is absent. Recipient selection, timing, retries and
censorship belong in this bound. A deposit already lost is a sunk cost: later
deterrence needs remaining escrow, or an optimal continuation allowing further
disclosure. Escrow must remain enforceable through the reporting window.

The monetary model must specify utility for transfers. Liquidity costs,
external stakes, capital constraints and fees are absent unless modeled.
A fixed deposit cannot deter disclosure over unbounded game stakes.
The checked `exists_rescaling_defeating_sanction` makes the last limitation
precise: scaling only a profitable base payoff sufficiently defeats a fixed
utility sanction. It does not rescale the complete utility, including the
sanction, or assume a universal conversion from currency to utility.

## Stronger candidate: monitored protocol conformance

A watchdog can enforce a broader rule than detecting opening certificates:
sanction every accountable message outside the compiled communication protocol.
Take coverage of the relevant communication medium, attribution and enforceable
sanctions as explicit environment assumptions. Investigate that medium on its
own; an assumed external channel is not needed to assess this candidate.

Distinguish **protocol conformance** from **conformance to one strategy profile**.
The first should retain every legal source bid, choice and withholding while
constraining their implementation. The second can sanction a player merely for
choosing a different legal source action. It may enforce a prescribed outcome,
but changes the source deviation game and needs a different theorem statement.

A concrete protocol monitor can check authorized accounts, source event and
service window, message multiplicity, permitted evidence, and canonical
identifiers or encoding fields. Its admitted traces must include ordinary
submissions before inclusion. A proof of compliance may certify a relation
involving hidden values; it does not automatically let a public watchdog
reconstruct a strategy depending on private types or coins. Observing one
action in a randomized strategy's support also does not certify its sampling
probabilities. Enforcing those probabilities needs a stated randomness or
execution service.

The remaining lower-edge obligation is **source adequacy of admitted behavior**:
every admitted native observation and deviation must have the source account
required by the strategic theorem. Payload variations, unused fields, candidate
identifiers, cryptographic randomness, timing and silence can carry signals
while every message has a legitimate shape. Variations already observable as
legal source choices belong in that source account; implementation-only
variations must be normalized, accounted for, or proved strategically harmless.
Canonicalization alone supplies no theorem about all these channels.

There is a sharp checked limit to zero-false-positive enforcement for a specified
lawful observation law `mu`. In
[Enforcement.lean](../GameTheoryExtensions/Analysis/Enforcement.lean),
`alarm_zero_iff` requires silence at every observation in `mu.support`, even
for randomized alarms. `detection_le_outside_support` bounds detection of a
deviating law `nu` by `nu.probOf (mu.supportᶜ)`;
`exists_optimal_sound_alarm` attains that bound with the same deterministic
outside-support alarm for every `nu`. Thus `alarm_zero_of_support_subset`
rules out sound detection whenever every deviating observation is lawful,
even if its probability changed. These are existence and optimality results
over a specified observation carrier, not implementations of a monitor.
Retaining all legal source strategies requires soundness for all their laws,
not only for the selected equilibrium's observations.

[ObservableEnforcement.lean](../GameTheoryExtensions/Analysis/ObservableEnforcement.lean)
quantifies that distinction. `sound_for_family_iff` takes a family of permitted
observation laws: soundness for every member is precisely silence on the union
of their supports. For one profitable deviation, `exists_sound_deterrent_iff`
then characterizes whether any finite nonnegative utility fine and sound alarm
can deter it: its observation law must put positive mass outside the admitted
set. The forward construction charges the original gain divided by that mass.
This is an exact incentive-comparison result with automatic collection, not an
executable checker, a uniform fine for every deviation, or an SE theorem.

[MonitoredSignaling.lean](../GameTheoryExtensionsTests/MonitoredSignaling.lean)
isolates initially shared information. Alice and Bob share a fair private pad
`r`, independent of her secret `x`. A permitted field `c` is either independent
and fair or deliberately chosen as `x xor r`. The public observation `(x,c)`
has the same law in both cases, even if `x` is eventually revealed:
`public_transcript_law` holds for any secret prior, `monitor_law` allows
randomized monitoring, and `sanction_expectation_zero` transports zero expected
sanctions. Bob's decoder `c xor r` succeeds with probability one under signaling
and one half under honest use (`signaling_correct`, `honest_correct`).
No forged message or external channel is involved.

Including Bob's public guess changes the result: `interaction_laws_differ`
proves statistical distinction is possible. Yet every signaling transcript
remains possible under honest independent fair messaging and guessing.
`interaction_alarm_zero` therefore gives zero detection for any alarm with zero
honest false positives, even observing `(eventual secret, field, public guess)`.
For every fixed secret, randomized monitor and pointwise nonnegative sanction,
`interaction_sanction_le_twice_honest` proves

```text
expected signaling sanction <= 2 * expected honest sanction.
```

The honest law is the equal mixture of the signaling law and an incorrect-guess
branch. This bound permits different enlarged transcript laws and does not
cover general signed transfers. The obstruction requires free permitted
variation and private shared correlation; it is not universal over canonical
protocols. Removing sender control, constraining its admissible use, or
representing the signal in the source are separate proposals. Complete packet
coverage alone does not close this information gap.

### Future work: mediation before observation

This problem has direct cryptographic precedents. Lepinski, Micali and shelat
define collusion-free protocols to preserve communication intrinsic to legal
game actions while preventing extra communication introduced by the protocol.
Their positive construction assumes finite games with publicly observable
actions and physical setup channels; hidden Vegas choices do not automatically
satisfy those hypotheses.
[Collusion-Free Protocols (2005)](https://shelat.khoury.northeastern.edu/dl/CollusionFreeSTOC.pdf)

Alwen, shelat and Visconti instead assume a mediator that filters and
rerandomizes traffic, with a separate security condition for a corrupt mediator;
subsequent work gives mediated collusion-free multiparty computation.
[Mediated model (2008)](https://crypto.ethz.ch/publications/files/AlShVi08.pdf),
[multiparty construction (2009)](https://www.iacr.org/archive/crypto2009/56770517/56770517.pdf)
The stronger collusion-preserving formulation fixes the same external
communication resources on both sides and requires that the implementation
introduce no additional communication capacity; ordinary collusion-freeness
does not imply this compositional guarantee. This is a closer research target
for preserving a game's ambient communication than assuming communication
away. Its constructions still require explicit resources with isolation,
independent randomness and programmability.
[Alwen, Katz, Maurer and Zikas (2012), Sections 1.1 and 2](https://www.iacr.org/archive/crypto2012/74170124/74170124.pdf)

Cryptographic reverse firewalls similarly transform messages in transit
without access to the protected party's private state or shared secrets.
[Mironov and Stephens-Davidowitz (2015), Sections 1.1 and 2](https://www.iacr.org/archive/eurocrypt2015/90560152/90560152.pdf)

These are candidates for enforcing a communication abstraction **before
recipients observe sender-controlled encodings**, under stronger communication
control than a watchdog imposing fines afterward. Their guarantees need a
protocol-specific instantiation; residual channels have been exhibited in
particular constructions advertised as subliminal-free signatures.
[Teseleanu (2021)](https://eprint.iacr.org/2021/1331.pdf)
None supplies a blockchain implementation or an SE-preservation theorem here.

## Checked sequential-equilibrium experiment

The [finite ambient game](../GameTheoryExtensionsTests/AmbientEnforcement.lean)
has a fair secret bit known to Alice. Bob always guesses; both receive one for
a correct guess and zero otherwise. The source hides the bit from Bob and
gives Alice no action. The target additionally lets Alice disclose before
Bob's choice, with automatic deduction `D` from her payoff. Ordinary source
actions are never fined.

[AmbientEnforcementSource.lean](../GameTheoryExtensionsTests/AmbientEnforcementSource.lean)
proves `source_sequential_equilibrium` for every source policy profile: any
guess distribution `q` is rational against the hidden fair bit. The proof
includes consistent beliefs and a common fully mixed sequence.

[AmbientEnforcementEquilibrium.lean](../GameTheoryExtensionsTests/AmbientEnforcementEquilibrium.lean)
compiles each player's own policy independently. Alice remains silent; Bob
retains `q` after silence and guesses correctly after disclosure.
`target_sequential_equilibrium` proves an actual target SE whenever

```text
for each secret bit x: 1 - D <= Pr_q(guess = x).
```

The condition is checked at Alice's information after learning her bit.
`all_source_profiles_implemented` therefore implements every source profile
when `D >= 1`; `fair_sequential_equilibrium` needs only `D >= 1/2` for fair
guessing. `compile_initialized_state_law` preserves the joint terminal state,
including the secret, guess and absence of disclosure; `compile_payoff_law`
preserves the actual payoff-vector distribution, including target deductions.

[AmbientEnforcementThreshold.lean](../GameTheoryExtensionsTests/AmbientEnforcementThreshold.lean)
proves necessity against **every target assessment**, requiring only the same
joint secret/guess law. For `D >= 0`, `retained_law_implementable_iff` gives
exactly the bitwise condition above; `fair_law_implementable_iff` and
`all_source_laws_implementable_iff` give the sharp thresholds `1/2` and `1`.
`no_unpenalized_fair_law` rules out implementation even of the fair source law
at `D = 0`. These characterize which source laws have target SE extensions;
they do not assert equality of the complete source and target equilibrium
outcome sets at the thresholds.

For the strict bound `D > 1`, `strict_deposit_silence` forces every sequentially
rational target assessment to remain silent at both Alice types.
`strict_deposit_reflects_equilibrium` then gives a source SE with the same full
initialized state law and net payoff-vector law. Together with the forward
compiler, this gives exact SE outcome-law correspondence for this fixed game
under strict collateral. It does not identify off-path beliefs or strategies.

This supplies a genuine upper edge for this fixed game with automatic
enforcement. It does not implement a monitor, reporting service or blockchain
escrow. Disclosure remains legal in the target and occurs in trembles; the
receiver responds rationally after learning the bit. Extending the theorem to
strategic reporters must also establish their rational behavior and one common
consistent assessment. Preserving initialized game results does not require
preserving source ignorance after an unexpected disclosure.

## Audit of the actual selective-association witness

The checked native witness proceeds as follows:

1. Alice's first response creates a Boolean candidate and attaches its opening
   certificate, before a source binding has selected that candidate.
2. The passive observation rule lets Bob see that first envelope; Carol sees
   no such pending envelope.
3. At the reserved binding opportunity Alice resubmits the same immutable
   candidate without evidence. The accepted association now links the earlier
   certificate to the game binding.
4. Later ordinary openings and the program's declared settlement determine
   payoffs. The profitable disclosure uses a legal raw response, not a forged
   certificate.

The operational and payoff proofs are in
[SelectiveAssociationNative.lean](../VegasTests/SelectiveAssociationNative.lean),
[SelectiveAssociationNativeDeviation.lean](../VegasTests/SelectiveAssociationNativeDeviation.lean)
and their companion modules. They contain no punishment service.

The checked [monitor experiment](../VegasTests/DisclosureMonitoring.lean)
makes the access distinction precise. `pending_certificate_detected` shows
that the network-input alarm sees the early certificate while the ledger alarm
does not. `certificate_free_inclusion_keeps_gap` retains this distinction
after the actual certificate-free binding inclusion, using the first five
service instructions and a silent Bob response. `input_alarm_ignores_readers`
proves that the input alarm does not need a record of private readers.

This alarm reads the complete network input record exposed to the scheduler.
That access is stronger than a contract's ledger view or an ordinary player's
partial observation. `uninformed_player_same_input` and
`no_uninformed_player_detector` show that Carol's complete current player input
cannot distinguish the certified prefix from an uncertified submission, even
though Bob has received evidence in the former. These alarms detect explicit
carried certificates, not all disclosures: `no_alarm_for_uncertified_submission`
is not a proof that the submitted message conveys no information. The recorded
broadcaster is ideal provenance, not a concrete signature proof. The experiment
implements neither a watcher, an accountable receipt, nor escrow slashing.

The intended watchdog uses **two ordinary observation mechanisms**: the ledger
for included packets, and the same passive pending-message rule available to
players. It does not require the scheduler's complete input record. In the
existing runtime an activation samples pending identifiers, and `learn` retains
the selected fresh packets from other authors in that observer's `leaked`
list. Both that list and the ledger belong to its ordinary player view.
Observing an offending packet can therefore supply report material even when
it is never included. Carol's indistinguishability result concerns the sample
in that specific prefix; it does not rule out a watchdog that receives the
packet.

[MessageMonitoring.lean](../Interaction/MessageMonitoring.lean) makes this
minimal interface explicit: `PlayerView.reports` filters the retained leaked
packets and ledger using a packet predicate. `mem_reports` characterizes its
report material exactly; `reports_learn_selected` detects a selected fresh
foreign packet satisfying the predicate. `reports_learn` and
`reports_includePending` preserve existing reports under a fixed predicate,
including after a packet leaves the pending pool. Another observer's private
sample does not alter them (`reports_learn_other`). These theorems concern
observed material, not its selection probability or contractual liability.

[MessageMonitoringProbability.lean](../Interaction/MessageMonitoringProbability.lean)
maps the actual observation kernel through `learn` and the report filter.
`sampling_le_report` bounds the probability of retaining a specific offending
packet. Compliant leaked, ledger and pending packets give the point-mass empty
report law (`reportLaw_eq_pure_nil_of_compliant`). `sampling_delivery_lower`
composes a sampling lower bound `p` with a delivery lower bound `q` conditional
on each supported nonempty report, obtaining `p * q`. Delivery can depend on
the report: independence is unnecessary. These are fixed-snapshot results;
an execution-wide sender-conditional guarantee must also establish activation
and applicable bounds at the sender's information set. To infer no sanctions
from no reports, adjudication must reject the empty report.

The compiler-specific checker lives in
[ReactiveConformance.lean](../Vegas/Pending/ReactiveConformance.lean).
Legitimate opening packets may carry a matching certificate. The checker
rejects certificates on commitments, withholding and malformed calls, and
mismatched certificates on openings. `reactive_decision_submission_permitted`
checks every compiled graph action, including legal source deviations, against
arbitrary emission states and known packets. `no_grant_no_transmission` checks
that the prescribed compiler sends nothing without a service grant.

[PassiveDisclosureMonitoring.lean](../VegasTests/PassiveDisclosureMonitoring.lean)
uses that checker on the actual native witness. Bob's ordinary observation
contains the offending certified commitment while the ledger does not; his
report persists after the separate certificate-free binding is included.
A passive sample at Carol's information position reports it with exactly the
specified probability. This does not insert a new observer into the game or
change Carol's actual strategy. The checker is deliberately only an evidence
shape check: an ordinary early opening without a certificate is still allowed
by it. Full protocol conformance needs a separate timing and information
argument.

Using the same mechanism does not give the watchdog the recipient's sample.
`ObservationRule` may depend on the observer, and each activation draws its
own sample. A positive enforcement result needs a lower bound on receiving,
retaining and successfully reporting evidence, conditional on the sender's
information when choosing the violation. It also needs timely watchdog
activation. An average chance of seeing traffic is insufficient if the sender
can identify opportunities when observation or reporting is unavailable.
The checked scheduler-obliviousness lemmas hide samples from the scheduler;
they alone establish no positive monitoring rate.

Retaining a packet preserves its contents, not a publicly verifiable arrival
timestamp or the identity of its latest rebroadcaster. Packet conformance,
authentication, report timing and the account charged remain separate checks.
A public report included before release can establish early availability;
ordinary passive observation alone does not establish that public fact.

A monitor checking only already-associated source facts also misses the
candidate's early certificate. A possible service could retain a report and
link it to the eventual association, or assign custody liability to candidates
at enrollment. Both need escrow locked until adjudication. Punishing unrelated
candidates would impose a broader communication policy.

Including the report before release could prove early availability without
trusting a claimed private receipt time. This needs timely inclusion and still
does not identify the original transmitter, especially after witness or key
sharing. The current ideal evidence interface implements neither these
receipts nor a cryptographic attribution proof.

## What a bounty must add

A reporter must prefer reporting after accounting for its bounty, fees,
verification costs, lost information advantage, retaliation and enforceable
side contracts. A reportable proof does not establish this incentive. Refunds
through self-reporting or jointly controlled accounts count against the
sender's net loss; externally funded rewards also require protection against
fabricated and repeated claims. These belong in the reporter game before a
fixed reporting probability is assumed.

There are relevant cryptographic precedents, with narrower models.
Ning, Dang, Hou, and Chang use share deposits and informer rewards for early
release, and address framing by ensuring the dealer cannot simply manufacture
another participant's reportable share. Their stated communication model
restricts cross-clique sharing to a public bulletin and bounds mutually
sharing cliques; it is not unrestricted private collusion. This directly
supports testing origin and communication assumptions, rather than treating a
bounty as a universal solution.
[Keeping Time-Release Secrets through Smart Contracts, Sections 3.1--3.3](https://eprint.iacr.org/2018/1166)

Kelkar, Ganesh, Partap, Bonneau, and Weinberg study cryptographically provable
whistleblowing together with smart collusion, where conspirators can enforce
penalties against defectors. They establish limitations even with anonymous
whistleblowing and identification of colluders, as well as positive results
under their stated financial assumptions. This reinforces the need to specify
which collateral and counter-incentives the model permits. It does not provide
an SE theorem for the Vegas communication service.
[Breaking Omerta (2025)](https://eprint.iacr.org/2025/1582)

## Next step and stopping point

The checked automatic-enforcement experiment retains every source profile and
ordinary action, with exact SE outcome-law correspondence under `D > 1`.
The native observation audit and permitted
signaling experiment identify independent gaps in implementing enforcement.
The next focused experiment should replace the debit oracle with a strategic
report and adjudication: first exhibit failure when reporting is unprofitable
or monitor absence is known to the sender, then prove a conditional threshold.

Keep the optional layer outside the production tower until a concrete receipt,
observation and reporting service supplies the enforcement used by its upper
edge. Enforcing a single prescribed strategy is a separate goal from retaining
the source game's legal deviations.

Deferred implementation note: whether miner incentives support participating
in this monitoring, and whether Ethereum supplies the required observation,
reporting and escrow interface, remain questions for later investigation.
Neither economic participation nor implementation feasibility is proved or
assumed to follow from the current experiments.
