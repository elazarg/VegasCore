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

The checked finite sender/receiver class supplies the first edge with
specified utility charges. The Boolean experiment also gives sharp thresholds
and a converse. The second edge must implement the first edge's information
and enforcement powers. Ordinary pending-message sampling supplies some
evidence without giving the watchdog access to the complete execution history.

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
`alarm_zero_iff` requires silence at every observation in the support of `mu`, even
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
For a specified nonnegative fine, `exists_sound_alarm_for_penalty_iff` gives
the sharp condition: detectable mass times the fine must cover the gain.
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

## A checked class of sequential-equilibrium extensions

The reusable construction is in
[DisclosureEnforcementEquilibrium.lean](../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean).
Nature draws a private state with an arbitrary finite prior. The sender knows
that state; the source gives only the receiver a decision, drawn from a finite
nonempty action set. Both players' payoffs are arbitrary functions of the state
and receiver decision. The target adds an optional authenticated disclosure
before that same receiver decision.

The compiler retains the source receiver law after silence and chooses a
receiver-optimal action after disclosure. It sends no disclosure on prescribed
play. `source_equilibrium_implemented` starts from **any source SE assessment**
and constructs a target SE with identical complete initialized state and net
payoff-vector laws, provided the sender's charge at each private state covers
its gain from the receiver's disclosed response. The translation is playerwise.
The proof uses the existing SE definition, whole-policy continuation deviations,
and one common fully mixed sequence. It checks the receiver's rational response
after a disclosure, including off-path disclosures.

Two ways of setting charges have different quantifiers:

- `requiredCharge` is the least nonnegative charge satisfying the sender
  condition for a chosen source decision law and disclosed response.
  `every_source_equilibrium_enforceable` gives some suitable response and charge
  for every source SE. These charges may depend on the selected equilibrium.
- `source_equilibrium_preserved_of_range` uses a bound on the sender's payoff
  range at each private state. The same charges, target game and playerwise
  compiler then work for **every source SE**, without inspecting which source
  equilibrium was selected. The unconditional compiler laws supply the state
  and payoff-law identities.

There is also a checked case where the participants supply the incentive
without a sanction. `source_equilibrium_preserved_constant_sum` assumes that,
at each private state, the sum of sender and receiver payoffs is independent
of the receiver's decision. The receiver's optimal informed response then
minimizes the sender's reward, so `sender_deterrence_of_constant_sum` establishes
deterrence with zero charge. Every source SE therefore extends with the same
state and payoff laws. Zero-sum games are a special case. This is a result for
the specified one-decision class, not arbitrary zero-sum games or Vegas programs.

The prior is represented on its full-support carrier, so no zero-probability
chance states become extra decision sites. `source_consistent_belief` proves
that every consistent source assessment uses the prior at the receiver's
always-reached site; source optimality is derived from its actual SE premise.

This is a finite class of disclosure games, not arbitrary finite games or the
native packet game. It has one informed sender, no separate private receiver
signal, one receiver decision, and only silence versus authenticated full
disclosure. It admits no other communication alphabet, partial evidence or
repeated disclosure. These are substantive restrictions. A monitoring backend
must justify that any further messages or observations have the required
strategic account.

The charge is a utility deduction. A sampled fine can supply its expected
value only after proving the relevant conditional collection law. If reports,
collection outcomes or reporter rewards affect later choices, those effects
must also be included. Substituting a probability times a fine into the charge
formula alone is not a native implementation theorem. The initialized net
payoff-law equality is exact because prescribed play discloses nothing and
incurs no charge.

## Sharp thresholds in the Boolean experiment

The [finite ambient game](../GameTheoryExtensionsTests/AmbientEnforcement.lean)
has a fair secret bit known to Alice. Bob always guesses; both receive one for
a correct guess and zero otherwise. The source hides the bit from Bob and
gives Alice no action. The target additionally lets Alice disclose before
Bob's choice, with automatic deduction `D` from her payoff. Ordinary source
actions are never fined.

[AmbientEnforcementSource.lean](../GameTheoryExtensionsTests/AmbientEnforcementSource.lean)
proves `GameTheoryExtensionsTests.AmbientEnforcement.source_sequential_equilibrium`
for every source policy profile: any
guess distribution `q` is rational against the hidden fair bit. The proof
includes consistent beliefs and a common fully mixed sequence.

[AmbientEnforcementEquilibrium.lean](../GameTheoryExtensionsTests/AmbientEnforcementEquilibrium.lean)
compiles each player's own policy independently. Alice remains silent; Bob
retains `q` after silence and guesses correctly after disclosure.
`GameTheoryExtensionsTests.AmbientEnforcement.target_sequential_equilibrium`
proves an actual target SE whenever

```text
for each secret bit x: 1 - D <= Pr_q(guess = x).
```

The condition is checked at Alice's information after learning her bit.
`all_source_profiles_implemented` therefore implements every source profile
when `D >= 1`; `fair_sequential_equilibrium` needs only `D >= 1/2` for fair
guessing. `GameTheoryExtensionsTests.AmbientEnforcement.compile_initialized_state_law`
preserves the joint terminal state, including the secret, guess and absence of
disclosure; `GameTheoryExtensionsTests.AmbientEnforcement.compile_payoff_law`
preserves the actual payoff-vector distribution, including target deductions.

[AmbientEnforcementThreshold.lean](../GameTheoryExtensionsTests/AmbientEnforcementThreshold.lean)
proves necessity against **every sequentially rational target assessment**, requiring only the same
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

The incentive premise is the sender's **belief-weighted expected loss** at the
decision, including the chance that evidence is accepted and the charge is
collected. A contract need not be able to verify that expectation. The generic
local rationality theorem evaluates it using the assessment's conditional
beliefs; the finite enforcement experiments use specified, known charges.
For standard SE these beliefs must be consistent with the modeled chance and
information structure. Uncertainty about monitor reliability can be modeled,
but arbitrary fear of punishment is not a substitute for that consistency
obligation. A subjective-equilibrium interpretation with different model
beliefs would be a separate theorem.

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

An off-chain pending-message observer supplying evidence to a contract is a
candidate **oracle service** in the blockchain sense. This terminology does
not grant it omniscient observation, trustworthy testimony, or guaranteed
delivery. Those are exactly the interface obligations above.

A reporter must prefer reporting after accounting for its bounty, fees,
verification costs, lost information advantage, retaliation and enforceable
side contracts. A reportable proof does not establish this incentive. Refunds
through self-reporting or jointly controlled accounts count against the
sender's net loss; externally funded rewards also require protection against
fabricated and repeated claims. These belong in the reporter game before a
fixed reporting probability is assumed.

The existing participants may themselves implement enforcement when their
continuation incentives favor reporting or counteraction. This is an
alternative to an external paid watchdog. Competitive interests, including
zero-sum payoffs, already supply deterrence in the finite decision class above.
They do not by themselves establish a profitable feasible report at every
information set in a richer game. Such an
implementation must construct the participants' strategies and consistent
beliefs, and account for any information revealed by a report.

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

## Remaining implementation boundary

The [SE research plan](se-preservation-roadmap.md) orders these obligations and
specifies the first native pilot. The broader routes are alternatives to assess
after that concrete test, rather than additional compiler layers.

The finite sender/receiver class establishes forward SE preservation with
complete state and net payoff-law equality. The Boolean instance also has
exact SE outcome-law correspondence under `D > 1`. Neither result is a
source-to-native preservation theorem.

The direct next obligation is a concrete reporting and adjudication service
whose permitted packet behavior has the source interpretation required by the
equilibrium proof. Sampling supplies evidence; successful collection, liability
and additional observations still need proofs. A strategic reporter additionally
requires its own rationality and consistency argument. The native shape checker
does not yet exclude all additional communication, and the permitted-signaling
experiment explains why simply increasing a sound fine cannot always fix that.

The [sequential enforcement note](sequential-enforcement-design.md) distinguishes
forward extension from reflection and records a proposed broader theorem. That
generalization remains unproved; the implemented theorem is the finite class
specified above.

Keep the optional layer outside the production tower until a concrete receipt,
observation and reporting service supplies the enforcement used by its upper
edge. Enforcing a single prescribed strategy is a separate goal from retaining
the source game's legal deviations.

Deferred implementation note: whether miner incentives support participating
in this monitoring, and whether Ethereum supplies the required observation,
reporting and escrow interface, remain questions for later investigation.
Neither economic participation nor implementation feasibility is proved or
assumed to follow from the current experiments.
