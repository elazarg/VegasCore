# Semantics, compiled output and enforcement

This note has three parts. Keep them apart when editing.

- **Part I, insights.** Facts and arguments about compiling commit–reveal games
  to a ledger that hold whatever design we choose. Each carries a status tag.
- **Part II, current state.** What the code defines and proves now. The paper
  must be faithful to this part, including its discrepancies.
- **Part III, proposals.** The design we intend to move to, its decisions and
  open questions. Nothing here holds yet. Proposals become current state only
  when implemented and checked.

Status tags:

- **[checked]** A Lean result at the cited declaration.
- **[argued]** An argument made here or in a linked note, not checked in Lean.
- **[conjecture]** Plausible, with no argument yet.
- **[assumption]** A modelling or realism assumption that must be stated.

## Part I. Insights

### I.1 Layers

[argued] Several distinct things are easily run together under words such as
"runtime" or "ledger". They change for different reasons and need different
justifications.

| Layer | What it is | Justified by |
| --- | --- | --- |
| Source semantics | What a program means, including what a failure means | Language design |
| Analysis views | Games derived from a program for the designer to solve, such as an intended game or a payoff rewrite | Language design |
| Intermediate representation | The typed event graph | Compiler correctness |
| Compiled output | Contract acceptance rules, deadlines, what a failure does on chain, the settlement verdict, deposits, honest clients | Preservation theorems |
| Implementation gadgets | Generic protocol mechanisms realizable over a chain, neither specific to Vegas nor inherent to the chain | A realization argument per gadget |
| Chain model | Accounts and signatures, a pending pool, inclusion, clock, contract execution | Given |
| Environment assumptions | What the chain and its operators do: inclusion service, observation, audit coverage, randomness | Stated hypotheses |

A failure semantics is a choice in the first two layers or in the compiled
output, never in the chain model. A builder schedule (such as a calendar) is an
environment assumption, never a property of the compiled output.

### I.2 Gadgets are ideal functionalities

[argued] Gadgets are best stated in the style of a hybrid model: the theorems
assume an ideal functionality, and realizing it is a separate claim of the form
"a construct with these properties is implementable over a chain". Each gadget
needs its functionality, a realization sketch, and its known failure modes.

| Gadget | Ideal functionality | Realization sketch | Known failure modes |
| --- | --- | --- | --- |
| Readiness credential | A packet is bound to the public record that made its event ready | Cite the block or state that completed the prerequisites; the contract checks ancestry and readiness | Valid only after finality; reorganization invalidates it |
| Commitment with opening certificate | Hiding, binding, verifiable opening | Hash or Pedersen commitment and its opening | Non-malleability; voluntarily shared openings or keys |
| Audit | See I.6 | See I.6 | See I.6 |

### I.3 How a compiler can meet a deviation

[argued] Every deviation the target admits is met in one of these ways.

| Response | Mechanism | Cost | Effect on the source |
| --- | --- | --- | --- |
| Prevent | The contract or a gadget rejects it | A gadget realization obligation | None: the deviation has no outcome |
| Attribute from the public record | The settled record names the culprit, for example an expiry | Collection is certain | The response belongs to the semantics or an analysis view |
| Attribute from signed evidence | An authentic signed packet proves the deviation | Collection only with probability $p_i$; deposits of order range$/p_i$ locked | None if deterred, apart from the deposit hypothesis |
| Expose | The deviation is a source move priced by the program | The programmer prices it | The source game contains it |
| Assume | A property of the chain or its operators | A model assumption | None |
| State as a limitation | A non-attributable channel | A weaker claim | The result excludes it or is forward-only |

Consequences:

- [argued] Prevention removes a deviation's effect on the record, not the
  information it carries. A rejected packet can still be shown to other players
  through the pending pool. Information deviations therefore need an
  evidence-based response even when the contract rejects the packet.
- [argued] The certainty of attribution decides the money mechanism. A fault in
  the public record can be priced exactly. A fault proved only by sampled
  signed evidence needs a deposit scaled by $1/p_i$.
- [argued] Non-attributable channels (timing among one's own activations,
  private relays, fee fields, shared secrets) can be neither prevented nor
  deterred. They are limitations, not obligations.

### I.4 Which deviations a source language must contain

[argued] A source language needs to expose exactly the deviations the
implementation can neither prevent nor deter. For commit–reveal on a ledger
that is silence, at a commitment or at a reveal. A guard-violating value or an
unopenable binding is indistinguishable from silence by the time anyone can
tell, at the reveal. Malformed, premature, duplicate and evidence-bearing
packets are prevented or deterred. Everything else is a limitation or an
assumption.

### I.5 What the failure response must satisfy

- [argued] A dropped late opening is evidence of a deviation. Under a builder
  that includes an owner's sole timely packet, non-inclusion of that packet
  witnesses a late send.
- [argued] Charging that evidence can nevertheless break sequential equilibrium.
  If the late sender is already punished through its failure, an extra charge
  adds an expected cost whose size the builder sets after the deposit is fixed.
  That cost can fall between two types' continuation values and make late
  sending a type-dependent choice. See
  [the commit–reveal note](se-preservation-commit-reveal.md), Section 7.
- [argued] For sequential equilibrium under builders that may include late
  packets, a failing player's payoff must depend neither on its type nor on the
  route to failure. Otherwise the timing of a late opening becomes a
  type-dependent choice. The counterexample with a forfeit and continued play is
  [checked] (`Vegas.Paper.late_leak_intended_outcome_not_preserved`).
- [assumption] A contract controls money, not what a player values. A
  type-independent failure payoff is implementable only if a player who has
  failed values nothing in the game beyond what it is paid: private values
  without externalities on failure outcomes, with utility quasi-linear in money.
  Private valuations for bidding fit, since a failing bidder receives no item.
  Allocative externalities (caring who wins), public outcomes the failed player
  still values, and allocations received before failure do not fit.
- [argued] After a player stops participating, the chain still lets it send,
  and a leaked opening with its certificate is verifiable disclosure. "No
  further moves" can therefore hold mechanically only for the record. For the
  network it must hold by deterrence: if every such packet is forbidden and the
  charge still applies, silence strictly dominates.

### I.6 The audit

[argued] What the preservation proofs need from an audit, independently of who
runs it:

- **Authenticity.** Only packets actually sent and signed are reported.
  Signatures provide this.
- **Coverage.** Each forbidden packet of player $i$ is reported with
  probability at least $p_i$, whatever the rest of the traffic.
- **Timeliness.** Reports land in a window before settlement. Reports are
  transactions, so this is a second inclusion-service assumption.
- **Neutrality.** Collected deposits are burned, so no player gains from
  another's violation.
- **No feedback into play.** No player observes reports during play.

Candidate auditors and their realism:

- **Players.** They see exactly the packets the observation rule shows them, so
  they are natural reporters. If players receive bounties, their off-path
  payoffs depend on others' violations, which changes the game being analyzed.
- **Third parties with bounties.** They preserve neutrality for the players.
  Coverage depends on what they can observe.
- **A service of the contract owner.** Plausible, but trusted.
- **Limits.** Private relays to the builder evade public watchers. A small $p_i$
  means large locked deposits.

[conjecture] A forbidden packet matters only if some player observes it or it
reaches the record. Coverage of observed or included packets may then suffice,
instead of coverage of all traffic. This would let coverage be derived from the
observation rule.

### I.7 Guarantees cost different amounts

[argued] Different preserved notions need different compilers, as stronger
security criteria need stronger compilers in secure compilation. A Nash
comparison fixes the opponents' policies, and against honest clients that
decide at their first opportunity every native policy of one player has the
outcome law of a source deviation whose bindings may fail. If failure buys
nothing, no audit is needed. Sequential equilibrium must also be rational after
traffic no source policy produces, which requires deterrence of information
deviations and a failure response as in I.5. The current results instantiate
this (II.3).

## Part II. Current state

### II.1 Where things live in the code

| Layer | Code |
| --- | --- |
| Source semantics | [`SourceProgram`](../Vegas/Source) execution: a failure is a `Result` value and play continues |
| Analysis views | The intended game (`Setup.intendedModel`); payoff rewrites `forfeitUtility` and `exclusionUtility` ([Forfeit](../Vegas/Source/Forfeit.lean)) |
| Intermediate representation | [Event graph compiler](../Vegas/Compile/EventGraphCompiler.lean) |
| Compiled output | `EventGraphRuntime` handlers and deadlines; the forced-exit contract `recoveryApplication`; the settled-record verdict (`SettledRecord.Permits` with binding omissions, `sourceServiceAudit`) and the count verdict (`CountPermits`, `Recovery.countAudit`); client profiles |
| Gadgets | Readiness tokens (`PublicView.tokenFor`) and opening certificates (`WitnessedSubmission.emit`), formed by the application's `packet` function |
| Chain model | The [`Interaction`](../Interaction) layer: `MessageNetwork`, `ReactiveApplication`, schedulers, observation rules |
| Environment assumptions | `AsyncContract` and `Recovery.AsyncContract` (timely builders), calendar rosters, observation-rule finiteness, audit-service coverage |

There are two compiled contracts on one chain model:

- **Plain.** A failure is recorded and play continues. Its verdict is the
  settled-record verdict, which forbids any packet the final record does not
  accept with canonical content and separately charges a binding omission.
- **Forced exit.** An owned expiry, or an accepted opening whose result is
  failure, adds its owner to an exit set. The exited owner's later events are
  completed as failures, and packets for them get no readiness token and are
  rejected (`RecoveryState.emit`, `RecoveryState.handle`). Its verdict is the
  count verdict: a packet is permitted only if it has a valid token, a correct
  call by the right owner, and is its sender's first packet for its event; the
  verdict reads no inclusion. The exited player's payoff is a fixed
  `excludedPayoff`, minus any charge (`recoveryExclusionBase`).

### II.2 Deviations under the current contracts

| Deviation | Plain contract | Forced-exit contract |
| --- | --- | --- |
| Silence at a binding | Charged as an omission; no source counterpart, since source commitments choose values only | The owner exits |
| Silence at a reveal | Exposed: priced by the program's failure branch, or by a forfeit in the intended game | The owner exits |
| Guard-violating or unopenable binding | A failed reveal, as above | The owner exits at the failed reveal |
| Premature, misaddressed or malformed packet | Rejected; forbidden | Rejected; forbidden |
| Competing or duplicate packets | The first valid inclusion is accepted; the others forbidden | All but the first well-formed packet per event forbidden |
| Commitment carrying its opening certificate | Forbidden | Forbidden |
| Late send after the protected turn | On a calendar every owner packet is included; elsewhere a dropped packet is forbidden as unaccepted | Not charged; a dropped opening expires and the owner exits |
| Packets after exit | Not applicable | Rejected; every such packet is forbidden, and the charge applies after exit |
| Timing, private channels, fee fields | Limitation | Limitation |
| Builder misbehavior, biased randomness | Assumption | Assumption |

The post-exit packet rule holds in the code: every call by an exited owner lacks
a token, commitments must be the sender's own bindings, and openings must come
from the owner. No lemma states the resulting dominance of silence.

### II.3 Checked results

| Result (paper label) | Analysis target | Compiled output | Environment | Lean |
| --- | --- | --- | --- | --- |
| Nash (1) (`thm:nash`) | Source game | Plain contract, any authentic verdict, nonnegative deposits including zero | Any builder meeting `AsyncContract` | `Vegas.Paper.async_first_turn_nash_iff` |
| Nash (2) | Source game | Plain contract, settled-record verdict | Calendar | `Vegas.Paper.source_audited_raw_nash_iff` |
| Nash (3) | Intended game via forfeit | As (1) or (2) | As (1) or (2) | `Vegas.Paper.intended_async_first_turn_nash`, `Vegas.Paper.intended_audited_raw_nash` |
| SE (`thm:sequential`) | Source game | Plain contract, settled-record verdict | Calendar | `Vegas.Paper.source_audited_raw_sequential_equilibrium` |
| SE (`cor:intended-ledger`) | Intended game via forfeit | As above | Calendar | `Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium` |
| SE (`thm:recovery`) | Intended game | Forced exit, count verdict | Any builder meeting `Recovery.AsyncContract`; independent private inputs | `Vegas.recovery_intended_raw_sequentialEquilibrium_preserved` |
| SE, conditional | Intended game with exit payoff | Plain contract with exit payoff, count verdict | Timely builder | `Vegas.onePacket_intended_raw_sequentialEquilibrium` (assumes certificates; superseded by the row above) |
| Negative (`thm:late-leak`) | Intended game with forfeit | Continued play after failure; dropped late openings charged | An abstract game, not the ledger | `Vegas.Paper.late_leak_intended_outcome_not_preserved` |
| Intended to source (`thm:intended`) | Intended game to source game | None | None | `Vegas.Paper.intended_sequential_equilibrium` |

### II.4 Discrepancies

These must appear in the paper as assumptions, future work or TODOs while they
stand.

1. **Nash and SE concern different compiled outputs.** The Nash correspondence
   under timely builders is proved for the plain contract. SE under timely
   builders is proved for the forced-exit contract and the count verdict. No
   result covers Nash for the forced-exit contract.
2. **Forced exit is not a source semantics.** The source has no operational
   exit. `exclusionUtility` fixes a failing player's payoff but lets it keep
   acting, so its later publications still affect others' payoffs; the
   forced-exit contract instead fails its later events. The SE theorem starts
   from the intended game, where nothing fails, so it is unaffected.
3. **Missed bindings have no source counterpart.** They are charged as
   omissions by the plain contract and cause exit under forced exit.
4. **Two audit-service models.** The settled-record audit is an authentic
   sampler with coverage $p_i$ over all traffic. The count audit is an
   `EvidenceReportService` with observation and conditional delivery rates in a
   challenge window (`CountEvidenceCoverage`). Their deposit conditions differ.
5. **A gadget is formed in the contract layer.** The application's `packet`
   function forms readiness tokens, and the forced-exit contract changes it.
   Draining completes the affected events, so they would carry no token anyway.
6. **The exit payoff is a utility.** `excludedPayoff : Player → ℝ` fixes the
   exit utility directly; the realism assumption of I.5 is not stated.
7. **Naming.** "Runtime", "recovery runtime", "exclusion" and "forced-exit
   ledger" name a compiled contract as if it were a chain.

## Part III. Proposals

### III.1 Target language: commit–reveal with exit

Following I.4 and I.5: pure commit–reveal, plus one way to fail.

- Every owned move, a commitment or a reveal, may instead fail. A failure is
  public, ends its owner's participation, and pays the owner a fixed exit
  payoff.
- The other players continue. Payouts may read who exited and at which move.
  A publication is a value or "its owner exited here".
- The exit payoff may default to the owner's minimum over intended outcomes, so
  that a programmer writes pure commit–reveal and, optionally, the survivors'
  payouts after an exit (refunds by default).
- The intended game is the game without failures. With an exit payoff no higher
  than every intended payoff, no forfeit is needed.
- Missed bindings become exits, which removes the value-only commitment
  interface and the omission charge.

### III.2 Target development

One source semantics (III.1), one compiled contract and verdict, one audit
model, and Nash and SE results for that combination. Steps:

1. Operational exit in the source semantics; re-establish publication
   accounting, guard safety and the source–graph correspondence.
2. Nash correspondence for the forced-exit contract and the count verdict,
   adapting the first-turn client argument.
3. An equivalence between source-level exit and the contract's draining, so
   that the SE theorem is stated from the source semantics.
4. One audit-service model and one deposit condition.
5. Gadgets as a separate layer between the chain model and the compiled
   contract, each with its stated functionality.
6. Named lemmas, when the code is stable: post-exit dominance of silence; that
   a dropped owner packet witnesses a late send.
7. The calendar, the forfeit, the plain contract and the settled-record verdict
   become documented alternatives, with the reasons they were not chosen.

### III.3 Open questions

- Whether the free first packet should cover bindings as well as openings.
- Whether the exit payoff is per player or may depend on the public history
  before exit.
- Whether the observed-coverage conjecture of I.6 holds, and whether players,
  third parties or a service should audit.
- How the paper should present gadgets: inside the ledger model, or as explicit
  ideal-functionality assumptions.
