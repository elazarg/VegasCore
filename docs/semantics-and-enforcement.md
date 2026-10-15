# Semantics, compiled output and enforcement

Status: design note. It records where each part of the development lives, how
the compiler meets each kind of deviation, which combinations carry checked
results, where the code and the paper disagree with a single coherent story,
and the decisions needed to reach one semantics with Nash and sequential
equilibrium (SE) results. Plans here are proposals until the project owner
approves them.

## 1. Layers

Several distinct things are easy to run together under words such as
"runtime" or "ledger". They change for different reasons and are justified
differently.

| Layer | What it is | Chosen by | In the code |
| --- | --- | --- | --- |
| Source semantics | What a program means, including what a failure means | Language design | [`SourceProgram`](../Vegas/Source) execution: a failure is a `Result` value and play continues |
| Analysis views | Games derived from a program for the designer to solve | Language design | The intended game (`Setup.intendedModel`, a menu restriction); payoff rewrites `forfeitUtility` and `exclusionUtility` ([Forfeit](../Vegas/Source/Forfeit.lean)) |
| Intermediate representation | The typed event graph | Compiler | [Event graph compiler](../Vegas/Compile/EventGraphCompiler.lean) |
| Compiled output | Contract acceptance rules, deadlines, what a failure does on chain, the settlement verdict, deposits, and the honest clients | Compiler | `EventGraphRuntime` handlers; `recoveryApplication`; the settled-record and count verdicts; client profiles |
| Implementation gadgets | Generic protocol mechanisms realizable over a chain, neither specific to Vegas nor inherent to the chain | Implementation, with a refinement obligation | Readiness credentials (`PublicView.tokenFor`), opening certificates (`WitnessedSubmission.emit`), the audit or watcher service |
| Chain model | Accounts and signatures, a pending pool, inclusion, clock, contract execution | Given | The [`Interaction`](../Interaction) layer: `MessageNetwork`, `ReactiveApplication`, schedulers |
| Environment assumptions | What the chain and its operators are assumed to do | Stated hypothesis | Builder contract or calendar, observation rule, audit coverage, randomness beacon |

Gadgets deserve their own layer. A readiness credential binds a packet to the
public completion of its prerequisites; on a chain it would be a reference to
the block or state that completed them, which survives only to finality. A
commitment with an opening certificate is a cryptographic gadget. The audit is
a reporting service with its own incentives. None of these is specific to
compiling Vegas, and none is provided by a chain as such. Each needs a
refinement argument of its own, and each can fail independently: reorganization
invalidates credentials, and private relays defeat the audit.

In the code, gadgets and the compiled contract share the application layer:
`ReactiveApplication.packet` forms the emitted packet, including its token, and
the same application supplies the contract handler. The forced-exit contract
uses this to withhold the token from calls for an exited owner's events
(`RecoveryState.emit`). Draining completes those events, so they would carry no
token anyway, but the layering lets a contract rule change a gadget's output.

## 2. Enforcement responses

The compiler meets a deviation in one of the following ways. Each has a
different cost and a different effect on the source.

| Response | Mechanism | Cost | Effect on the source |
| --- | --- | --- | --- |
| Prevent | The contract or a gadget rejects it | None at runtime; a gadget refinement obligation | None: the deviation has no outcome |
| Attribute from the public record | The settled record names the culprit (an expiry, a failed reveal) | Collection is certain; the response rewrites the game off-path (forced exit) or prices it (forfeit) | The response is part of the semantics or of an analysis view |
| Attribute from signed evidence | An authentic signed packet proves the deviation | Collection only with probability $p_i$; deposits scale with $1/p_i$ and must be locked | None if deterred, apart from the deposit hypothesis |
| Expose | The deviation is a source move priced by the program | The programmer must specify its price | The source game contains it |
| Assume | A stated property of the chain or its operators | A model assumption | None |
| State as a limitation | Non-attributable channels | Weakens the claim | The theorem is forward-only or excludes it |

Prevention removes only a deviation's effect on the record. A prevented packet
can still carry information, through the pending pool and the observation rule,
so information deviations need a second, evidence-based response. This is why
the audit forbids packets the contract would reject anyway.

## 3. Deviation inventory

"Plain" is the compiled contract in which a failure is recorded and play
continues, with the settled-record verdict (`SettledRecord.Permits` plus binding
omissions). "Forced exit" is the contract of `recoveryApplication` with the
count verdict (`CountPermits`).

| Deviation | Attribution | Plain contract | Forced-exit contract |
| --- | --- | --- | --- |
| Silence at a binding (missed binding) | Public record | Charged as an omission; no source counterpart, since source commitments cannot fail | The owner exits |
| Silence at a reveal | Public record | Exposed: priced by the program's failure branch; in the intended game, by a forfeit | The owner exits |
| Guard-violating or unopenable binding | Public record, at the completing reveal | Becomes a failed reveal; as above | The owner exits at the failed reveal |
| Premature packet | Prevented by the credential; signed evidence | Rejected; forbidden | Rejected; forbidden |
| Packet for another player's event, or malformed | Prevented; signed evidence | Rejected; forbidden | Rejected; forbidden |
| Competing or duplicate packets | Signed evidence | The contract accepts the first; extra packets forbidden | Extra packets forbidden; the first well-formed packet per event is free |
| Commitment carrying its opening certificate | Signed evidence (an information deviation) | Forbidden | Forbidden |
| Late send after the protected turn | Under the builder contract, non-inclusion of an owner's sole packet witnesses a late send | On the calendar every owner packet is included; otherwise a dropped packet is forbidden as unaccepted | Not charged; a dropped opening expires and the owner exits |
| Packets after exit | Record effect prevented; information by signed evidence | Not applicable | Rejected by the contract; every such packet is forbidden, and the charge still applies after exit |
| Choice among one's activations (timing) | Not attributable | Limitation: the result is forward-only | Same |
| Off-chain relays, private channels, fee fields | Not attributable | Limitation; audit coverage presupposes audited communication | Same |
| Builder censorship, bribery, strategic ordering | Not a player deviation | Assumption: non-strategic builder with a known law | Same |
| Biased or withheld randomness | Not a player deviation | Assumption: an unbiasable live beacon | Same |
| Sharing secrets or signing keys | Not attributable | Limitation: the cryptographic refinement must account for it | Same |

The free first packet does not leave late sending unpunished. A dropped late
opening expires, and expiry forces exit at the exit payoff. A further charge
would add an expected cost whose size the builder sets after the deposit is
fixed. That cost can lie between two types' continuation values and make late
sending type-dependent, which is the obstruction recorded in
[the commit–reveal note](se-preservation-commit-reveal.md), Section 7.

After exit, "no further moves" is a fact about the record and an incentive fact
about the network. The contract ignores an exited player's packets, but the
chain lets it send, and a leaked opening with its certificate is verifiable
disclosure. Every such packet is forbidden by the count verdict. The exited
player's payoff is the exit payoff minus any charge, so every emission lowers
its expected payoff by at least $p_i d_i$, and silence strictly dominates. The
exit payoff appears in the deposit condition of the forced-exit theorem for this
reason. No lemma currently states this dominance.

## 4. What each guarantee needs

| Guarantee | Needs | Does not need |
| --- | --- | --- |
| ε-Nash correspondence | Prevention, exposure, timely service, honest first-turn clients | Audit coverage, deposits (zero is allowed), forced exit, independence |
| Sequential equilibrium | Additionally: evidence-based deterrence with coverage and deposits, and either a calendar or forced exit with a free first packet; under forced exit, independent private inputs | Value-blind builders or content-blind leaks |

The Nash correspondence holds because, against first-turn clients, every native
policy of one player has the outcome law of a source deviation whose bindings
may fail, and failure buys nothing. SE must also be rational after traffic no
source policy produces, which is what the audit and forced exit pay for. This is
the analogue of a threat model: a stronger preserved notion requires a costlier
compiler.

## 5. Checked combinations

| Result (paper label) | Analysis target | Compiled output | Environment | Main Lean declaration |
| --- | --- | --- | --- | --- |
| Nash (1) (`thm:nash`) | Source game | Plain contract, any authentic verdict, nonnegative deposits | Any builder meeting `AsyncContract` | `Vegas.Paper.async_first_turn_nash_iff` |
| Nash (2) | Source game | Plain contract, settled-record verdict | Calendar | `Vegas.Paper.source_audited_raw_nash_iff` |
| Nash (3) | Intended game via forfeit | As (1) or (2) | As (1) or (2) | `Vegas.Paper.intended_async_first_turn_nash`, `Vegas.Paper.intended_audited_raw_nash` |
| SE (`thm:sequential`) | Source game | Plain contract, settled-record verdict | Calendar | `Vegas.Paper.source_audited_raw_sequential_equilibrium` |
| SE (`cor:intended-ledger`) | Intended game via forfeit | As above | Calendar | `Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium` |
| SE (`thm:recovery`) | Intended game | Forced exit, count verdict | Any builder meeting `Recovery.AsyncContract`; independent private inputs | `Vegas.recovery_intended_raw_sequentialEquilibrium_preserved` |
| SE, conditional | Intended game with exit payoff | Plain contract with exit payoff, count verdict | Timely builder | `Vegas.onePacket_intended_raw_sequentialEquilibrium` (assumes certificates; superseded by the row above) |
| Negative (`thm:late-leak`) | Intended game with forfeit | Failure continues; dropped late openings charged | An abstract game, not the ledger | `Vegas.Paper.late_leak_intended_outcome_not_preserved` |
| Intended to source (`thm:intended`) | Intended to source game | None | None | `Vegas.Paper.intended_sequential_equilibrium` |

## 6. Discrepancies

These must appear in the paper as assumptions, future work or TODOs until
resolved.

1. **Nash and SE concern different compiled outputs.** The Nash correspondence
   under timely builders is proved for the plain contract. The SE result is
   proved for the forced-exit contract with the count verdict. No result
   covers Nash for the forced-exit contract.
2. **Forced exit is not a source semantics.** The source has no operational
   exit. `exclusionUtility` fixes a failing player's payoff but lets it keep
   acting, and its later publications still affect others' payoffs; the
   forced-exit contract instead fails the exited owner's later events. The SE
   theorem starts from the intended game, where nothing fails, so it is
   unaffected, but the two forms disagree off-path.
3. **Missed bindings have no source counterpart.** Source commitments choose
   values only, so a missed binding is handled outside the source: charged as an
   omission by the plain contract, an exit under forced exit.
4. **Two audit-service models.** The settled-record audit is an authentic
   sampler with coverage $p_i$ over the complete traffic (`sourceServiceAudit`).
   The count audit is an `EvidenceReportService` with separate observation and
   conditional delivery rates inside a challenge window (`CountEvidenceCoverage`).
   The deposit conditions differ accordingly.
5. **Gadget and contract share a layer.** The forced-exit contract changes token
   attachment (Section 1).
6. **Naming.** "Runtime", "recovery runtime", "exclusion" and "forced-exit ledger"
   name a choice of compiled contract as if it were a chain. The chain model is
   the same in every result; the calendar is an environment assumption.

## 7. Toward one semantics

Target: one source semantics with forced exit, one compiled contract and
verdict, one audit-service model, and Nash and SE results for that combination.
Other combinations remain as design alternatives, not as the results.

Decisions to make:

- **Exit in the source.** A failed move ends its owner's participation: the
  owner's later moves fail without a choice, and its payoff is a fixed exit
  payoff. The others continue, and their utilities still read the program's
  failure results, so `Result` stays meaningful. The checked source properties
  (publication accounting, guard safety) and the source–graph correspondence
  must be re-established.
- **Failing commitments.** Whether the source gains a failing commitment move,
  or a missed binding is modelled directly as exit. With exit in the source, the
  value interface and the omission charge become unnecessary.
- **Intended game.** With exit at a payoff no higher than every intended payoff,
  departures from the intended menus are unprofitable without a forfeit
  (`intended_exclusionSource` is the payoff form of this). The forfeit becomes
  an alternative.
- **Nash under forced exit.** Adapt the first-turn client argument to the
  forced-exit contract and the count verdict.
- **Source and contract exit agree.** An equivalence between the source-level
  exit and the contract's drain, so that the SE theorem can be stated from the
  source semantics.
- **One audit-service model and one deposit condition.**
- **Gadget layer.** Readiness credentials, certificates and the audit as a
  separate layer between the chain model and the compiled contract, each with
  its stated refinement obligation.
- **Named facts.** Post-exit dominance; that a dropped owner packet witnesses a
  late send under the builder contract.
- **Alternatives.** The calendar, the forfeit, the plain contract and the
  settled-record verdict move out of the main results, with the reasons they
  were not chosen recorded here.

Open questions:

- Whether the free first packet should apply only to openings, or also to
  bindings.
- Whether the exit payoff is per player or may depend on public history before
  exit.
- How the gadget layer should be stated in the paper: as part of the ledger
  model, or as explicit assumptions about an implementation over a chain.
