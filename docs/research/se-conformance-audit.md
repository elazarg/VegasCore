# Adversarial audit of monitored source-to-native SE preservation

## Scope and status

Target: every SE of a stated Vegas source class has an SE in the existing
bounded reactive runtime with the same initial-type/result and net-payoff laws.
This is forward preservation; reflection and a fixed playerwise compiler are
additional requirements. No whole native theorem follows from this audit.
Items labelled **candidate** or **test** are obligations, not proved results.

The native menu must retain silence, arbitrary bounded submissions, evidence
requests, replay and passive foreign reads. A conformance restriction describes
the play to implement; sanctions must deter departures in the unrestricted game.
Deleting departures from the menu does not establish the monitored theorem.

## Minimum contract to try

1. **Preserve source choices.** Every admitted source action has an unpunished
   implementation, including withholding, every legal value, and admitted
   irreversible forfeiture. Soundness quantifies over all source policies,
   rather than one selected equilibrium. Do not fine disclosure merely because
   the equilibrium withholds it. The compiler legitimately attaches certificates
   to successful opening calls; [shape conformance](../../Vegas/Pending/ReactiveConformance.lean)
   proves this for every graph action.
2. **Specify refusal and timeout.** State whether silence is the implementation
   of a source refusal or whether a canonical refusal packet is required.
   If missing a deadline incurs a fine, prescribed refusal packets need the same
   delivery guarantee as prescribed openings. Otherwise punishment can alter
   a legal source result. Current completion results do not alone prove this.
3. **Account for early irreversible failure.** Start with source forfeiture,
   or prove its omission for the selected program/backend. The source's later
   withholding opportunity does not supply the earlier continuation identified
   by [IrreversibleFailure](../../GameTheoryExtensionsTests/IrreversibleFailure.lean).
   A watcher cannot certify a private candidate's valid hidden value just by
   inspecting its opaque handle. A validity-proof backend is a separate premise.
4. **Remove representation channels from permitted play.** Fix game instance,
   event, candidate association, packet/evidence form and retry interpretation.
   Every remaining public choice of handle, serial, padding, count or timing
   needs a source interpretation or a proof of strategic irrelevance. Canonical
   handles can address the ideal model; they do not prove a cryptographic
   commitment's randomness or encoding has no usable signaling channel.
5. **Use authenticated context, not current-stage guessing.** Dependencies at
   execution are weaker than dependencies at first submission. The checked
   [authorization contract](../dependency-authorized-submission.md) excludes
   premature executable packets, but its public-history implementation is not
   a ledger-verifiable timestamp. A later observation cannot establish when
   the packet was authored. Checking a delayed lawful packet against only the
   monitor's present stage can falsely flag it.
6. **Close information between source decisions.** Permitted traffic must
   reproduce the source information and remaining choices at every relevant
   decision. A useful candidate is: extra observations become public in the
   source before any further admitted decision can exploit them. Native reads
   remain possible; the claim concerns their effect on continuations. Equal
   final outputs or equal ledger snapshots do not establish this condition.
7. **Retain the service contract.** Fix opportunities and deadlines; use distinct
   unpublished identifiers and at-most-once inclusion, including rejected calls.
   Control traffic-dependent selection and preserve enough opportunities after
   deviations. Local uniformity, authorization and replay invariance are checked;
   their whole-continuation strategic implication remains open.
8. **Make punishment conditional and incremental where needed.** At a player's
   decision, its consistent beliefs must give sufficient expected collectible
   loss for the *whole* first-departure continuation. A mean monitoring rate
   across executions is insufficient. Already collected collateral is sunk:
   later choices require rational continuation repair or further applicable
   incentives, not reuse of the original fine as a new marginal cost.

These are different obligations, not eight compiler flags. Clauses 1--7 must
first establish that permitted native play genuinely implements the source;
clause 8 then concerns extending that restriction to unrestricted native SE.

## What ordinary monitoring can certify

The watchdog may use only its ledger and sampled foreign pending messages.
[MessageMonitoring](../../Interaction/MessageMonitoring.lean) gives report
material and persistence; [the probability adapter](../../Interaction/MessageMonitoringProbability.lean)
composes actual sampling and conditional report-delivery bounds. The
[native test](../../VegasTests/PassiveDisclosureMonitoring.lean) detects the
selective-association packet without reading the network's complete input log.
Neither result supplies sender-conditional coverage over all histories, timely
activation, accountability, adjudication, available collateral or collection.

An included report while the required dependencies are still absent is a
candidate proof of early availability. A late report needs immutable signed
context or another justified origin certificate. The semantic permission test
should remain valid for lawful delayed packets. Existing source guards read
public operands and the proposal, but a deployable historical guard/evidence
checker is still required; the watcher must not read private candidate tables.

A report can itself reveal the secret. If report success, failure, rewards or
fine collection are observed before consequential decisions, they belong in
the continuation game. Replacing these events by an expected terminal charge
needs its own equivalence proof. The
[finite enforcement theorem](../../GameTheoryExtensions/Analysis/Protocol/DisclosureEnforcementEquilibrium.lean)
uses a specified utility charge and explicitly repairs the receiver's response
after disclosure; it is not that equivalence proof.

## Kill tests for candidate assumptions

| Test | Evidence or required experiment | Design consequence |
|---|---|---|
| Readiness, immediate acceptability, no premature reveals | [Native ready-commitment witness](../../VegasTests/ReactiveReadinessRestrictions.lean): the selectively leaked certificate rides on a ready, immediately acceptable commitment. | Readiness alone does not exclude the known information mechanism. |
| Packet shape alone | The shape checker permits ordinary opening bodies with matching evidence, irrespective of their emission stage. | Add context and information obligations; do not claim shape is full conformance. |
| Free lawful field | [MonitoredSignaling](../../GameTheoryExtensionsTests/MonitoredSignaling.lean): a shared private pad permits signaling with identical public message law; complete signaling transcripts also lie in lawful support. | Zero false positives cannot punish this channel, even after the secret is public. |
| Canonical shape but selectable handle or retry count | **Next small native test:** two allowed representations of the same source choice, distinguished by a receiver before its move. Reuse the actual submission/observation prefix. | Reject the contract unless representation is fixed, source-visible, or proved irrelevant. This test is not yet a native SE counterexample. |
| Failed resolution | Current `reactiveResolutionPacket` emits withholding when validation fails. Arbitrary raw openings remain in the menu and can carry plaintext despite failure. | A failure result must not license every raw failed-opening transcript. Classify and account for rejected traffic. |
| Fresh packet changes an old winner | Checked O2 in [the inventory](../spe-obstructions.md); replay and shared transmission opportunities supply O3/O4. | A communication fine does not repair unrelated scheduler/menu obstructions. |
| Fine paid before another opportunity | **Test:** reach a collected-fine prefix, then allow another profitable disclosure with no additional loss. | Prove repaired off-path optimality; a first-violation proof must not claim repeated compliance. |
| Public detection before a receiver move | **Test:** let the receiver condition its action on report/collection outcome. | An average charge alone does not justify erasing those observations. |
| Two prior deviators | **Test:** accepted conflicting candidates, changed deadlines and a receiver already holding evidence. | Source reconstruction and subsequent rationality cannot assume the focal player's initialized invariant. |

The proposed new tests discriminate contracts; they do not assert an additional
impossibility theorem. Existing checked examples already rule out the simpler
readiness-only, ledger-only and freely variable lawful-message arguments.

## Most direct candidate edge

Use the existing runtime with a staged service: settle a canonical admitted
response, including its source-visible result, before the next admitted
decision that could use its pending contents. Allow arbitrary extra reads and
raw transmissions; classify consequential extra transmissions as departures.
Keep binding meaning fixed at submission, guard-aware withholding, explicit
forfeiture, deterministic public service metadata and protected inclusion.
Concurrent events can be added only after proving the same information condition.

First prove permitted histories implement source histories and decisions,
including accepted-choice reconstruction and own recall. Then prove a genuine
first-departure SE extension with one common tremble sequence and rational
continuations after violations. A prescribed source continuation need not stay
optimal after disclosure. A fixed playerwise compiler needs a local completion
rule; a theorem merely choosing a target assessment for each source assessment
has weaker quantifiers. This general extension is currently unproved.

For a first positive fragment, require that disclosures are followed only by
terminal receiver decisions with a local optimal-response rule. The finite
sender/receiver theorem supplies that strategic pattern, but an actual Vegas
graph, runtime service, monitor and payout adapter still have to instantiate it.
The staged service is an explicit restriction to justify, not a property proved
of arbitrary blockchain schedules or miners' incentives.

## Alternatives and boundaries

- **Same ambient evidence:** interpreting source and native play with matching
  communication/evidence opportunities can avoid hiding disclosure. It still
  requires a timed service correspondence and cannot silently substitute a
  synchronous all-public channel for partial pending observations.
- **Terminal observations:** allowing new information only after all decisions
  affecting retained and net payoffs are fixed is a promising restricted edge.
  Commitments being fixed is insufficient while withholding, guesses, reports
  or transfers remain strategic. Its native continuation theorem is open.
- **All-public games:** use a proved source-view sufficiency condition at each
  decision. Having utilities depend only on public final payouts does not make
  private inputs or interim commitments strategically public.
- **Other channels and sharing:** the present bounded alphabet and ideal evidence
  ownership are model boundaries. A watcher theorem does not establish the
  absence of private channels, shared pads/keys, coalitions or cryptographic
  encoding channels. State any exclusion as an assumption or model it in the
  ambient source; do not derive it from passive packet monitoring.

No new runtime or Lean theorem is introduced by this audit. Its acceptance gate
is an actual source-to-native continuation/SE theorem for the stated fragment,
not a longer list of individually plausible packet checks.
