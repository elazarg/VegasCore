# Sequential equilibrium on protected executions of the native runtime

This note isolates a positive result on the actual reactive runtime. The
environment may activate players repeatedly, read pending packets, choose their
inclusion order, advance the clock, and execute public chance instructions. Its
policy may depend on its complete public command history. Players retain their
own actions, their private candidate catalogues, receipts, and every sampled
pending packet. The proof does not replace those transitions with one atomic
delivery operation.

The restriction is strategic: at the first ready activation of an instruction's
owner, a binding must submit a canonical source value and an opening must submit
the canonical effective opening. Every other activation has the single response
silence. This is a particular restriction of the native action menus. It is not
the native raw game, which also permits deferral, late submissions, retries, and
malformed traffic. Establishing an equilibrium in this restricted game does not
establish an equilibrium against those extra actions.

## Result card

| Item | Exact scope |
| --- | --- |
| Source | The finite intended source game: successful private bindings whose values satisfy the owner's predicted guard, and mandatory effective TRUE openings. Initial bindings are successful, and the setup is well formed. |
| Runtime | The existing sequential event graph and reactive application, including genuine pending plaintext openings, opaque binding handles, private candidate preparation, readiness credentials, private leak samples, and complete player recall. |
| Strategic domain | Only the first-ready restriction just described. Values vary over the entire intended source menu; opening and waiting responses are singletons. |
| Service assumptions | The existing asynchronous contract and timely activation/inclusion bounds, for the fixed physical horizon and initial law. The scheduler receives its existing public input and own command recall. Nature branches finitely. |
| Bounds | The finite raw alphabet covers all binding and publication values. At least one prepared candidate slot per graph event is sufficient on this restricted domain. These are fixed before choosing the scheduler. |
| Utility | The existing decoded source utility with the intended-game reveal-forfeit convention, followed by the existing sampled terminal audit. No fees, time preferences, capital costs, or strategic miner utilities are added. |
| Quantifiers | Fix source, horizon, deadlines, bounds, cryptographic observation interface, forfeits, audit, and deposits; then take any public scheduler satisfying the contract. For every source sequential equilibrium, construct a sequential equilibrium of the first-ready restricted native game. |
| Preservation | Exact joint law of initial source data, terminal logical record, and net utilities. Every initialized execution has zero audit charge and zero source reveal forfeit. |
| Mathematical status | The complete paper proof passed root and independent mathematical review. The adaptive stopped-prefix adapter is not a checked Lean theorem. Existing checked laws establish substantial parts of the construction. |
| Full native claim | None. Extending this assessment to the bounded raw menu remains a separate mathematical problem. |

The reveal forfeit can be fixed above the source payoff range as in the primary
preservation target. Its magnitude is not used to deter anything in this
restricted-game proof: all permitted histories already satisfy the intended
source rules. The sampled audit need only be authentic, meaning its observed
evidence is a subset of actual evidence. No positive detection probability is
needed for the zero-charge assertion.

## The source and the exact physical choices

The relevant source is `Setup.intendedModel`, not an independently invented
commitment interface. At a binding it retains the values in
`ProtocolView.intendedAvailable`: values satisfying the predicted guard, with
the specified fallback if the predicted set were empty. `Setup.WellFormed`
and the intended-state invariant exclude that empty case along legal initialized
histories. At an opening the menu is the singleton TRUE. The source keeps private
values and own logical actions in its observations; all samples and successful
publications remain in its accumulating typed context.

Use the actual sequential compilation `serviceGraph setup .sequential` and the
actual `serviceApplication`. The physical rule is defined from the player's
existing input `(past, view)`:

1. Recover the current owned ready event from the player's public application view.
   Count earlier own inputs naming that event, as in `serviceTurn`.
2. At the first such input, decode the source observation at the corresponding
   prefix. For a binding, retain **every** intended source value, translated by
   `canonicalServiceDecision`. For an opening, retain its TRUE translation.
3. If this is not the first ready input of the current owner, retain only
   `Action.mk none`.

The rule does not add a scheduler cursor, expose the number of environment
commands to a player, or erase earlier silent activations. All counts used in
the rule come from that player's actual recall. The native input determines the
source view by the existing source-prefix checkpoint decoder. Consequently two
equal native inputs have the same retained menu. On an impossible input outside
the initialized legal trace domain, a singleton silence menu is a harmless total
definition; it does not create a reachable exception.

There is no arbitrary choice of cryptographic handle at a protected binding.
The handle is `(owner, prepared k)`, where `k` is the public count of this owner's
completed bindings. The sender's private submission contains the typed value;
the materialized packet contains only the handle, event address, canonical
evidence field, and actual readiness credential. The source value is retained in
the authenticated private candidate catalogue and in the owner's actual action
recall. An effective opening contains the matching fixed value and authenticated
opening evidence.

This first-ready rule differs from `bounds.canonicalActions`, which always
retains silence and permits some later canonical calls. It also differs from
the existing service-risk menu. Neither of those larger menus is silently
identified with this restriction.

## Native path facts needed by the proof

The following arguments concern every legal history of the restriction,
including histories reached by a different permitted binding value. They do not
only concern the equilibrium's positive-probability paths.

**Canonical candidate allocation.** Initially, prepared slots are fresh and
initial binding candidates are represented by the successful typed source
cells. Inductively, each completed binding of an owner consumes exactly the
next counted prepared slot. No intervening activation prepares another slot:
it is silent. At a new owned ready binding, no earlier binding of that owner is
still pending, because the sequential dependency order has completed every
earlier event. Thus its counted slot is fresh, and the fallback branch of
`canonicalFreshSlot` is never used. The count is below the total event count.
`CoversOutputValues` supplies each permitted typed raw value and each eventual
opening value. Initial handles are allowed independently of the prepared-slot
bound. Hence all translated source actions and all silent responses belong to
the actual bounded raw menu. No source value is discarded to make the proof
work.

**Protected inclusion is actual acceptance.** The existing opportunity theorem
places the first ready owner activation inside `InclusionFitsDeadline` under
`AsyncContract` and `AsyncTimely`. After its one canonical submission, all its
other activations are silent, so the contract's no-other-emission premise for
that event holds. The contract promises a receipt, rather than directly
promising acceptance. Acceptance follows from the actual inclusion checks:
the event is ready, the counted handle is unused and has its immutable correctly
typed value, the readiness credential names the event, and inclusion occurs
before expiry. For an opening, the guard is satisfied along an intended source
history and the authentic evidence matches the accepted binding. Clock commands
advance by one and response transitions do not advance the clock; the inclusion
bound therefore cannot be bypassed by jumping over the deadline. An event cannot
expire first while its protected budget remains available. Duplicate include
commands after its completion do not create a new decision or packet.

**Logical evolution.** Acceptance of those packets implements the corresponding
source instruction. Public chance is executed by the existing environment
transition using the source public context; an invalid or repeated command has
no extra source effect. Expiry does not implement a public chance instruction.
`CompletesPlay` supplies eventual completion within the fixed horizon. Hence
every restricted history reaches each next instruction with the corresponding
source checkpoint. Effective openings, successful initial cells and the
well-formed intended-state invariant are essential here.

**Conformance and utilities.** Each emitted binding and opening has the actual
canonical content, and each is accepted at its event. Every binding has a
submission, so no public binding omission is charged. Thus all actual traffic
is permitted by the terminal settled-record audit. Authentic sampling cannot
turn permitted traffic into a forbidden packet. The terminal typed readout is
the source readout, and `failedReveals` is zero. The net utility therefore equals
the source utility for every terminal restricted history, before taking
expectations. Retained initial data can be included in that joint readout.

The checked first-turn policy, opportunity, canonical-slot, no-miss and
settlement laws substantiate these facts for the copied policies. The induction
above is the paper menu-closure argument required when the focal player chooses
any other retained value at a physical information set. Unconditional honest
execution alone would not establish that closure.

## The adaptive stopped-prefix replay

This is the additional observation argument. It is not an invocation of the
fixed-roster posterior theorem.

Let `h` be a legal source history immediately before a strategic source
instruction. A physical replay of `h` runs the **existing** transition system
from the corresponding initial source state, fixes the logical action and chance
labels already present in `h`, and stops immediately before the owner's first
ready response at that instruction. It permits all earlier activations, private
samples, inclusion commands, unsuccessful no-op commands, waits, and unit clock
advances which the scheduler generates. Its length is a random finite length
bounded by the fixed physical horizon.

In the replay, source action and logical chance probabilities are factored out
once into the source history weight. The remaining operational weights are
products of the actual public scheduler kernel and actual passive leak kernels.
There is no conditioning on a future chance value to help the scheduler choose
an earlier command. The source chance factor is extracted at its actual
successful execution, from the public context preceding that execution.

For a focal owner `i`, retain jointly:

- the complete network: pending packets, ledger, submitted inputs and serials;
- the complete public environment record, including command recall and receipts;
- `i`'s full actual input: own previous views, private submissions and emitted
  packets, retained leaked packets, candidate catalogue, and current view.

Call the resulting kernel `Q_h`. The full private catalogues of other players
need not be equal. They are coupled by their corresponding source states, not
erased or made independent.

### Normalization

Every restricted continuation of a supported source prefix implements the next
source instruction and reaches this first ready input within the fixed horizon,
by the path facts above. Forcing a legal retained action and a supported logical
chance outcome preserves compatibility with a native raw trace; the contract
quantifies over every such trace, independently of the original source lottery.
It therefore applies to these replay paths directly. The replay's stopping paths
form an antichain. Summing
their operational weights gives one: all scheduler and private sampling
transitions are normalized, and no positive operational mass is lost in an
expiry, missing transmission, or never-activated branch. This statement uses the
existing service contract, not a new assumption that failed physical executions
are invisible. It would fail for an unrestricted deferred submission.

### Equality on a source information fiber

Suppose `h` and `h'` belong to the same information set of the current source
owner `i`. Replay them with the same operational random choices. The source
public prefix, the instruction position, and all of `i`'s retained logical
private information are equal. The following transition-by-transition facts
then establish equality of the joint operational record retained above.

* A canonical binding's public packet is independent of its value. Its private
  preparation changes only its owner's catalogue. If that owner is `i`, the
  value is already identical by `i`'s source information; if it is another owner,
  no observation of `i` or the scheduler changes. Inclusion of that opaque
  packet has the same public receipt and foreign observation.
* Every earlier opening is completed before the current source instruction,
  by the sequential dependency graph. Its plaintext value is therefore in the
  current source public prefix. It is equal on this fiber, even if `i` saw its
  pending packet before acceptance. Its evidence and credential are then
  generated from the same public handle and fixed value.
* Current ready-event clocks, counted handles, receipt lists, and the scheduler's
  entire earlier command record agree. The scheduler has exactly the same
  input to its next lottery. It does not receive the foreign private catalogue
  or any player's private pending-sample outcome.
* The passive sampling rule reads only the recipient and actual pending packet
  list. These agree. Replaying the same sampled identifiers preserves the full
  retained leaked-message record. The rule may reveal every pending packet.
* All earlier responses outside the first ready decision are genuine silence.
  Their occurrence and the views remembered at them are retained and agree for
  `i`; there is no secret-dependent waiting policy.
* The current catalogue of `i` contains its source initial candidates and its
  own earlier accepted binding values, at structural slots. Those values remain
  in its source observation or own logical action recall. All unused prepared
  slots are fresh. Thus the catalogue, including its old values, agrees on the
  fiber rather than being discarded.
* Source chance reads the public context. Fixing a supported chance label gives
  the same chance factor in both histories and the same native public successor.
  All timing and sample commands remain in the operational replay.

The atomic opaque-binding equalities are already checked in
`ReactiveBindingObservation`. The source-store and own-completion observation
equalities are checked in `ServiceObservation` and `ServiceInformation`. Their
composition over this adaptive bounded stop is the additional paper lemma.

Consequently, for a source information set `I`,

\[
 Q_h=Q_{h'}=:Q_I\qquad(h,h'\in I).
 \tag{1}
\]

This equality concerns the joint public record and **focal** full input. It does
not assert equality of the global private execution state. Arbitrarily
correlated retained source secrets are allowed. They change the source prior
and the other owners' private catalogues; they do not change these operational
transition laws on the fixed focal information fiber.

For the current owner of a mandatory opening, its current value is already in
its source information before emission. For the next strategic player, that
value is public after acceptance. These are different reasons at different
stopping sites; pending visibility is allowed at both.

## One global consistency sequence

Take the completely mixed source behavioral sequence \(\sigma_n\) witnessing the
given intended source sequential equilibrium. Copy its value lottery at each
first ready native binding input, using the decoded source information. Use the
canonical singleton TRUE opening and actual singleton silence elsewhere. Call
this native policy \(\rho_n\).

Each \(\rho_n\) is completely mixed **in the stated restricted native game**:
every allowed source value has positive probability and singleton menus have
their unique action with probability one. It is not completely mixed in the raw
game. The source full-support sequence reaches every legal intended source
history, and the operational support reaches every legal physical history of
the restriction.

Let `w_n(h)` be source reach weight. For a genuine first ready native information
set with full input `J`, the replay gives

\[
 \Pr_{\rho_n}(h,J)=w_n(h)Q_I(J),\qquad h\in I.
 \tag{2}
\]

When more than one operational record gives `J`, the notation `Q_I(J)` sums
their weights. Its value can be arbitrarily small, but it is the same for every
hidden source history in `I`. Bayes' rule therefore cancels it **before taking
limits**. The marginal native belief on source histories is exactly the source
Bayes belief at `I` for every `n`. This is precisely the proportional-reach
hypothesis consumed by `bayesBelief_projection_of_proportional_reach`.

Now use Bayes beliefs on **all** native information sets for each \(\rho_n\).
Finite source support, finite raw bounds, finitely branching nature and the
physical horizon give finitely many histories. Take one common subsequence on
which every native belief simplex converges. Strategies converge to the copied
source strategy. The source belief marginals at genuine sites converge to the
specified source assessment by (2). At new singleton waiting sites there is no
source-corresponding belief formula; the same compact subsequence supplies their
full native limiting beliefs. Those sites have no strategic comparison to
preserve. Thus the whole assessment, including off-path source histories and
physical views, has one consistent witness.

## Sequential rationality, rather than only correct execution

Fix a genuine native first ready binding site `J`, its decoded source site `I`,
and a permitted alternative value or lottery. From **each** compatible clean
physical prefix, choosing that value and then following the copied future
policies has the source continuation readout law from the corresponding `h`
with that source action. The path proof works with the actual private catalogues,
pending samples, receipts and clocks left by this prefix. Future copied source
lotteries ignore their operational additions, and the service contract still
applies to that legal continuation. The success and utility assertion is not
obtained by restarting the execution or replacing its private state with fresh
independent state.

Together with (2), the prescribed and alternative continuation laws, averaged
under the native Bayes belief, are exactly the corresponding source laws. At
finite `n` the source witness need not be an equilibrium, but its local comparison
converges to the source equilibrium comparison. The fixed finite tree makes all
these payoff expressions continuous, even at sites whose reach probability
vanishes. Equivalently, instantiate the existing
`exists_sequentialEquilibrium_limit_of_local_simulations` after the stopped-prefix
and local continuation adapters have been supplied.

Opening and waiting menus are singletons. Their one-shot comparisons are
identities. At each genuine binding site, the limiting comparison is a source
sequential-rationality comparison, hence nonpositive for every alternative.
Native full recall gives the one-shot deviation principle for this finite game,
so physical policies which adapt later permitted values to remembered traffic
do not create a further gap. This proves sequential rationality at every
information set of the restriction.

Here finitely branching nature is the existing
`ReactiveApplication.FiniteNature initial scheduler` condition: finite support
of the initial law, the scheduler's command lotteries, private pending-sample
lotteries, and application environment transitions. A finite instruction count
alone does not make an infinitely supported public sample or scheduler command
law into a finite game.

Finally, initialized native transport implements every source instruction
exactly; its audit charge and reveal forfeit vanish pathwise. Copying the limiting
strategy therefore preserves the joint source terminal law and net utilities.
The initialized-law induction is independent of the observation calculation;
it also covers a program containing only public chance instructions, with no
owned instruction and hence no first ready strategic stopping site.
No deposit was selected using the scheduler's exact inclusion probabilities.
Indeed the copied policy is the same for every scheduler in the stated class;
beliefs over operational histories may depend on that scheduler.

## Proof and evidence matrix

“Checked” below means that the named existing theorem supplies the stated
part of the argument with its own explicit hypotheses. “Paper adapter” means
the composition proved in this note has not been implemented or checked in Lean.

| Obligation | Existing declaration or primitive signature | Status and remaining adapter |
| --- | --- | --- |
| Intended legal histories have valid guards and effective TRUE | `Setup.WellFormed`, `Setup.intendedState_trace`, `Setup.failedReveals_eq_zero_of_intendedState` in `IntendedPreservation` | Checked source invariant; apply at each decoded native prefix. |
| Native current input determines the source information | `SourcePrefixCheckpoint.source_view_eq_of_observe_eq` in `SourceServicePrefixInformation`; `decisionView?_observe` in `ServiceInformation` | Checked at related checkpoints; adaptive menu-closure supplies those checkpoints. |
| First response is timely | `firstTurn_inclusionFits` in `SourceServiceFirstTurnOpportunity` | Checked with actual trace and answered-activation hypotheses. First-ready histories satisfy those hypotheses. |
| The actual binding packet uses the counted fresh slot | `sourceServiceFirstTurn_binding_call`, `canonicalSlot_fresh_of_used`, `CanonicalSlotsUsed` | Checked copied-policy facts; restricted-history induction extends them to each permitted local value. |
| Every source action is a bounded raw action | `CoversOutputValues`, `canonicalServiceDecision_available`, `riskCanonicalSlot_resources`, `MessageBounds.submissions_mem` | Static output coverage and event-count slot bound suffice on clean histories. All-raw compiled coverage uses the stronger horizon bound and is not required here. |
| Private binding values do not change public/foreign inputs | `reactiveBinding_network`, `reactiveBinding_activation_other_input`, `reactive_include_commitment_input_congr` | Checked atomic facts; adaptive stopped replay composes them. |
| Dynamic accepted candidates remain available | Initial candidate construction, immutable `Submission.register`, fresh counted-slot induction | Native primitive proof; no extra candidate preparation is permitted in this restriction. The catalogue is retained. |
| Pending sample outcomes are private from scheduler | `ReactiveApplication.Scheduler`, `Execution.observeEnvironment`, `Execution.environmentStep`; `MessageNetwork.ObservationRule` | Explicit actual signatures: scheduler sees public history, leak kernel sees pending packets. No independence of source secrets is invented. |
| Source readout is preserved | `firstTurn_readout_law` and `FirstTurnSourceLaw` in `ServiceHonestLaw` | Checked initialized source-profile law. Exact law after every clean physical prefix is a paper checkpoint/continuation adapter. |
| Net audit charge is zero | `sourceServiceFirstTurn_charge_zero`, `sourceServiceFirstTurn_settlement_law` | Checked copied-policy laws for authentic sampling. The paper all-clean-history conformance induction gives the stronger local use. |
| Adaptive first-ready likelihood is normalized and constant on the source fiber | Equations (1)–(2) and the native primitive coupling above | Paper adapter. Existing `SourceServicePrefixFactorization` and `SourceServicePrefixPosterior` prove fixed-roster versions, not this scheduler-independent composition. |
| Full posterior transport | `bayesBelief_projection_of_proportional_reach` | Checked general theorem once the adaptive fiber likelihood is established. |
| One global consistent, rational assessment | `exists_sequentialEquilibrium_limit_of_local_simulations` and finite native recall | Checked general theorem; paper adapters give its local-law and initialized-law hypotheses. |

## What this does and does not resolve for the concrete model

The observation problem on protected intended serial executions has a plausible
complete positive answer with the actual native packets and recall. Variable
physical duration is not an intrinsic obstruction: a normalized bounded stopped
kernel suffices. Neither total pending visibility nor correlated private source
types invalidates the fiber argument. Candidate memory is essential in the
proof, and happens to be controlled by the no-extra-preparation restriction.

The remaining checked work is therefore an adaptive prefix/continuation adapter
on existing layers, rather than an alternative blockchain interface. A stronger
model claim still needs more than that adapter. The actual raw game permits:

- silence at a first ready opportunity, followed by a later accepted canonical
  binding or opening;
- repeated or competing packet submissions and distinct authenticated packet
  identifiers;
- additional privately prepared candidates and evidence requests;
- malformed or prematurely leaked content and arbitrary continuation after
  those departures.

The terminal audit cannot automatically deter an excluded late packet: on a
successful accepted route its content may be audit-clean. Its loss on failed
routes depends on the actual mode and subsequent play. A proof extending the
protected assessment must compare the complete continuation incentives, including
the resulting consistent receiver beliefs. `TerminalAudit` requires such
collection bounds against arbitrary later behavior; first-ready honest execution
does not provide them.

The checked intended-source forfeiture theorem is also not that raw extension.
It compares forbidden **logical source actions**, and ensures an eventual failed
source reveal for the deviator. A permitted logical value submitted late is a
different physical deviation. No theorem here identifies those two departures.

Optional lawful FALSE disclosure belongs to a separate source target. It creates
a silent instruction completed by expiry, and general TRUE actions can sometimes
translate to the same silence when local validation fails. The primary proof
above deliberately uses the project's mandatory effective intended source, so
it does not need a source-intent reconstruction theorem for those physical
aliases. Extending to the optional normalized disclosure game requires that
additional observation and menu argument, even before adding late raw traffic.

Finally, the proof retains the project's idealized cryptography and nonstrategic
public scheduler. It omits fees, strategic builders or miner collusion, timing
utility, reorganization/finality races, computational guessing errors and raw
EVM encoding costs. A conditional service theorem is useful only if the chosen
backend meets its timely opportunity/inclusion/completion bounds; this note does
not establish those operational bounds for a particular deployed chain.
