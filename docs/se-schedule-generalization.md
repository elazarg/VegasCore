# Sequential-equilibrium preservation under asynchronous service

## Target and fixed semantics

Every source sequential equilibrium should have an equilibrium of the bounded
raw pending-message runtime preserving the joint law of initial parameters,
public results and realized net payoffs. Fix the program, initial law, runtime,
builder, observation mechanism, utility and deposit before choosing the source
equilibrium. The target concerns all bounded raw responses, not just prescribed
clients. A target equilibrium may depend on the fixed builder.

The semantics below are the agreed baseline. Changes require the owner's
approval (see the [checklist](se-async-checklist.md)). In particular:

| Operation | Meaning |
| --- | --- |
| Readiness | Dependencies complete; readiness starts the event's timer. There is no grant cursor. |
| Clock | Only explicit clock commands advance time. The deadline is the configured event deadline, currently its index plus one. |
| Binding | Submit an opaque handle. Acceptance records the handle and its immutable typed value or source failure. |
| Resolution | Canonical TRUE sends an authentic opening when owner-local validation succeeds. Canonical FALSE, and TRUE whose validation fails, send an authenticated evidence-free withholding packet, which completes the event on inclusion. |
| Silence | WAIT, an undecided owner. Resolution expiry with no accepted decision executes source FALSE and is a public decision miss, charged like a binding omission. |
| Binding expiry | Executes source failure. A completed binding with no accepted handle is a public decision miss. |
| Authorship | A player transmits only fresh envelopes it authors; there are no copies. Delivery and inclusion handle the original envelope, so ledger identifiers are distinct. |
| Causal evidence | The restricted emitter supplies a readiness credential only after the prerequisites complete. Raw callers cannot choose a credential themselves. |
| Packet verdict | Read only the signed packet, historical readiness evidence, final public record and receipts. Completed events require an accepting receipt and canonical content. |
| Enforcement | One capped charge per owner, from authentic partial evidence or a public decision miss. Gameplay continues after a charge or miss. |

The source language, guarded TRUE behavior and original private action recall
are unchanged. No mandatory decision admission, mandatory opening, session
cancellation, repeated deposit or universal cancellation charge is adopted.
Concrete credentials and commitments still require a backend refinement;
an ideal capability is not a proof of its cryptographic implementation.

## Checked boundary

[SourceServiceCompilation](../Vegas/Game/SourceServiceCompilation.lean) proves
full-source SE preservation for the fixed calendar. Its native game is the
sequentialized graph with the baseline raw responses. The
[checklist](se-proof-checklist.md) describes this checked theorem and its proof
dependencies. It is not a checklist of completed arbitrary-builder work.

[AsyncServiceSpec](../Vegas/Game/AsyncServiceSpec.lean) and
[ReactiveAsyncContract](../Vegas/Pending/ReactiveAsyncContract.lean) state the
arbitrary public builder contract. The general preservation theorem is open.
The contract supplies a timely owner opportunity, bounded inclusion of its sole
signed identifier, and complete play. Its clauses quantify over raw histories,
including flooding. Reaction and inclusion bounds must fit each deadline.
It permits early responses: the proved [roster contract](../Vegas/Game/ServiceRosterAsync.lean)
can give Bob a pre-ready own id0. If id0 is still pending when good id1 is included,
id1 is not globally sole. The finite fragment's no-early-Bob/clear origin is stronger.

The calendar's terminal audit takes an authentic partial-sampling backend as a
parameter. This does not by itself instantiate a watcher that observes and
reports through a real pending network. That implementation adapter is an
explicit remaining part of faithful end-to-end preservation.

The [archive](../archive/se-generalization/README.md) contains the speculative
routes, detailed investigations and retired modules as reference text. They are
not compiled or counted as evidence for the active theorem.

## What a game transformation must establish

Small models can expose reusable proof steps, but a projection between games
does not automatically transport equilibrium. Keep three obligations distinct:

1. **Honest execution.** Derive the joint source outcome, original private recall
   and realized settlement law under the proposed clients.
2. **Information.** Derive actual reach weights on each native information fiber.
   Additional signals can change best responses even when outcomes agree.
   Babbling requires payoff irrelevance and consistent off-path beliefs with
   rational continuations; merely ignoring a signal does not prove it harmless.
3. **All deviations.** Compare every whole native continuation at the same
   assessment, including WAIT, raw packets and behavior after a sunk charge.
   Honest execution alone supplies none of these comparisons.

Reuse [Enforcement](../GameTheoryExtensions/Analysis/Enforcement.lean): it already
expresses regret as base gain minus the fine times the change in charge
probability, and gives a whole-continuation rationality theorem. The runtime
must derive its conditional gain and collection bounds. Reuse
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
after deriving a common proportional reach factor on the actual fiber, and
[local comparison limits](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean)
after constructing one consistent native sequence and its comparisons.

[PassageRestrictionExtension](../GameTheoryExtensions/Analysis/Protocol/PassageRestrictionExtension.lean)
already proves `exists_consistent_extension_unclocked`, giving consistent rational
completion at genuinely new sites, and `sequentialEquilibrium_extends_of_continuation_unclocked`,
which consumes whole-policy comparisons at retained sites. Public binding omission
gives certain capped collection via `serviceAudit_charge_of_omission` in
[ReactiveServiceAudit](../Vegas/Pending/ReactiveServiceAudit.lean); later comparisons
use base payoff and rational completion, not renewed collateral. Hidden departures
pooling at a retained input are not thereby new free sites.
[TerminalAudit](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean)'s
`sequential_equilibrium_extends_of_terminal_audit` supplies the first-extra range
argument using conditional owner OR collection from every retained hidden history
under arbitrary target futures, with upper−ρD≤lower (ρ is the conditional owner OR rate).
Its scalar API requires `InformationSite.CommonDepth`.
The unclocked whole-policy consumer above and `settlement_le_of_departure_coupling`
in [TerminalAuditCoupling](../GameTheoryExtensions/Analysis/Protocol/TerminalAuditCoupling.lean)
are existing comparison routes; the coupling theorem uses incremental charge.
The calendar's `active_evaluator_stopped_coupling` in
[SourceServiceEvaluatorRepair](../Vegas/Game/SourceServiceEvaluatorRepair.lean)
supplies actual endpoint marginals. `bindingFrame_baseUtility` in
[BindingRepairReadout](../Vegas/Game/BindingRepairReadout.lean) preserves parameter
and public payoff from full Frame plus RIGHT OwnBindings; private-material
changes on these branches require no blanket positive collection rate.

[ReactiveMenuRestriction](../Interaction/ReactiveMenuRestriction.lean)'s native
menu inclusion preserves the SAME runner and full information. A coarse source
decoder in [ServiceInformation](../Vegas/Game/ServiceInformation.lean) is not a
source-to-native ActionRestriction embedding. Construct the retained native
assessment and its actual reach/continuation law before invoking the extension.
Silent FALSE, failed TRUE and deferral need no physical intention tag:
[policyMixture](../Interaction/ReactivePolicyMixture.lean) conditions the chosen slot on actual recall,
and [realization](../Interaction/ReactiveMixtureRounds.lean) preserves the whole execution law.
[DisclosurePosterior](../Vegas/Game/SourceServiceDisclosurePosterior.lean) and
[DisclosureMemory](../Vegas/Game/SourceServiceDisclosureMemory.lean) restore original intentions in the proof law.

These are existing interfaces to instantiate, not unproved arrows in a new
transformation tower. Reuse, remove or replace existing machinery first. Before
implementing a new abstraction or changing semantics, identify the concrete
obstruction, explain why the existing levels cannot resolve it, and discuss the
proposed SE proof benefit with the user.

## Concrete concerns

1. **WAIT is an actual action.** It can implement a prescribed source FALSE.
   At a binding or intended TRUE input, a protected first opportunity does not
   guarantee protection after waiting. Suppose sending later succeeds with
   probability 0.1, while one more wait gives another opportunity with success
   probability 0.75. A proof that always sends when timely is insufficient.
   Compare the whole later policy, including ordinary resolution expiry and
   binding-omission charges. Longer deadlines alone do not prove this comparison.
2. **Selective inclusion can select public opening contents.** A builder can
   include late TRUE only for some values and raw withholding reliably; the
   withholding packet's possible charge still belongs in the payoff comparison.
   Opaque binding traffic does not make public openings opaque. A builder using
   only public data can still select by the disclosed value. Derive the actual
   success/rejection/expiry law before reducing a delayed decision to a source
   alternative; public observability does not imply choice-independent delivery.
3. **A one-time fine is sunk once certain.** After a public binding omission,
   another bad packet does not pay another deposit. For example, a player already
   losing 100 may profit by sending a certificate influencing a later guess.
   Its continuation must be rational under the remaining utility. Before its
   first offense, a fine bound must cover the gain from the entire continuation.
4. **Traffic can change beliefs.** With equally likely types, WAIT probabilities
   0.1 and 0.9 produce a 10/90 posterior after observing WAIT. Own perfect recall
   cancels own action factors, not another player's timing likelihood. Derive a
   joint source/traffic law at every actual native information set.
5. **Rare histories need relative bounds.** If a clean information set has mass
   epsilon squared and exceptional behavior has mass epsilon, unconditional
   convergence gives no conditional-belief control there. Choose one common
   perturbation family with exceptional mass negligible relative to clean reach.
6. **Rejection can still communicate.** A rejected opening remains an authentic
   pending packet. If it proves a hidden bit to a later player, its effect is not
   erased by reverting the call. The final-record audit must establish actual
   collection for the offending packet; a send-time oracle is unavailable.
7. **Watcher observation and delivery are separate.** Seeing a bad packet does
   not collect a fine if its report is censored. A postgame reporting window can
   help, but its activation and conditional delivery guarantees must be stated.
   The watcher must use actual known evidence, never the whole hidden pending pool.
8. **Prescribed packets must stay lawful.** A binding in slot 3 must be checked
   against its historical predecessor count, even after later bindings complete.
   Repeated knowledge or forwarding of one signed identifier is not a new authored
   packet. Prove this under foreign raw continuations, not only initialized play.
9. **Concurrent bindings require information commutation.** Independent store
   updates can commute while strategies or observations fail to commute. A public
   opening cannot precede another source-earlier binding under the barrier order.
   Preserve latent source choices without exposing unexecuted foreign values.

These are proof obligations, not established counterexamples to preservation.
A failed proposed comparator refutes that comparator; it does not refute the
existence of some preserving native equilibrium.

## Design alternatives

| Alternative | What it changes | Required argument and cost | Decision |
| --- | --- | --- | --- |
| Baseline runtime, existing asynchronous contract | No gameplay semantics. Timing and continuation strategies may depend on the builder. | Prove WAIT comparisons, joint beliefs, rational continuation after a sunk fine and real collection. These are the unresolved core. | Active target. |
| Stronger inclusion service | Keep gameplay semantics; promise timely handling at every allowed timely owner activation, or avoid activating an owner after protection closes. | Give an operational, all-history scheduler condition and an implementable instance. It removes selective late inclusion only where proved. It narrows the class of builders and does not solve sunk-fine continuation. | Fallback only; not a substitute for the current target. |
| Larger deadline budget | Keep the action meanings; change runtime parameters to leave room for additional activations and inclusion. | Recheck readiness-to-opportunity delays, complete play and practical throughput. Timing signals and capped-fine incentives remain. | Optional configuration, not a proof technique. |
| Opaque admission followed by mandatory opening | Add another transaction phase and freeze a resolution before public inclusion. | Prove fresh phase protection and source/private-recall simulation. Nonopening needs a new rule; cancellation changes future gameplay and utility. | Archived protocol alternative; not adopted. |
| Quitting or repeated penalties after misconduct | Change enforcement or future gameplay. | Specify a public implementable trigger, evidence/delivery probabilities and collateral. Quitting does not prevent pending communication; repeated deductions need an actual funding rule. | Not adopted without a necessity argument. |

Discuss any precise implementability/theorem obstruction or concrete design defect,
the existing levels' limitation and proposed proof benefit before changing semantics.
Keep the baseline until a change is agreed; proof convenience alone is insufficient.

## Faithful watcher and settlement

Use a postgame challenge window after the source outcome is fixed and existing-envelope verdicts are stable.
Preserve actual known envelopes and public ledger; observe genuinely unknown
foreign pending IDs through the real observation rule. Only the builder publishes
a witness, by including its pending original; a player who knows a foreign envelope
cannot resubmit it. A FALSE gameplay receipt still publishes the original
signed body, so a fresh accepted report is unnecessary. Conditional publication
bounds must cover selected contents and later raw traffic; a longer window alone
does not imply certainty.

The baseline final-record audit has a unary packet verdict. If two different
identifiers compete for one completed event, at least one lacks an accepting
receipt; including one identifier again does not create that offense. Do not import
the archived protocol's distinct-packet pair audit or its pair-coverage requirement
without showing that the baseline audit actually needs it.

Without copies, no reporter can republish a known foreign witness; a pending
forbidden envelope is published only when the builder includes it. A supported
conditional inclusion bound r gives total owner OR collection at least r times the
probability that the witness is pending or public at the challenge. The
[small-model note](se-small-models.md#b-publishing-a-pending-forbidden-witness)
derives this bound without independence. Such a builder inclusion promise is
still absent, and an ex ante challenge bound does not supply the current audit's
pointwise per-record sampler coverage. If the verdict is not stable, observation
and selection need an additional joint analysis.

The concrete reporting component must refine the baseline audit backend while
preserving gameplay and players' information. Do not independently resample a
report already realized in the execution. Public binding omissions remain
contract evidence; a watcher cannot certify an unseen absence.
An endpoint coupling does not automatically contain full protocol histories.
For a history-dependent challenge, reconstruct each actual side-history law
conditionally on its endpoint using [fiberPosterior_reconstruct](../GameTheory/GameTheory/Math/Probability/Conditioning.lean).
Use each side's own evidence; prove the joint Boolean audit law factors through
the declared observation/backend, rather than infer this from a collection bound.

The history-integrated terminal-audit interface does not require coverage of each
final list. In contrast, `sampledTrafficAudit_collection_from_record` in
[ReactiveAuditCollection](../Interaction/ReactiveAuditCollection.lean) propagates
a persistent attributed forbidden record only after pointwise sampler coverage
is supplied. Authenticity supplies the separate zero-charge soundness direction.

## Small objects that isolate the hard questions

Use the following objects to settle specific lemmas before generalizing. They
are mathematical fragments and experiment specifications, not five new language
implementations or five separate SE compiler projects. Each has a concrete
connection to the final proof.

| Object | Smallest useful form | Standalone result to seek | What it would supply |
| --- | --- | --- | --- |
| A timed decision | One owner, two source actions, two opportunities, a hidden builder branch, expiry and bounded continuation values. Binding packets are opaque; resolution packets can expose their fixed public value. | Derive the actual stopping law and a whole-policy WAIT comparison, using source rationality or the change in charge probability where applicable. Include ordinary FALSE expiry. | The WAIT/source-choice comparison for a constructed assessment. A pointwise send-now argument is insufficient. |
| A timing information experiment | Two hidden types, one sender and one later receiver, two timing signals and a binary public outcome. Fix the source action law and actual inclusion kernels. | Derive the joint reach table. Where the construction follows the source assessment, test its required conditional weights using rational timing and one common tremble family; generated off-path inputs may instead have different beliefs and rational actions. | The belief-and-timing compatibility question. A timing equilibrium and a separately chosen factorization do not suffice. |
| A capped-sanction continuation | Two economic stages and one Boolean charge flag, with uncertain observation and delivery. Give the remaining stage an arbitrary bounded payoff. | Prove the first-departure whole-payoff inequality and identify what remains rational once the charge is already certain. Use the change in collection probability, not a second full fine. | The enforcement boundary and the correct domain for free rational completion. Existing general enforcement/completion APIs should discharge the abstract part. |
| A signed-witness channel | One forbidden envelope, actual pending/public/known locations, partial observation and builder inclusion of the pending original; any Boolean receipt publishes the signed body. | Conditional builder inclusion r gives total owner OR collection r·P(pending or public); fixed-record selection needs its own coverage. Derive actual postgame service and settlement refinement. | The watcher/backend boundary in the small-model note; no new report handler or SE theorem follows. |
| An opaque binding swap | Two different owners, two independent bindings, no intervening public opening, and a public order choice. | Use the existing commutation of normalized behavioral kernels preserving typed store and every owner's original-action recall; then analyze native timing, traffic and adaptive order. | Barrier concurrency. The source-level commutation theorem does not supply native conditional beliefs. |

The [resolution-and-guess calculation](se-small-models.md#a-resolution-followed-by-a-guess)
solves one restricted three-action tree for every 0<p<1 and qD≥0 with one common
fully mixed family. At p=3/4,q=1/2,D=4, rational full bounded RAW Bob/tail completion
includes reactivation. A full finite public builder extending retained
service admits Alice's earlier responses via normalized first-extra comparisons,
unclocked extension and forward canonicalRaw. Explicit protection, complete play,
paired resources and the same fair backend preserve the joint law. The private type
is uncommitted; a θ-binding permits rejected certificates to reveal θ after old R
without a second fine, breaking pooling, not preservation. Different source resources,
later economics and actual service/backend certification remain outside that result.

The committed-type fragment has conditional finite full-RAW-tree constructions for
two source assessments. Separate first-NONE rates and free floors select HIGH at
off-path expiry for T at both types, or LOW at on-path FALSE for H→T, L→F.
Each uses ONE Bayes family and selected continuations to bound whole WAIT policies.
The [CommittedResolutionService](../Vegas/Examples/CommittedResolutionService.lean) example proves
`contract`, `timely` and finite Nature support for the compiled source setup and fixed linear
horizon-16 scheduler over initialized unrestricted RAW histories. Alice acts at
clocks 0/1, then postcompletion Alice and first Bob at clock 2, Bob expiry at 5;
empty gameplay leaks, Alice delay 0/bound 1, Bob delay 2/bound 0 and N=4.
Censored T's FALSE receipt separates it from clean expiry. `silent_bob_input_law` checks
one common full first-Bob input under literal silent initialized play at both types,
including empty own recall and public Alice failure, without characterizing the entire fiber.
`prescribed_packets_clean` derives TRUE receipts and final permissions for all transmitted
envelopes on initialized ALL-prescribed `sourceServiceTurnPolicy`/`firstTurnTiming` play,
for any source behavioral profile. `prescribed_settlement` gives the full joint payoff vector
as pure arbitrary base utility under any authentic sampler and arbitrary deposit.
`first_true_bob_output_law` checks the actual canonical first H opening's prompt stage-2
acceptance and public `success true` through first Bob activation under arbitrary later
native policies. `mixed_bob_reach_bound` proves abc≤mL and mH≤u at the full common input:
a,b,c are actual conditional NONE probabilities at L's three silent-path inputs, and u includes
ALL first-H mass outside one canonical TRUE atom, including aliases. If abc>0, the initialized
1:3 weights give mH/(mH+3mL)≤u/(u+3abc). This is physical reach, not yet the SAME native
assessment's belief. Native Bayes conditioning, concrete payoffs/whole-policy comparisons,
source outcome transport and concrete first-packet verdict consumers remain open.
The two native SE constructions are conditional paper mathematics;
no checked native/general SE or live watcher follows.

The archived [exact finite checker](../archive/se-generalization/documents/scripts/experiments/adaptive_schedules.py)
and [C6 probe](../archive/se-generalization/documents/scripts/experiments/deferral_miss_probe.py)
are reference tools. C6's certain-penalty binding probe also finds preserving equilibria
in its negative control; it establishes neither generic composition nor resolution impossibility.

Charge/report adapters and binding commutation can be checked separately, but
full composition needs the same timing and belief construction. A small-model
result counts toward that proof only with premises derived from the actual runtime.

## Road to the proof

1. **Derive the remaining concrete runtime adapters.** Reuse the checked all-prescribed
   receipt and settlement consumers and canonical first-H branch law under arbitrary later RAW.
   Instantiate [opening conformance](../Vegas/Pending/ReactiveOpeningConformance.lean) and existing
   [condemnation/persistence](../Vegas/Game/ServiceSettledEvidence.lean) with the actual initialized
   resources for first-packet verdicts under RAW continuations. Connect the checked physical
   mixed-reach bound to Bayes conditioning in the SAME native information game and the actual audit backend.
   Arbitrary later source economics need their own comparisons.
2. **Instantiate the existing native completion.** Use the actual bounded RAW menu,
   runtime information and decision recall with
   [free-agent completion](../GameTheory/GameTheory/Analysis/Protocol/AgentCompletion.lean).
   Choose source-following and free inputs, one fully mixed source/timing/raw family,
   independent pinned rates and free floors, and a single actual Bayes subsequence.
   Give a legal comparator shared across all hidden histories of an information
   set. Do not pin a source policy at delayed inputs without proving rationality.
3. **Prove the source/traffic invariant.** Couple legal source actions, chance,
   public results and original own recall to actual native histories. Establish
   the conditional weights, including hidden builder history and foreign WAIT.
   Supply the relative escape bounds required by the common sequence.
4. **Instantiate existing comparisons and collection.** Derive actual retained
   WAIT/private-representation comparisons and the information/payoff embedding.
   Use existing rational completion for publicly sunk charges. Derive conditional
   postgame service and first-extra collection; distinguish history-integrated bounds
   from the source capstone's pointwise coverage. Establish zero charge on supported
   equilibrium play. These runtime premises, not another sunk-fine theorem, remain open.
5. **Compose the general serial capstone.** Reuse the existing local-comparison
   limit and depth-free extension APIs. Derive their compiler-specific premises
   rather than assuming posterior correspondence or continuation dominance.
   Preserve the joint realized law, pin standard axioms, and run the full build
   and load-bearing evidence checks.
6. **Extend to barrier concurrency.** Reuse the behavioral store-and-recall
   commutation in [PolicyCommutation](../Vegas/EventGraph/PolicyCommutation.lean);
   derive native information and pending traffic under adaptive public order.
   Discharge the same timing and continuation questions. This remains part of
   the asynchronous objective; completing the serial stage does not close concurrency.

Keep the checked calendar theorem while this work proceeds. Restore an archived
helper only when a concrete mathematical step needs it and its premises match
this model. Prefer a small number of invariants and whole-law lemmas over a file
for every intermediate observation. Build footprint is not proof progress.
