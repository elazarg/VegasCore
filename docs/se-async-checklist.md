# Arbitrary-builder SE preservation checklist

This is the progress ledger for sequential-equilibrium preservation beyond the
fixed calendar. The [calendar checklist](se-proof-checklist.md) covers the
checked fixed-calendar theorem; the [design and plan](se-schedule-generalization.md)
states the semantics, concerns and proof route. This file fixes the obligations
and records which are closed.

## Methodology

1. **The target and the boxes are fixed.** A box's statement, the target theorem
   and the baseline semantics change only with explicit approval from the
   project owner. Lack of progress is never a reason to reword, split into a
   weaker box, or drop a box.
2. **A box closes only on a checked theorem.** The theorem must prove the
   box's obligation with its stated quantifiers, build under the warning-strict
   project build, and use only the standard axioms. Name it under "Evidence".
   Helper lemmas, a narrower fragment, an example instance, archived code, or
   mathematics in documents do not close a box; record them under "Partial
   evidence".
3. **Positive and negative claims have the same standard.** A proposed
   sufficient condition counts only when proved for the stated object. A
   counterexample counts only when it fixes one valid source sequential
   equilibrium and one admissible configuration and shows that every native
   sequential equilibrium changes the required joint law. A failed comparator
   refutes that comparator, not the box.
4. **Work an item as long as it is fruitful.** When an item stalls, record
   what was tried and why it failed, then either continue with a new idea or
   bring the obstruction to the project owner with a proposed change. Do not
   change the box to fit what was proved.
5. **Small models are evidence, not closure,** unless their premises are
   derived from the actual runtime.
6. **Reopen boxes explicitly.** If a cited theorem is removed, archived or
   invalidated, uncheck its box in the same change.

## Target

Fix the program of the intended game (every owned commitment holds a value and
every owned reveal opens; see [two sources](se-two-sources.md)), its initial law
and utilities, the forfeit pass with a forfeit strictly above the payoff range, the
bounded raw runtime, a builder satisfying `AsyncContract` with reaction and
inclusion bounds that fit every deadline, the observation rule, the audit
backend and a deposit strictly above the deterrence bound, before choosing an equilibrium of the intended game.
Every sequential equilibrium of the intended game has a sequential equilibrium
of the bounded raw runtime for the forfeit-compiled program under that builder
that preserves the joint law of initial parameters, public results and realized
net payoffs, and charges and forfeits no player on its paths. The native
equilibrium may depend on the builder. Stage S is the sequentialized graph;
stage C adds concurrent bindings under the barrier order. The audit backend is
the authentic partial sampler with conditional coverage until box W closes.
Players are finitely many throughout.

The earlier target, preservation of every sequential equilibrium of the source
game with withholding priced by the program's own failure branch, is refuted in
a small model: `scripts/experiments/censored_disclosure_probe.py` (game G2)
fixes an honest source equilibrium whose deterrence rests on the responder's
reply to withholding, and an admissible builder that censors unprotected late
openings by value, under which no native sequential equilibrium preserves the
joint law. It is not pursued.

## A. Model

- [x] **A1. The runtime matches the baseline semantics.** Every operation in
  the semantics table of the [design](se-schedule-generalization.md) is
  implemented as stated; in particular there are no message copies, readiness
  credentials are attached only after prerequisites complete, and packet
  verdicts read only signed content, readiness evidence and the final record.
  Evidence: row by row, for `EventGraphRuntime.reactiveApplication` with an
  arbitrary deadline configuration and observation rule, under arbitrary player
  responses and every scheduler.
  Readiness: exactly the ready strategic events carry an activation timestamp,
  none in the future, at every initialized history
  (`reactive_history_invariant`); a timestamp is set to the clock of the
  transition in which its event becomes ready and is never restarted
  (`reactive_transition_activationStart`); it is kept until the event completes
  (`reactive_respond_progress`, `reactive_environment_progress`). The state has
  no grant cursor (`EventGraphRuntime.State`).
  Clock: a response never moves the clock (`reactive_respond_clock`) and a
  scheduler command moves it by one exactly for `EnvironmentCommand.advanceClock`
  (`reactive_environmentStep_clock`); the source runtime's deadline is the
  event index plus one (`runtime_deadline`).
  Binding: acceptance records the submitted handle and its immutable typed
  meaning, failure for an unprepared or wrong-typed candidate
  (`handle_commitment_eq`, `submitStep_commitment_fixed`,
  `handle_lookup_of_not_fresh`); the environment sees the same envelope for
  every private meaning (`reactiveBinding_observation`).
  Resolution: canonical FALSE is silence
  (`canonicalServiceDecision_resolution_false`); TRUE whose owner-local
  validation fails is silence (`canonicalServiceDecision_resolution_unvalidated`);
  TRUE whose validation succeeds emits the opening of the owner's accepted
  handle with the validated value and its authentic certificate
  (`history_canonicalServiceDecision_resolution_validated`). The packet
  language (`EventGraphRuntime.Payload`) has no withholding payload.
  Silence: a silent response transmits nothing (`trafficStep_silent`);
  resolution expiry executes source FALSE with publication failure
  (`environmentStep_expire_resolve_eq`) and changes no public binding omission
  (`missedBinding_expire_of_not_binding`, `missedBindingBy_expire_of_not_binding`),
  and a charge needs a traffic verdict or such an omission
  (`serviceAudit_charge`).
  Binding expiry: executes source failure (`environmentStep_expire_bind_eq`)
  and, without an accepted handle, produces the public omission read from the
  record (`missedBinding_expire`, `State.publicView_missedBinding`).
  Authorship: every envelope in the network is a fresh emission recorded in its
  author's recall (`history_provenance`, `trafficStep_submit`), and pending and
  ledger identifiers stay distinct (`idsDistinct_history`).
  Causal evidence: every emitted packet carries exactly the token issued by the
  public view recorded with its response, so a present token means the
  prerequisites had completed in that view (`history_emissionTokens`,
  `history_emission_token_issued`, `history_network_tokens`); inclusion rejects
  a missing or foreign token (`reactiveApplication_handle_of_not_tokenValid`).
  Packet verdict: the audit's verdict depends on the traffic only through the
  signed envelopes and otherwise only on the settled record of final public view
  and receipts (`sourceServiceAudit_congr`); a packet of a completed event is
  permitted only with an accepting receipt and settled content
  (`SettledRecord.permits_eq_false_of_settled`, `SettledRecord.permits_of_accepted`).
  Enforcement: one charge per owner, from the sampled authentic traffic or a
  public binding omission (`serviceAudit_charge`,
  `serviceAudit_charge_of_omission`), collected only at settlement
  (`settlementAudit_charge_unsettled`), while play continues and the omission
  persists (`reactiveMissedBindingInvariant`).
- [x] **A2. A non-calendar builder satisfies the contract.** Evidence: the
  fixed linear scheduler of
  [CommittedResolutionService](../Vegas/Examples/CommittedResolutionService.lean)
  satisfies `AsyncContract` and timeliness over unrestricted raw histories; the
  calendar instance is `rosterScheduler_asyncContract`.

## H. Intended game

- [x] **H. Intended-game preservation.** For every program of the intended game
  with finite commitment payload types and a finite initial law, and every
  sequential equilibrium of it, the forfeit-pass rewriting has a
  sequential equilibrium of the source game with the same joint law and no
  forfeit on its paths. Composed with S8 (and C2), it gives the target theorem.
  The intended game's commit menus offer only values the guard accepts,
  judged from the committer's observation. Hypothesis: the program is well
  formed, every guard being satisfiable at every reachable commit given its
  author's inputs, and every state in the initial law's support holds values in
  its commitment cells (both proved outside VegasCore);
  the forfeit pass forfeits the owner of every failed reveal (see
  [two sources](se-two-sources.md), point 1).
  Evidence: `intended_sequentialEquilibrium_preserved`
  ([IntendedPreservation](../Vegas/Game/IntendedPreservation.lean)), pinned in
  [Paper](../Paper.lean) as `Vegas.Paper.intended_sequential_equilibrium` with
  standard axioms. For every setup with `FiniteBindingTypes`, a finite initial
  law and `Setup.WellFormed`, every parameter reader and utility, every forfeit
  D with `utility high who - utility low who ≤ D` for all outcomes, and every
  sequential equilibrium of `Setup.intendedModel`, there is a sequential
  equilibrium of the source model under the value interface with payoff
  `forfeitUtility` (the utility minus D per failed reveal of the player), no
  failed reveal on any terminal history it reaches, and the intended joint law of
  typed terminal state and payoff. The intended model restricts the source menus
  (`Setup.intendedRestriction`): a commit offers the values the guard is
  predicted to accept from the owner's observation (`SourceGuard.predicts`), or
  every value when none is, which `Setup.WellFormed` rules out at every commit
  the intended game reaches; a reveal offers only opening. `Setup.WellFormed`
  is `GuardsSatisfiableFrom` from every initial configuration in the support
  together with values in every initial commitment cell. Route: the
  action-restriction extension without a common depth; no reveal of the intended
  game fails (`ProtocolState.failedReveals_eq_zero_of_intended`, from the run
  invariant `Config.Intended` and `Obligation.accepts_eq_predicts`); a source
  action outside the intended menu leaves its author indebted
  (`ProtocolState.indebted_of_deviation`), the debt survives every step
  (`ProtocolState.indebted_step`, using `Obligation.owner_eq_of_completedBy`) and
  is paid by a failed reveal of the author on every terminal continuation
  (`ProtocolState.failedReveals_pos_of_indebted`, `deviation_failedReveals_pos`).
  Players are finite, as in every SE result here.

## S. Serial stage, every contract builder

- [x] **S1. Honest execution.** For every source profile, the prescribed
  turn-counted clients give the source joint law of initial parameters, typed
  results and realized settlement, up to an error that vanishes with the
  deferral weight, and their every transmitted packet is permitted by the final
  record against arbitrary foreign raw play.
  Evidence: `sourceServiceClients_honestExecution`
  ([SourceServiceTurnSettlement](../Vegas/Game/SourceServiceTurnSettlement.lean)).
  For every scheduler satisfying `AsyncContract` and `AsyncTimely`, every turn
  timing and every source profile, the clients (the turn-counted policy of the
  profile's disclosure normalization, `sourceServiceClientProfile`, which has
  the profile's source law) give executions whose joint law of complete typed
  terminal state and realized settlement vector is within the total deferral
  weight in total variation of the source joint law, for every authentic
  partial audit and every deposit; and every packet of a player following its
  client is permitted by the settled record at every execution within the
  horizon, whatever the other players do. The error is the deferral weight
  itself; `geometricTiming_settlement_lawError` bounds it by
  `eventCount * weight` in the menu's information model, and
  `geometricTiming_deferral_tendsto` makes it vanish. The route couples the
  turn-counted run with its first-turn limit as laws of whole executions
  (`sourceServiceTurnPolicy_runToHorizon_bind_within`), so charged binding
  omissions and resolutions expired by deferral lie inside the error, and the
  first-turn limit's joint law is exact (`sourceServiceFirstTurn_settlement_law`:
  no public binding omission by `sourceServiceFirstTurn_no_miss`, permitted packets by
  `sourceServiceTurnPolicy_owner_settled`). The information-model form for
  admissible menus is `sourceServiceClients_settlement_lawError`.
- [ ] **S2. One common native consistency sequence.** One fully mixed family
  over source trembles, timing and raw responses, with exceptional mass
  negligible relative to clean reach on every information set that clean play
  eventually reaches, converging to a consistent native assessment.
  Partial evidence: `exists_consistent_prescribed_completion` (consistent
  rational completion at free sites, keeping prescribed limits and the terminal
  law); `exists_deferralWeights_faster` and `exists_source_timing_rates`
  (deferral rates negligible against given source scales);
  `runBehavioral_withinTV_of_supported_choices`. The correspondence used for
  the copied/free split is defined: `CorrespondsIntended` (every state along a
  native history decodes at its completed prefix to a point of the intended
  game and every recorded response was canonical; prefix-closed by
  construction) and `correspondingAgents` (agents at which a corresponding
  history decides, a function of the information state)
  ([AsyncIntendedCorrespondence](../Vegas/Game/AsyncIntendedCorrespondence.lean)).
  No native sequence over the actual runtime is constructed.
- [ ] **S3. Joint source and traffic law at every native information set.**
  Actual reach weights couple legal source actions, chance, public results,
  original own recall and traffic, including foreign WAIT likelihoods and
  hidden builder history, so that native beliefs are derived, not chosen.
  Partial evidence: `mixed_bob_reach_bound` for the example;
  `bayesBelief_bind_eq_conditional_passage` (beliefs at a site as conditional
  passage laws, abstract).
- [ ] **S4. WAIT comparisons.** At every retained owner input, every whole
  continuation that waits, including later attempts under selective inclusion
  and expiry, is bounded by source comparisons at the same assessment.
  Superseded on the current route (owner-approved): under the S8 timing split,
  waiting at an owner's corresponding turn is chosen by rational completion, so
  no source comparison is needed; this box applies again only if the route
  changes.
  Partial evidence (forfeit side of the comparisons): the native decoding
  advances by the source step of the decoded action at every completion
  (`SourceResidual.step`); from a decoding in the intended game a completion
  stays in it or is a departure of the event's actor, who is then indebted
  unless the departure is a failed binding
  (`SourceResidual.intended_or_departure`); and a decoded debt is paid by a
  failed reveal on every terminal history of terminal play from it, under any
  players and any scheduler that completes play
  (`decoded_indebted_failedReveals`,
  [SourceServiceDecodedDebt](../Vegas/Game/SourceServiceDecodedDebt.lean)).
  No WAIT comparison is proved.
- [ ] **S5. Charged deviations before the first charge.** Every forbidden or
  unprescribed packet is bounded by the deposit times the actual change in
  conditional collection, uniformly over arbitrary later play.
  Partial evidence: under the final-record coverage hypothesis
  `FinalForbiddenEvidenceCoverage`, collection bounds under arbitrary later
  policies for signed constructor breaches
  (`signedContentBreach_collection_continuation_of_finalCoverage`),
  noncanonical commitment handles
  (`noncanonicalCommitment_collection_continuation`) and openings whose public
  guards fail (`guardFailingOpening_collection_continuation`), combined in
  `auditableServiceChoice_collection_committed`. `signedContentBreach_risk_excluded`
  and `auditableBreachAtSite_of_signed_witness` classify these packets per
  information site in the risk-menu restriction;
  `sequential_equilibrium_extends_of_local_collection` and
  `risk_sequentialEquilibrium_extends` extend an audited risk-menu equilibrium
  to the complete effective runtime, given backend coverage and a comparison
  for the other excluded responses;
  `asyncAuditDeposit_covers_gain` fixes the deposit per scheduler. Missing:
  private binding material, guard-passing uncertified capability and other
  unprescribed packets; coverage is assumed, not derived (box W2).
- [ ] **S6. Rational continuation after a sunk charge.** Once a charge is
  certain, continuations are rational under the remaining utility, and no
  further fine is counted.
  Partial evidence: `isSequentiallyRationalAt_iff_of_constant_collection`
  (when expected collection is constant across continuations, rationality is
  rationality under the base payoff).
- [ ] **S7. Remaining sites.** Sample, foreign, recorded and private
  representation sites have bounded gain at the same assessment.
- [ ] **S8. Composition.** The retained game is the risk menu
  (`Vegas/Pending/ReactiveRiskMenu.lean`). At every site whose history still
  corresponds to a history of the intended game, whatever the timing so far,
  play copies the decision content of the compiled equilibrium of the intended
  game (what to submit), while the timing (submit now or wait) is chosen by
  rational completion; an information set is copied when it contains such a
  history. At every other site play is free, chosen by rational completion. H and S1–S7 compose into
  the target theorem for stage S, with the joint law and no charge or forfeit
  on paths.
  Partial evidence: `exists_sequentialEquilibrium_limit_of_copied_comparisons_of_lawError`
  ([CopiedSiteLimit](../GameTheoryExtensions/Analysis/Protocol/CopiedSiteLimit.lean)),
  the abstract limit theorem for this split: copied information agents play
  prescribed laws converging to a compiled limit, free agents are completed
  rationally (`exists_consistent_free_agent_completion`); if, for every residual
  choice at free agents, local gains at copied sites are bounded by source gain
  mixtures up to a vanishing error and the native observation laws approach the
  perturbed source laws, there is a native sequential equilibrium with the
  source law that agrees with the compiled limit at every copied site. Its
  premises are not constructed for the actual runtime. It is the pinned-tremble
  case of `exists_sequentialEquilibrium_limit_of_component_comparisons_of_lawError`
  (same module), which covers sites where the timing is completed: every agent
  plays a mixture of finitely many fully supported component laws with weights
  chosen by rational completion (`exists_consistent_component_completion`,
  [ComponentCompletion](../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean)),
  so an agent with a waiting and an acting component copies the acting law's
  content while completion chooses when to act; at every compared site each
  single choice is negligible, bounded by a source gain mixture, or bounded by
  the gain of a mixture of the agent's own components at the same index (the
  latter discharged for a choice trembled inside its component by
  `withLaw_comparison_gain_le_mix_add`), and both obligations may assume the
  weights are optimal among component mixtures. Source side for the
  intended game: `Setup.intended_auditedSource` (every intended SE is the limit
  of a fully mixed Bayes sequence and is rational for the audited utility of
  store and collection probabilities, at the intended horizon), with
  `Setup.auditedUtility_runtime` (the same utility is the audited terminal
  payoff on the runtime) and `TerminalAudit.clean_of_law_eq` (a law equality on
  readout and collection probabilities with a charge-free source gives no charge
  on paths and the joint settlement law)
  ([IntendedAuditedOutcome](../Vegas/Game/IntendedAuditedOutcome.lean)).
- [ ] **S9. Validation.** The stage-S theorem is pinned in `Paper.lean` with
  standard axioms, the calendar theorem is derived as its instance, and every
  cited evidence declaration is in its dependency closure.
  Partial evidence: `intended_audited_raw_sequentialEquilibrium`
  ([IntendedServiceCompilation](../Vegas/Game/IntendedServiceCompilation.lean))
  composes H with the calendar theorem at the forfeited utility: for a
  well-formed setup, every intended-game equilibrium has an audited bounded raw
  runtime equilibrium with the intended joint law of terminal store and payoff
  realized as settlement, no charge and no failed reveal on its paths; pinned
  in `Paper.lean` with standard axioms. It is the
  calendar runtime only, under the calendar theorem's audit assumptions, and its
  deposit is fixed for the forfeited utility, whose range grows with D times
  the number of reveals. The censored-opening verdict deferred under A1 is not
  changed.

## C. Concurrent stage

- [ ] **C1. Information commutation.** Under the barrier order and an adaptive
  public order, native information and pending traffic of independent bindings
  commute, without exposing unexecuted foreign values.
- [ ] **C2. Concurrent theorem.** The target theorem holds for barrier-order
  graphs, pinned with standard axioms.

## W. Operational watcher

- [ ] **W1. Reporting.** The abstract audit sample is refined by reports of
  observed signed envelopes delivered before settlement under the same bounded
  inclusion assumption as gameplay.
- [ ] **W2. Derived coverage.** The audit's conditional coverage is derived
  from the observation rule and report delivery instead of assumed.
- [ ] **W3. Refinement theorem.** The target theorem holds with the
  operational reporting in place of the abstract sampler.
