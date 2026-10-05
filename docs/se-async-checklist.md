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

Fix the program, initial law, utilities, bounded raw runtime, a builder
satisfying `AsyncContract` with reaction and inclusion bounds that fit every
deadline, the observation rule, the audit backend and the deposit, before
choosing a source equilibrium. Every source sequential equilibrium has a
sequential equilibrium of the bounded raw runtime under that builder that
preserves the joint law of initial parameters, public results and realized net
payoffs, and charges no player on its paths. The native equilibrium may depend
on the builder. Stage S is the sequentialized graph; stage C adds concurrent
bindings under the barrier order. The audit backend is the authentic partial
sampler with conditional coverage until box W closes.

## A. Model

- [ ] **A1. The runtime matches the baseline semantics.** Every operation in
  the semantics table of the [design](se-schedule-generalization.md) is
  implemented as stated; in particular there are no message copies, readiness
  credentials are attached only after prerequisites complete, and packet
  verdicts read only signed content, readiness evidence and the final record.
  Partial evidence: readiness credentials and the final-record verdict are
  implemented; players transmit only fresh envelopes they author, and ledger
  and pending identifiers stay distinct on every history
  (`ReactiveApplication.idsDistinct_history`). Silent withholding is
  implemented: a canonical resolution response is silence or the successful
  authentic opening (`serviceDecision_resolution_cases`); resolution expiry
  executes source FALSE with publication failure
  (`environmentStep_expire_resolve_eq`); and the audit charges only a traffic
  verdict or a public binding omission read from the record
  (`serviceAudit_charge`, `PublicView.missedBinding`), so an expired resolution
  is never charged. Divergence: the contract still accepts an explicit
  withholding call, which executes FALSE and whose packet the settled verdict
  forbids (`SettledRecord.SettledContent`), instead of rejecting it. The remaining
  rows have not been checked against the implementation one by one.
- [x] **A2. A non-calendar builder satisfies the contract.** Evidence: the
  fixed linear scheduler of
  [CommittedResolutionService](../Vegas/Examples/CommittedResolutionService.lean)
  satisfies `AsyncContract` and timeliness over unrestricted raw histories; the
  calendar instance is `rosterScheduler_asyncContract`.

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
  negligible relative to clean reach on every information set, converging to a
  consistent native assessment.
  Partial evidence: `exists_consistent_prescribed_completion` (consistent
  rational completion at free sites, keeping prescribed limits and the terminal
  law); `exists_deferralWeights_faster` and `exists_source_timing_rates`
  (deferral rates negligible against given source scales);
  `runBehavioral_withinTV_of_supported_choices`. No native sequence over the
  actual runtime is constructed.
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
  (`Vegas/Pending/ReactiveRiskMenu.lean`): canonical responses while an owner
  is clear, and every unforbidden bounded response once the owner has a public
  binding omission or recalls its own unprotected opportunity, with free play there
  chosen by rational completion. S1–S7 compose through
  `exists_sequentialEquilibrium_limit_of_local_comparisons_of_lawError` and
  `sequentialEquilibrium_extends_of_continuation_unclocked` into the target
  theorem for stage S, with the joint law and no charge on paths.
- [ ] **S9. Validation.** The stage-S theorem is pinned in `Paper.lean` with
  standard axioms, the calendar theorem is derived as its instance, and every
  cited evidence declaration is in its dependency closure.

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
