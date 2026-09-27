# End-to-end sequential-equilibrium proof checklist

## Fixed target

For the full ordinary VegasCore source language, fix the program, initial
distribution, utilities, bounded native interface, backend service, audit rule
and deposits **before choosing a source equilibrium**. Prove that every source
sequential equilibrium has a sequential equilibrium in the full bounded raw
runtime with the same joint initial-type, public-result and realized net-payoff
law.

The source retains private inputs, fresh commitments, public chance, guards and
withholding. The final runtime retains its raw responses and partial pending
observations. Authentication, observation coverage, protected service and
collectible deposits are explicit backend assumptions. The theorem does not
assume posterior correspondence, continuation dominance or a target equilibrium.
It asserts existence of a preserving target equilibrium; reflection of all
target equilibria and a fixed playerwise strategy translation are separate claims.

This target uses the existing bounded runtime. Unbounded interaction and a
cryptographic or EVM implementation are separate refinements.

## How boxes close

Each box denotes the complete stated mathematical obligation, with its original
quantifiers. It closes only when a checked theorem proves that obligation.
Helper lemmas, constructor cases and generic theorems with uninstantiated
compiler premises stay under their existing box. A narrower fragment does not
close a box. Checked proof files awaiting integration can supply mathematical
evidence; the final validation box additionally requires their integration.

These obligations stay fixed. A genuine obstruction or an explicit scope change
requires an explanation before changing them. If a checked proof is invalidated,
its box must be reopened explicitly. The boxes have unequal costs and are not a
percentage estimate.

## Source to permitted runtime

- [x] **S1. Full-language execution and settlement correspondence.** Every
  admitted source profile, compiled by the existing final-opportunity policy,
  has the correct source readout and realized settlement law, including fresh
  bindings, chance and guarded disclosure. This is an initialized-law result.
  Evidence: `sourceServiceCompiledProfile_readout_law` in
  [SourceServiceLaw.lean](../Vegas/Game/SourceServiceLaw.lean) and
  `sourceServiceCompiledProfile_settlement_law` in
  [SourceServiceAudit.lean](../Vegas/Game/SourceServiceAudit.lean).

- [x] **S2. One common native consistency sequence.** From an original
  consistent source assessment, construct the actual fully mixed timed native
  profiles, their Bayes beliefs, and one common subsequence converging at all
  native information sites to a consistent assessment. No normalized-source
  equilibrium is assumed. Evidence: `exists_sourceService_timed_consistent` in
  [SourceServiceTimedConsistency.lean](../Vegas/Game/SourceServiceTimedConsistency.lean).
  This establishes consistency, not rationality or outcome preservation of the
  resulting limit.

- [ ] **S3. Information correspondence at every native decision.** Derive the
  actual conditional information laws throughout every source constructor and
  every intermediate owner visit. Account for private source intentions,
  timing, replay and passive observations using the original source
  assessment. A joint law only at event boundaries does not close this box.
  The event-boundary joint law is checked in
  [SourceServicePrefixFactorization.lean](../Vegas/Game/SourceServicePrefixFactorization.lean);
  actual owner-visit Bayes posteriors and original-assessment comparisons are
  checked in [SourceServiceBayes.lean](../Vegas/Game/SourceServiceBayes.lean) and
  [SourceServiceAssessment.lean](../Vegas/Game/SourceServiceAssessment.lean).
  Foreign and implementation-only visits need no information law: every legal
  response at such a site has the same complete continuation law at every
  history of the site, so its comparison holds for every belief.

- [ ] **S4. Sequential incentives for every permitted native choice.** Bound
  every actual local native deviation by comparisons in the original source
  assessment, along the common sequence from S2. Include waiting, replay,
  binding and guarded disclosure; any comparison error must vanish uniformly
  as needed by the SE limit theorem. A terminal-law equality does not close this
  box. The site-by-site interface is checked in
  [SourceServiceLocalComparison.lean](../Vegas/Game/SourceServiceLocalComparison.lean);
  public-sampling sites, foreign visits, and owner visits after a recorded
  binding or opening have checked zero-gain comparisons, and unsent owner
  bindings an exact simulation by original source deviations
  ([SourceServiceForeignComparison.lean](../Vegas/Game/SourceServiceForeignComparison.lean),
  [SourceServiceForeignDisclosure.lean](../Vegas/Game/SourceServiceForeignDisclosure.lean)).
  Unsent owner disclosures remain; the
  [completion plan](se-completion-plan.md) orders the remaining work.

- [ ] **S5. Full-language source-to-permitted-runtime SE theorem.** Combine
  S1–S4 into an actual compiler theorem: every original source SE has a permitted
  native SE with the required joint law. Prove the law of the resulting
  assessment limit, rather than assuming that it is the final-opportunity
  strategy from S1. The initialized equality for every timed approximant is
  checked in [SourceServiceTimedLaw.lean](../Vegas/Game/SourceServiceTimedLaw.lean);
  rationality and the resulting limit law still require S3–S4.

## Permitted runtime to full runtime

- [x] **R1. Repair across any remaining complete-event suffix.** Starting from
  matched executions at an event boundary, couple the actual original suffix
  with one fixed legal repair implementation. Prove both marginal laws,
  retained-history reachability, and the alternatives of matching observations,
  persistent forbidden-traffic evidence or public binding omission. Evidence:
  `remaining_events_stopped_coupling` in
  [SourceServiceRemainingRepair.lean](../Vegas/Game/SourceServiceRemainingRepair.lean).
  The arbitrary active-decision entry is the separate obligation R2.

- [x] **R2. One legal repair for every whole native deviation.** Start at any
  retained information site, including intermediate visits. Couple the entire
  native continuation to one legal behavioral policy shared by all hidden
  histories at that site, against unchanged opponents. Derive the starting
  invariants from actual histories and identify both laws with the standard
  continuation evaluators. Evidence: `active_evaluator_stopped_coupling` in
  [SourceServiceEvaluatorRepair.lean](../Vegas/Game/SourceServiceEvaluatorRepair.lean).
  The reference recall and repair policy are fixed before the hidden history;
  both marginals are the actual `runBehavioralFrom` evaluator laws.

- [x] **R3. Actual conditional settlement dominance with one fixed deposit.**
  Instantiate the gain and collection bounds on the continuations from R2,
  uniformly over paired profiles and finite beliefs. Infer a sufficient finite
  deposit from the declared utility bounds and conditional collection rate
  before choosing an equilibrium. Do not count a sunk fine twice or require
  increasing punishment after a departure. Evidence:
  `sourceService_continuation_settlement_comparison` in
  [SourceServiceContinuationComparison.lean](../Vegas/Game/SourceServiceContinuationComparison.lean).
  It constructs one repair before quantifying over arbitrary finite beliefs and
  instantiates the actual evaluator coupling and fixed deposit bound.

- [x] **R4. Permitted-to-full-runtime SE theorem.** Instantiate the existing
  restriction-extension theorem with R2–R3, supply rational consistent play at
  new information sites, and restore all bounded raw response aliases. Preserve
  the initialized joint result and realized settlement law. No continuation
  comparison may remain an unproved compiler premise. Evidence:
  `sourceService_audited_raw_equilibrium_extends` in
  [SourceServiceRawExtension.lean](../Vegas/Game/SourceServiceRawExtension.lean).
  Source readouts and their initial-parameter/public-result projections satisfy
  the proved raw-normalization invariance condition.

## End-to-end closure

- [ ] **E1. Compose the full compiler theorem.** Compose S5 and R4 for the fixed
  target above. Its public statement quantifies over every source SE and leaves
  only the stated source, utility and backend assumptions. Check that shared
  parameters, readouts and deposits agree across the composition.

- [ ] **E2. Validate and audit the delivered claim.** Integrate the proof into
  the build roots; pass the warning-strict build and repository proof/document
  gates; audit the final theorem's dependency closure for unproved obligations;
  and align the paper and artifact claims with its exact assumptions and scope.
  Document the justification and impact of the backend assumptions separately
  from their mathematical consequences. Commit and push the reviewable result.

The [stack document](se-compilation-stack.md) gives the detailed proof map and
backend assumptions. The [results roadmap](se-preservation-roadmap.md) records
other checked results and research boundaries. This checklist is the completion
ledger for the full-language end-to-end theorem.
