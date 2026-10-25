# Mathematics and reusable proof APIs

The local tree has remaining opportunities in both mathematical bounds and
proof reuse. The strongest mathematical one is a normalization improvement:
unit-payoff differences cost half the L1 distance of equal-mass vectors, and
added mass costs its share of the final total, rather than its ratio to the old
total. Three existing convergence arguments can also be replaced by the
already available generic PMF convergence API.

This review changes no production theorem, dependency source, option or SE
target. The reviewed baseline is `ec4de15c`. GameTheory remains read-only.

## Scope and method

The declaration surfaces of all 75 modules under `GameTheoryExtensions` and
all 25 modules under `GameTheoryExtensionsTests` were extracted and screened.
They contain respectively 14,478 and 3,548 physical lines, excluding the root
aggregators. This is surface coverage, not a claim of reading every tactic.

The selected deep reads covered the finite-weight, conditioning and convergence
arguments in ActionSplitting, ApproximateLumping, CounterpartBounds, Domination,
EqualMassFibers, Expectation, NestedPosterior, ObservedChoice, OptionalDomination,
PresentConditional, ProductTransport, RestrictedDisintegration, SiteDraw,
SwapTransport, Support, TotalVariation and Uniform. Selected protocol bodies
were read in BehavioralContinuity, ComponentCompletion, ContinuationDecision,
FreeKeyedPools, KeyedPools, LastDecision, LocalSimulationLimit, Perturbation,
ProjectedBeliefTransport, RetainedDeviation, SourceGainTransport,
SupportedChoiceContinuation and UniformPolicyLimit. ObservableEnforcement and
QuasilinearBounds were also checked for assumption/claim mismatches.

Six Interaction mathematical-interface surfaces were extracted. The new deep
reads there were the scheduler command-density argument and the actual
ReactiveAliasStrategy convergence consumer. GameTheory deep reads were limited
to the owning parts of Core.Signature, Math.Probability.Convergence,
Conditioning and ConditionalObservation, and the assessment-compactness
interface. No fresh whole-GameTheory audit is claimed.

Generated declaration surfaces and inventories are under
`ephemeral/proof-review-current`; the durable checked sources are in the
[probe appendix](checked-probes.md). Body-level
estimates below come from the displayed complete proofs and their adapters;
they do not use a comparison of the old and corrected lexical body inventory.

## 1. Respect normalization in finite-weight comparisons

**High mathematical value; high confidence in the kernels; feature growth.**

The current owning layers are:

- `GameTheoryExtensions/Math/Probability/SwapTransport.lean:25`,
  `abs_sum_mul_sub_le_sum_abs`;
- `SwapTransport.lean:43`, `abs_normalized_sub_base_le`;
- `SwapTransport.lean:126`, `abs_normalized_sub_le_of_base_agree`;
- `GameTheoryExtensions/Math/Probability/ProductTransport.lean:44`,
  `sum_abs_div_sum_sub_div_sum_le`;
- `ProductTransport.lean:198`, `sum_abs_div_sum_add_sub_div_sum_le`;
- `ProductTransport.lean:264`, `NearProductWeights.errorBound`.

The unit-payoff lemma is valid for unnormalized weights and therefore uses the
full L1 distance. Its two uses inside `abs_normalized_sub_base_le`, however,
compare vectors whose totals are both one. Subtracting one half from the payoff
cancels the common total, and its absolute value is at most one half. Thus

```
|sum p*f - sum q*f| <= (sum |p-q|)/2        when sum p = sum q and 0 <= f <= 1.
```

This fact needs neither nonnegative p/q nor any new finiteness assumption beyond
the existing finite sums. In the actual normalized-weight proof the needed
nonzero normalizers are already proved: the regularPos and scaledPos witnesses; the full
weight total is positive because it contains the positive regular part and
nonnegative irregular weights.

There is a second independent cancellation. Write M for the positive regular
total and S for the nonnegative added total. The existing generic normalization
lemma can be used with its *actual* relative error S/M and lower-total factor
1+S/M, instead of error eta and lower factor one. Its L1 conclusion is

```
2*(S/M)/(1+S/M) <= 2*eta/(1+eta)          when S <= eta*M.
```

No extra `0 <= eta` hypothesis is required: it follows from S>=0, M>0 and the
existing smallness premise. This strengthens the existing contamination helper
under exactly its present assumptions.

Consequently the same SwapTransport proof route can replace the current
two-sided `4*rho + 4*eps/(1-eps)` by

```
2*rho/(1+rho) + 2*eps/(1-eps).
```

This is a proposed assembled bound, not a checked production theorem. The two
generic kernels are checked independently. All original requirements remain:
positive regular base totals and scales, relative pointwise errors below one,
nonnegative actual weights, finite indexing types, and actual agreement of the
normalized base payoff. Centering does not permit deleting those guards.

Complete consumer routes exist in two families:

1. `GameTheory.Math.Probability.abs_normalized_sub_base_le` ->
   `abs_normalized_sub_le_of_base_agree` ->
   `Vegas/Game/OnePacketKeyedRecords.lean:120/150`,
   `recordLaw_near_of_baseLaw` ->
   `Vegas/Game/OnePacketLateRecords.lean:416`, its common error formula and
   vanishing-error proof. Replace the displayed constants/formula and prove
   convergence of the new `rho/(1+rho)` term. No scheduler, payoff, deviation or
   SE premise changes are needed.
2. `GameTheory.Math.Probability.sum_abs_div_sum_add_sub_div_sum_le` ->
   `NearProductWeights.errorBound` and
   `sum_abs_nativeLaw_sub_sourceLaw_le:291` ->
   `GameTheoryExtensions/Analysis/Protocol/ProjectedBeliefTransport.lean:142/147/196`,
   `projectionErrorBound`, its limit theorem and
   `GameTheory.Protocol.InformationModel.sum_abs_projectedBelief_sub_le`. The actual weights are constructed there
   at line250. Its remainder term becomes `2*eta/(1+eta)`; positive information
   mass, Bayes consistency and the projection/factorization facts remain.

Estimated whole production cost: **35–90 additional physical lines**, including
the centering kernel, stronger contamination proof, the normalized-mass
identities and all visible formula/limit adapters. This is a strengthening,
not compression. Independent regression should test a disjoint two-point pair
attaining half-L1 and an added-mass example attaining `eta/(1+eta)` on unit
payoffs. Do not claim an optimal perturbation constant: the relative-error term
can potentially be sharpened further, but this review does not prove that.

## 2. Use the generic PMF convergence API in its remaining local consumers

**Low risk; high confidence; approximately 25–35 net fewer production lines.**

The frozen foundation already owns both required facts:

- `GameTheory/GameTheory/Math/Probability/Convergence.lean:407`,
  `PMFConvergesPointwise.bind`, with a varying kernel on arbitrary carriers;
- `Convergence.lean:450`, `pmfConvergesPointwise_mix_zero`.

Three local proofs still perform atomwise multiplication and scalar-limit
algebra themselves:

- `GameTheoryExtensions/Math/Probability/ActionSplitting.lean:116–140`,
  `PMF.split_converges`. Its 17-line body recovers the unique canonical branch,
  expands atoms and multiplies limits. Instead bind the convergent normalized
  laws through the varying split kernel; each fixed kernel converges by
  `pmfConvergesPointwise_mix_zero`. The checked replacement body has five lines.
  The exact actual consumer is
  `Interaction/ReactiveAliasStrategy.lean:89–104`,
  `splitPolicy_converges`. Full support, legal-menu identification, fixed
  canonical representative and the original single noise sequence remain.
- `GameTheoryExtensions/Analysis/Protocol/Perturbation.lean:37–52`,
  `BehavioralAssessment.perturb_strategy_converges`. The nine-line scalar proof
  is the existing core theorem at the strategy coordinate; a two-line proof
  suffices. Its public statement and all clients stay unchanged.
- `GameTheoryExtensions/Analysis/Protocol/LastDecision.lean:94–107`, the own
  coordinate in `consistent_update_of_reach_invariant`. Use the same theorem
  after unfolding the local response. The foreign-coordinate constant limit
  and the whole Bayes/reach argument remain. Actual consumers are
  `Vegas/Examples/LateLeak/Intended.lean:408` and
  `SettleLateIntended.lean:518`.

The bound includes the necessary local unfolding and coordinate-update
adapters. No new public convergence lemma, aliases, finite-carrier premise,
compactness proof or GameTheory edit is needed. In particular the simplification
does not claim that strategy convergence alone determines off-path beliefs.

## 3. Posterior/readout naturality also holds on impossible observations

**Useful strengthening; high confidence; small feature growth.**

`GameTheory/GameTheory/Math/Probability/ConditionalObservation.lean:384`,
`map_fiberPosterior_readout`, currently requires a positive observed marginal.
Its exact naturality identity also holds when that marginal is zero. The
reason is specific and explicit: `fiberPosterior` in `Conditioning.lean:160`
falls back to its *input law*. Thus the two sides become respectively
`law.map read` and the same `law.map read`. Absence of the image marginal follows
by composition of PMF maps.

Add this genuinely stronger local extension and use it in
`GameTheoryExtensions/Math/Probability/NestedPosterior.lean:33`,
`observation_fiber_mass`. Its present proof is unchanged except that the positive
premise disappears and the new naturality fact replaces the supported-only
readout call. The existing zero-safe joint-density theorem already supplies
the remaining algebra.

There are four real callers:

- `Vegas/Game/QualifiedBinding/OrdinaryContinuation.lean:3655`;
- `Vegas/Game/QualifiedBinding/Likelihood.lean:9222`;
- `Likelihood.lean:9946`;
- `Vegas/Game/QualifiedBinding/ForeignPosterior.lean:278`.

The `possible` witness at OrdinaryContinuation3634–3636 is used only by that
mass identity and can be removed. The issuedPresent witness at
Likelihood9938–9942 likewise has only that one use and can be removed.
The oldSupported proof at ForeignPosterior262 **must stay**: it is also passed
to `posterior_append_observation:276`, where an actual posterior interpretation
is required. Likewise do not indiscriminately delete the reference-support
facts used elsewhere in the large likelihood proof.

Estimated whole production cost: **5–15 additional lines**, including the local
zero-mass naturality proof and all four ports, offset by those two unused
positivity derivations. Exact number requires an owner pilot. This result is
not a Bayes interpretation at a null observation, is not valid for arbitrary
independently chosen fallback laws, and does not equate arbitrary off-path
beliefs. GameTheory's positive-mass owner can remain unchanged.

## 4. Finish using the existing profile and expectation algebra

**Small, low-risk cleanup; conservative 15–30 net fewer production lines.**

- `ComponentCompletion.lean:63–74`, `bind_component_update`, is the existing
  `GameTheory.Profile.map_update` from `Core/Signature.lean:201` with coordinate
  map `fun who law => law.bind (component who)`. Its actual use is in the
  expected-utility calculation at ComponentCompletion174–175. Make the profile
  map explicit at that use and delete the one-use helper where elaboration
  permits; otherwise the existing concrete adapter can be proved by the core
  theorem without duplicating the coordinate case split.
- The ten-line local `same` fact at ComponentCompletion195–204 is exactly
  `Profile.update_eq_self`. Apply the existing lemma directly at line205.
- `Expectation.lean:148–155`, `expect_comm_of_support_finite`, can use the
  immediately preceding stronger `expect_comm_of_support_finite_left`, supplying
  the inner law's finite-support integrability. Keep both old finiteness
  premises in this specialization. Its direct consumers include
  `ContinuationDecision.continuation_value:83` and the finite averaging route;
  the original statement is preserved.
- `ApproximateLumping.lean:64–90`, `expect_three_parts`, rederives right-scalar
  expectation twice. `Expectation.expect_mul_const:126` already owns it.
  Its actual consumer is `withinTV_map_of_two_outcomes:95`, then
  `Vegas/Game/OnePacketOwnerStep.lean:413`. Keep the integrability arguments for
  sums and differences; only the duplicate scalar calculations go away.
- `ContinuationDecision.lean:151` has an unused trailing `OtherState` variable.
  Deleting it has no mathematical/API consequence.

The profile-map instance is covered by the checked generic probe. The full
ComponentCompletion and scalar/finite-expectation owner migrations have not
been compiled by this review. A single line of `simp` at a call site is not
assumed to work until the actual dependent signatures have been exposed.

## Checked experiments and current limits

Root checked `NormalizedWeightsProbe.lean` with the exact central setup:
**PASS**. Both unit_payoff_half_l1 and contamination_ratio
are proved. This does not yet check the assembled SwapTransport or projected
belief consumer migrations.

Root checked `ConvergenceReuseProbe.lean` with the same strict setup:
**PASS**. It checks the exact perturbed coordinate, varying
split-kernel convergence, updated own coordinate and generic dependent
PMF-bind/profile-update identity. No production edit is present.

Root checked `PosteriorNaturalityProbe.lean` with the same strict setup:
**PASS**. Both the all-observation naturality theorem and the
exact accumulated-mass proof with its positive premise removed are proved.
The four production consumer migrations remain unchecked.

## Rejected or lower-value directions

- Removing global finite histories from ContinuationDecision or
  UniformPolicyLimit is not a cosmetic class cleanup. The former needs actual
  continuation-utility integrability, posterior/response Fubini and reward
  integrability, not just equality of total expectations. The latter uses
  compactness of *varying whole-policy deviations* and a payoff bound in its
  subsequence contradiction. No concrete infinite-history client was found;
  no unused replacement hierarchy is recommended.
- `exists_pooled_bestResponses` could restrict an arbitrary pool carrier to the
  finite image of the finite player set. Current keyed pools already make that
  restriction (`KeyedPool` is an option of a range subtype). No actual client
  drops a meaningful restriction, so the extra casts/fallback weights are not
  justified by the present consumers.
- The support-based scalar comparison or the conditional-comparison
  predicates should not be called unsound solely because total `expect` has a
  zero default on nonintegrable inputs. Actual LocalSimulationLimit derives a
  uniform bound on every source gain at lines123–167, so the source lottery is
  integrable. A new guarded predicate would need a separate equivalence proof
  and a worthwhile consumer; this review found neither a correctness bug nor a
  worthwhile predicate split.
- The existing service-contract, hidden-permutation, event-tagged error and
  conditional-prior recovery-SE boundaries are not relisted as new findings.
  Their prior dispositions remain relevant. The new normalization constants
  improve finite bounds; they do not solve any of those separate factual or
  semantic obligations.
- No GameTheory-only cleanup from the completed queue is reopened. All proposed
  local reuse invokes its existing public owners; none copies a frozen proof
  merely to rename it.
