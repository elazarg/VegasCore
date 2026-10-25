# Mathematics and reusable proof APIs

The mathematics findings are implemented in the local tree. Finite normalized
comparisons have sharper bounds, posterior/readout naturality covers null
observations, and the remaining convergence and algebra consumers use existing
owning APIs. GameTheory source and its gitlink remain unchanged. No source
semantics, SE target or checklist statement changes follow from these results.

The exact-source checks and normal full build pass under the central strict
options. The [implementation ledger](../proof-review-progress.md#current-findings)
records acceptance of every production owner and actual consumer.

## Scope and measurements

The review screened declaration surfaces of all 75 modules under
GameTheoryExtensions and all 25 test modules in the review inventory: 14,478
and 3,548 physical lines, excluding root aggregators. Selected complete proofs
and actual consumers were read in the finite-weight, conditioning,
convergence, expectation, protocol-completion and continuation families. Six
Interaction interface surfaces were screened, with deeper reads of scheduler
density and private-alias convergence. GameTheory inspection covered selected
owning probability, signature and compactness APIs. This is not a fresh
line-by-line audit of every proof in those directories.

Measurements use review checkpoint `610ae97f` and the frozen physical-line
inventory. They include each implemented family and its concrete adapters,
not overlapping lexical proof windows. Probability helpers added for the
product-retention timing result and signature propagation for conditional
priors belong to their respective families and are excluded here.

| Implemented mathematics family | Production-line change |
| --- | ---: |
| Three convergence consumers | −24 |
| Profile and expectation cleanup, including its actual adapters | −29 |
| Null-safe posterior/readout law and all four callers | −4 |
| Normalized bounds, product transport, projected beliefs and record formulas | +63 |
| Total for these original mathematics families | +6 |

The [normalization regression module](../../GameTheoryExtensionsTests/NormalizedWeights.lean)
adds 52 lines separately. Test aggregators, Paper guards and documentation are
outside these production measurements. Strengthening grows the library; the
53 lines removed by API reuse are the compression result.

## Normalized finite-weight bounds

The finite comparison owner now provides two different mathematical scopes:

- [GameTheory.Math.Probability.abs_sum_mul_sub_le_sum_abs](../../GameTheoryExtensions/Math/Probability/SwapTransport.lean#L32)
  bounds the change of a unit payoff by the full L1 distance for arbitrary real
  weights. Equal totals and nonnegativity of the weights are unnecessary.
- [GameTheory.Math.Probability.abs_sum_mul_sub_le_half_sum_abs](../../GameTheoryExtensions/Math/Probability/SwapTransport.lean#L42)
  improves the coefficient to one half when the totals agree. Signed weights
  remain allowed. The unequal-mass result is retained because this extra
  premise gives the sharper theorem a different scope.

For finite sums the sharper identity is

```
|sum p*f - sum q*f| <= (sum |p-q|)/2
when sum p = sum q and 0 <= f <= 1.
```

Subtracting one half from the payoff cancels the common total. Every normalized
vector in the actual consumer has total one: the proof establishes positive
regular, scaled-base and full-weight totals before invoking the equal-total
bound.

[GameTheory.Math.Probability.sum_abs_div_sum_add_sub_div_sum_le](../../GameTheoryExtensions/Math/Probability/ProductTransport.lean#L198)
now bounds contamination by

```
L1(normalize(m+s), normalize(m)) <= 2*eta/(1+eta).
```

The hypotheses remain finite indexing, nonnegative regular and added weights,
a positive regular total, and added total at most eta times the regular total.
Writing those totals as M and S, the existing normalization API is instantiated
with relative error S/M and lower-total factor 1+S/M. Its bound is
2*(S/M)/(1+S/M), which is at most the displayed expression. Nonnegativity of eta
follows from the existing premises; no extra eta premise was added.

The assembled production results are:

- [GameTheory.Math.Probability.abs_normalized_sub_base_le](../../GameTheoryExtensions/Math/Probability/SwapTransport.lean#L74):
  one-side unit-payoff error at most `rho/(1+rho) + eps/(1-eps)`.
- [GameTheory.Math.Probability.abs_normalized_sub_le_of_base_agree](../../GameTheoryExtensions/Math/Probability/SwapTransport.lean#L168):
  two-side unit-payoff error at most `2*rho/(1+rho) + 2*eps/(1-eps)`.

The two-side result permits different finite carriers and positive scales. It
still requires positive regular base totals, nonnegative actual weights,
relative pointwise error below one, the irregular-mass bounds, a unit payoff,
and exact agreement of that payoff's normalized base expectations. Centering
removes none of those guards. No optimality claim is made for the separate
relative-error term.

Both concrete routes are implemented:

1. [Vegas.recordLaw_near_of_baseLaw](../../Vegas/Game/OnePacketKeyedRecords.lean#L73)
   consumes the stronger two-side theorem.
   [Vegas.keyedRecord_near](../../Vegas/Game/OnePacketLateRecords.lean#L83)
   and [Vegas.OnePacketBaseInputs.lateRecords_of_keyed](../../Vegas/Game/OnePacketLateRecords.lean#L308)
   use the same sharper formula and the limit of `rho/(1+rho)`. The base-law,
   Bayes, scheduler, payoff and actual site guards remain explicit; the separate
   conditional-prior propagation is not inferred from the numerical bound.
2. [GameTheory.Math.Probability.NearProductWeights.errorBound](../../GameTheoryExtensions/Math/Probability/ProductTransport.lean#L278)
   and [GameTheory.Math.Probability.NearProductWeights.sum_abs_nativeLaw_sub_sourceLaw_le](../../GameTheoryExtensions/Math/Probability/ProductTransport.lean#L306)
   use `2*remainderRatio/(1+remainderRatio)` for irregular mass. This propagates
   to [GameTheory.Protocol.InformationModel.projectionErrorBound](../../GameTheoryExtensions/Analysis/Protocol/ProjectedBeliefTransport.lean#L142),
   [GameTheory.Protocol.InformationModel.sum_abs_projectedBelief_sub_le](../../GameTheoryExtensions/Analysis/Protocol/ProjectedBeliefTransport.lean#L198)
   and [GameTheory.Protocol.InformationModel.tendsto_sum_abs_projectedBelief_sub](../../GameTheoryExtensions/Analysis/Protocol/ProjectedBeliefTransport.lean#L322).
   The factor/fiber contribution remains
   `2*(factorError+fiberError+factorError*fiberError)/((1-factorError)*(1-fiberError))`.
   The actual weight constructor, finite sums, product/fiber identities, Bayes
   consistency and positive information masses are preserved.

## Convergence through existing owning APIs

[GameTheory.Math.Probability.PMFConvergesPointwise.bind](../../GameTheory/GameTheory/Math/Probability/Convergence.lean#L402)
and [GameTheory.Math.Probability.pmfConvergesPointwise_mix_zero](../../GameTheory/GameTheory/Math/Probability/Convergence.lean#L450)
already supply the varying-kernel and vanishing-mixture limits. Three local
consumers now instantiate them instead of recomputing atomwise scalar limits:

- [PMF.split_converges](../../GameTheoryExtensions/Math/Probability/ActionSplitting.lean#L116)
  binds the convergent normal laws through their varying split kernels. Each
  kernel tends to its fixed canonical representative by the mixture theorem.
  Its actual reactive consumer is
  [Interaction.ReactiveApplication.SubmissionNormalization.splitPolicy_converges](../../Interaction/ReactiveAliasStrategy.lean#L89).
- [GameTheory.Protocol.InformationModel.BehavioralAssessment.perturb_strategy_converges](../../GameTheoryExtensions/Analysis/Protocol/Perturbation.lean#L37)
  applies the same mixture theorem at the prescribed strategy coordinate.
- The own-coordinate branch of
  [GameTheory.Protocol.InformationModel.consistent_update_of_reach_invariant](../../GameTheoryExtensions/Analysis/Protocol/LastDecision.lean#L40)
  uses the mixture theorem after coordinate replacement. Foreign coordinates
  retain their constant limits, and the Bayes/reach-invariance argument remains.
  Actual uses remain in the [LateLeak intended equilibrium](../../Vegas/Examples/LateLeak/Intended.lean#L408)
  and [settlement intended equilibrium](../../Vegas/Examples/LateLeak/SettleLateIntended.lean#L518).

The three complete owners remove 24 lines. Statements, fixed canonical
representatives, legal-menu guards and the common noise sequence are unchanged.
Strategy convergence alone still determines no off-path posterior or incentive.

## Posterior naturality at null observations

[GameTheory.Math.Probability.fiberPosterior_map_readout](../../GameTheoryExtensions/Math/Probability/NestedPosterior.lean#L13)
proves posterior/readout naturality for every observation, including zero mass.
The positive case uses the unchanged foundation theorem. In the zero case,
the defined fallback is the input law, so both sides reduce to the same
pushforward of that law. Composition of PMF maps identifies the two zero-mass
marginals.

[GameTheory.Math.Probability.observation_fiber_mass](../../GameTheoryExtensions/Math/Probability/NestedPosterior.lean#L48)
uses that stronger law and no longer needs a positive previous observation.
The accumulated observation's mass is its previous mass times the posterior
atom of the new coordinate, with the joint-density identity also valid at zero.

All four concrete calls are updated:

- [ordinary continuation](../../Vegas/Game/QualifiedBinding/OrdinaryContinuation.lean#L3652);
- [likelihood increment](../../Vegas/Game/QualifiedBinding/Likelihood.lean#L9222);
- [selected likelihood cylinder](../../Vegas/Game/QualifiedBinding/Likelihood.lean#L9942);
- [foreign posterior](../../Vegas/Game/QualifiedBinding/ForeignPosterior.lean#L278).

The two witnesses used only by the mass identity are removed. The foreign
posterior's support proof remains because its genuine posterior-append step
also needs it; support facts used elsewhere in the likelihood proof remain.
The enclosing private source-prefix cylinder-fold theorem also drops its
unused positivity premise and its sole caller drops the redundant witness.
The complete law-and-caller family removes four lines.

This is an identity for the defined total posterior. It gives no Bayes
interpretation at a null observation, does not apply to arbitrary unrelated
fallback laws, and equates no arbitrary off-path beliefs.

## Profile and expectation reuse

The complete cleanup bundle removes 29 production lines:

- [GameTheory.exists_pooled_bestResponses](../../GameTheoryExtensions/Analysis/Protocol/ComponentCompletion.lean#L92)
  uses [GameTheory.Profile.map_update](../../GameTheory/GameTheory/Core/Signature.lean#L201)
  for the actual dependent PMF-bind coordinate map, deleting its one-use local
  case split. [GameTheory.Profile.update_eq_self](../../GameTheory/GameTheory/Core/Signature.lean#L106)
  also replaces the local same-profile proof.
- [GameTheory.Math.Probability.expect_comm_of_support_finite](../../GameTheoryExtensions/Math/Probability/Expectation.lean#L148)
  instantiates the stronger one-sided finite-support theorem with the other
  law's actual finite-support integrability. Both finite-support premises of
  the specialization remain. The actual
  [GameTheory.Protocol.InformationModel.ContinuationDecision.continuation_value](../../GameTheoryExtensions/Analysis/Protocol/ContinuationDecision.lean#L67)
  still consumes it.
- The private three-part expectation calculation in
  [ApproximateLumping](../../GameTheoryExtensions/Math/Probability/ApproximateLumping.lean#L64)
  uses [GameTheory.Math.Probability.expect_mul_const](../../GameTheoryExtensions/Math/Probability/Expectation.lean#L120)
  instead of duplicating right-scalar expectation proofs. Sum/difference
  integrability remains explicit. Its actual route continues through
  [GameTheory.Math.Probability.withinTV_map_of_two_outcomes](../../GameTheoryExtensions/Math/Probability/ApproximateLumping.lean#L89)
  to the [one-packet owner-step consumer](../../Vegas/Game/OnePacketOwnerStep.lean#L413).
- The unused trailing type variable in the continuation-decision owner is
  deleted without changing a declaration's mathematical statement.

## Verification and remaining acceptance

The following strict isolated checks pass without compiled output artifacts:

- Exact production source for ProductTransport, SwapTransport and the whole
  ProjectedBeliefTransport owner, with only their owned imports filtered from
  the combined source. This checks the assembled one-/two-side bounds, actual
  projected-weight constructor, projected comparison and limit adapters.
- The 52-line finite regression module: disjoint added mass attains the
  contamination bound, the stronger helper is instantiated, signed equal-total
  weights use the half-L1 theorem, and a null observation returns the input law.
- All three migrated [appendix experiments](checked-probes.md): normalization,
  convergence reuse and posterior naturality call their current public owning
  APIs with every original statement and exact standard-axiom guard retained.

The normal warning-strict build additionally checks the complete import graph,
dependent completion owner, all four posterior callers, reactive convergence
clients and native record formulas. All 5,771 jobs pass. The candidate axiom
roots use exactly the standard axioms, and the guarded API replays pass.

## Directions not implemented

Removing global finite histories from the continuation-decision or uniform
policy-limit interfaces remains a separate generalization. It needs actual
continuation-utility integrability, posterior/response Fubini and, for varying
whole-policy deviations, the compactness/tightness argument. Equal total
expectations do not supply those premises. No concrete infinite-history client
justified a replacement hierarchy in this review.

Pooled best responses could restrict an arbitrary pool carrier to the finite
image of finite players, but the actual keyed-pool interface already does so.
Extra casts and fallback weights offered no useful client restriction to remove.

Total expectation's default on nonintegrable inputs does not alone invalidate
the current comparison predicates. The inspected local-simulation consumer
derives a uniform source-gain bound and hence actual integrability. No predicate
split or shadow guarded hierarchy is added without an equivalence proof and
an actual consumer. Frozen GameTheory-only cleanup is likewise not copied into
a parallel local implementation.
