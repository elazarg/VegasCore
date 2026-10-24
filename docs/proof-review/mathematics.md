# Mathematical proof review: GameTheory and GameTheoryExtensions

The mathematical baseline is `7272a57e`. No production Lean file, submodule file,
compiler option or frozen theorem target was changed. Isolated proposals below
are checked experiments, separate from production results. The main review
links their complete source and replay command.

## Coverage and limitations

The inventory covers the entire assigned trees, including opt-in experiments
and tests. `lean-defs.py` generated
`ephemeral/proof-review/math-surfaces.lean`: 92,786 lines of declaration surfaces.
The following counts come from the current files under the named directories;
root-level package/aggregator files outside these directories are not included.

| Tree | Modules | Physical lines | Lexically detected proof-bearing declarations | Lexical proof-body lines |
| --- | ---: | ---: | ---: | ---: |
| `GameTheory/GameTheory` | 616 | 173,782 | 7,407 | 76,943 |
| `GameTheoryExtensions` | 69 | 14,069 | 421 | 6,534 |
| `GameTheoryExtensionsTests` | 19 | 3,065 | 173 | 1,183 |

Proof counts use the lead's `ephemeral/proof-review/declarations.csv` inventory and are approximate
lexical measurements, not a Lean AST analysis. Module/physical-line counts are
direct file counts. The lead's count of 619 GameTheory files additionally
includes files outside the 616-file public-directory tree.

| Family | Surface coverage | Bodies and consumers examined in depth |
| --- | --- | --- |
| Core, 47 modules/18,270 lines | Full declaration inventory; focused signature searches | Approximate/ExpectedUtility, Transform, MixtureSimulation, UtilitySimulation/Transfer; substantial Shapley, Arrow, MixedPotential, FictitiousPlayPotential and CorrelatedDominance proofs |
| Protocol, 42 modules/15,159 lines | Full declaration inventory | PolicyMeasure finite-coordinate construction, measurability, integration and guarded values; StrategicRealization round trips and unilateral laws; behavioral information/Bayes/finite-horizon APIs |
| Probability, 36 modules/8,681 lines | Full declaration inventory | Expectation/map/bind/conditioning/measure/extended expectations, domination, conditional observation/comparison, convergence, tightness, compactness, finite sampling; sampled interaction APIs |
| Analysis, including 59 protocol modules | Full declaration inventory and largest-body inventory | AgentCompletion, RestrictionCompletion/Extension, BeliefTransport, AssessmentCompactness, ExtensiveFormPerfection, uniform/local gain limits; sampled stochastic contraction and repeated folk theorem proofs |
| Languages/bridges | Full declaration inventory; detailed FOSG/MAID surfaces | FOSGToEFG policy equivalences, predecessor and scaled law proofs; FOSGToEFGStrategic; MAID ToEFG path uniqueness and strategic consumers |
| Stochastic/repeated | Full module/declaration inventory | Stochastic.Kuhn prefix-law/integrability/discounted adapters; ordinary and monitored discounted Bellman splits; sampled monitoring self-generation/one-shot surfaces |
| Mechanism/fair division/knapsack | Full declaration-name scan | QuasiLinear weak monotonicity, Groves utility/truthfulness, InformationDesign guards; sampled RoundRobin EF1 invariant; algorithm/correctness separation inspected |
| Epistemic/evolutionary/cooperative/congestion/finite | Full declaration-name scan | Sampled approximate-agreement conditional bounds; inspected corresponding integrability and execution/correctness surfaces, not every proof body |
| Extensions, all 69 modules | Full declaration-name scan, including structures and tests' applications | PublicScheduling; restriction/retained deviation; component/copy/local completion; stopped laws; all main probability transport/bounds families; enforcement and monetary laws |
| Extensions tests, all 19 modules | Full declaration-name scan | Correlated audit/bounds, proportional and passage specialization tests; scope/counterexample conclusions in coalescing, correlated sequential gap, monitored signaling and preservation contracts |
| GameTheory tests and experiments | All included in the machine surface/size inventory | Largest experimental bridge families identified; hostile bridge/strategic test consumers searched. Most experimental/test proof bodies were not reviewed line by line. |

This is broad mining with targeted deep review, not an assertion that every one
of 8,001 detected proof bodies received a manual audit. No logical semantic bug
was found in the inspected proofs. Two stale theorem descriptions and an unused
certificate surface are identified below; these are not allegations of an
unsound Lean theorem.

## Ranking and interpretation of savings

The ranking weighs proved mathematical strengthening, reusable downstream
benefit, and implementation risk, rather than raw line count alone. All savings
are **unverified estimates** of whole proof/API/adapter changes; headers,
new helper proofs and caller adapters are charged. They are not build-time or
binary-size claims. Overlapping opportunities must not be added together.

| Rank | Finding | Main benefit | Estimated net physical-line saving | Status/confidence |
| ---: | --- | --- | ---: | --- |
| 1 | Derive proportional scale finiteness; remove local finite-history premise | Strictly stronger local Bayes transport | 0–25 | Full scratch proof PASS centrally; high |
| 2 | One discrete pushforward measurability/integration lemma | Shrink four repeated finite-coordinate arguments | 50–100 | Scratch primitive PASS centrally; high |
| 3 | Guarded absolute-expectation contraction | Shrink decorrelation, affine and approximation proofs | 70–120 | Scratch primitive PASS centrally; high |
| 4 | Make passage-based restriction completion the general owner | Eliminate two implementations of the same extension result | 130–230 | Existing checked subsumption test; high math/medium integration |
| 5 | Unite `UnitClose` and event total variation | One probability-closeness calculus, fewer proofs | 45–110 | Direct proof plan; high |
| 6 | Charge only active choices in continuation domination | Improve quantitative bounds, especially single mover | No guaranteed reduction; likely +25–70 | Existing product API supplies mechanism; high math |
| 7 | Reuse generic prefix-law adapters in stochastic Kuhn | Remove bounded special-case proof duplication | 40–85 | Existing stronger theorems; high |
| 8 | Countable/tight consistency completion | Remove unnecessary global finite-site/fiber assumptions | −20 to +15 (may grow) | Existing compactness APIs; high |
| 9 | Pooled best responses need integrability, not finite outcomes | Infinite-outcome finite-component games | −15 to +5 (may grow) | Local proof inspection; high |
| 10 | Counterpart bounds should use fiber multiplicity | Much sharper negligible-belief bounds | −10 to +10 | Current proof already contains multiplicities; high |
| 11 | Retained-deviation comparison as law-level domination | Separate restriction semantics from finite-sum calculus | 15–55 for bounded version | Existing gated-law API; medium |
| 12 | Coordinate-equivalence payoff-law transport | Shrink FOSG/MAID strategic bridge adapters | 35–80 | Existing coordinate/update/expectation APIs; high |
| 13 | Finite-set equivariance and inversion in Shapley proofs | Replace bespoke swapping; expose useful coalitional identities | 35–100 for symmetry; inversion unestimated | Symmetry high; inversion medium |
| 14 | Share scalar discounted Bellman algebra | Reduce ordinary/monitored/stochastic proof plumbing | 25–65 | Two inspected repetitions; high |
| 15 | Finish sound-detection result described in enforcement prose | Correct theorem inventory; useful exact obstruction/possibility result | Growth of ~40–90 if proved | Documentation mismatch confirmed; proof plan high |

Negative savings mean growth. Several valuable strengthenings should be selected
for mathematics or API quality, not advertised as compression.

## 1. Proportional scale finiteness is derivable

**Owners and declarations.**
`GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean:58`,
`bayesBelief_projection_of_proportional_reach`; its mass identity at line 37.
Consumer: `Analysis/Protocol/PublicScheduling.lean:1281`,
`PublicScheduler.bayesBelief_lift_map`. Base bound:
`GameTheory/GameTheory/Protocol/BehavioralBayes.lean:52`, `informationMass_le_one`.

**Old proof.** The proportional theorem asks for `scale ≠ ∞`. Public scheduling
proves this by assuming the entire expanded history type is finite, making each
fiber finite, then summing likelihoods bounded by one. This is the only use of
`[Finite S.protocol.History]` in that local Bayes theorem's body.

**Stronger statement.** Drop *scaleFinite* from proportional Bayes transport.
The raw history antichain makes its information mass at most one. The existing
fiber identity says `rawMass = scale * sourceMass`, and *sourcePositive* makes
the second factor nonzero. Therefore
*ENNReal.lt_top_of_mul_ne_top_left* proves scale finiteness. Drop the global
finite-expanded-history hypothesis from the local public-scheduler Bayes result.
Keep positivity, antichains, public-history recoverability and nonterminal
source-fiber assumptions exactly where currently used.

**Proof and risk.** A complete scratch version is in
`ProportionalBayesProbe.lean`, including the strengthened local theorem, not only
the scalar observation. The lead checked this file with the exact central Lake
options: session 58992, exit 0. Existing `informationMass_projection_of_proportional_reach`
already is the appropriate normalization identity; do not import or reprove the
Boolean restriction normalization theorem for this purpose. The final expanded
SE theorem still needs its other finite-history assumptions. This does not
establish an infinite-history SE preservation theorem. Low mathematical risk;
some public argument-order and proof-irrelevance elaboration work remains if
integrated. Estimated saving 0–25 lines after exposing the derivation; the main
gain is a strictly stronger result.

## 2. Finite-coordinate measure arguments repeat the same discrete pushforward step

**Owner.** `GameTheory/GameTheory/Protocol/PolicyMeasure.lean`:
`aemeasurable_run_mass:218`, `lintegral_run_mass:264`,
`aemeasurable_runPolicy_mass:998`, and
`lintegral_runPolicy_mass_eq_runMixedWithin_of_queriedInfos:1045`.

**Old proof.** Each defines a finite coordinate restriction, its assembly and a
PMF marginal, then repeats the proof that this marginal's countable support has
full measure, an arbitrary mass function is AE measurable there, and composition
with the measurable restriction is AE measurable. The forward and arbitrary
policy-measure branches share this argument despite different marginal laws.

**Reusable primitive.** If `project : Source → Target` is measurable and
`measure.map project = law.toMeasure` for a PMF `law`, any function of `project`
is AE measurable, assuming measurable singleton target atoms and a measurable
value carrier. No countability of the entire target is required. For an
ENNReal-valued function, *lintegral_map'* then transports its integral.

**New proof shape.** Keep the compiler-specific finite coordinates and the
`run_apply_congr_of_queriedInfos` factorization. Replace the repeated
`hfull/hmass/hmassMapped` construction by the primitive, followed by an AE
congruence for the exact mass function. Use the same map-integral identity for
both finite-coordinate distributions. Do not package the desired complete
policy realization theorem into a new certificate: the reusable input is only
a measurable projection and its independently proved PMF marginal.

**Evidence and cost.** `DiscretePushforwardProbe.lean` supplies both elementary
lemmas and passed the lead's central-options check, session 60754, exit 0.
Existing owners are `Math/Probability/Measure.lean`'s
`aemeasurable_of_countable_full_set` and Mathlib *lintegral_map'*; the probe does
not replace those engines. Estimated saving 50–100 lines including ~20–35 new
helper/API lines and four adapters. Initial larger estimates would wrongly count
projector-specific factorization as removable. Countable-support and AE
measurability details make integration medium effort despite elementary math.

## 3. Add the missing guarded L1 contraction once

**Owners.** `GameTheoryExtensions/Math/Probability/ProductDecorrelation.lean:32`,
`abs_expect_mul_sub_le_of_uncorrelated`; `AffineDecorrelation.lean:12`,
`abs_expect_affine_sub_le_of_decorrelated`; `ApproximateLumping.lean:38`,
the unit-bounded expectation comparison; repeated upper/lower comparisons in
`TotalVariation.lean`. A further instance is
`GameTheory/GameTheory/Analysis/Stochastic/Discounted.lean`,
`abs_expect_sub_le_dist`.

**Old proof.** Product decorrelation proves two-sided inequalities for both the
product error and its mean, repeatedly rebuilding boundedness/integrability
certificates and using `expect_mono` on positive and negative absolute errors.
The affine theorem repeats the same absolute-expectation argument. The base
library currently exposes a constant absolute bound, not the general L1 form.

**New statements.** For `PayoffIntegrable law f`, prove
`|expect law f| ≤ expect law (abs ∘ f)`. For integrable `f,g`, derive
`|expect law f - expect law g| ≤ expect law (fun x => |f x-g x|)`.
The existing summability definition and Mathlib *norm_tsum_le_tsum_norm* give the
first in roughly five lines; `expect_sub` gives the second. The scratch file
`ExpectationContractionProbe.lean` contains both and passed the lead's central
options check, session 82481, exit 0.

**Strengthening.** The affine theorem's `[Finite H]` is used to obtain
integrability, not for the covariance calculation. Replace it in a general
version by an actual integrability certificate for the arbitrary payoff; the
other factors are already bounded. Alternatively require integrability of the
absolute affine error, which together with the bounded baseline implies payoff
integrability. An inequality involving the totalized `expect` of an unguarded
error is NOT a substitute: a divergent series can totalize to zero. Preserve the
guards.

**Accounting/risk.** New calculus ~15–25 lines; adapters/reorganized bounds
~20–40; remove ~110–175 inspected repeated lines: net ~70–120. This overlaps
some TV simplifications in finding 5. High confidence in the mathematics;
turning the product-error proof into a short calculation still requires a
careful complete consumer rewrite, not mass simp-argument deletion.

## 4. Passage-based completion already subsumes the common-depth implementation

**Owners.** Base `Analysis/Protocol/RestrictionCompletion.lean:32`,
`exists_consistent_extension`, and `RestrictionExtension.lean`,
`sequentialEquilibrium_extends_of_continuation`; extension
`Analysis/Protocol/PassageRestrictionExtension.lean:350,504`, their
`..._unclocked` counterparts. Existing test:
`GameTheoryExtensionsTests/PassageRestrictionExtension.lean:25`,
`clocked_of_unclocked`.

**Old proof.** Clocked and passage-based completion repeat the same positive
site-mass product, relative tremble choice, reference agent support, pinned/free
agent construction, common subsequence and retained-profile convergence. The
passage version changes how retained beliefs are read and dominated; it does
not require common depth.

**Proposed owner/API.** Keep one general completion implementation with the
passage argument. Its conclusion already is the old conclusion with depth and
clock assumptions removed. Existing consumers can instantiate that stronger
theorem directly. The checked `clocked_of_unclocked` test is evidence of actual
subsumption, not a suggested new conjecture.

**Dependencies and plan.** The current submodule cannot import
GameTheoryExtensions. Either upstream the passage/probability lemmas and make
the general theorem the base owner, or keep external consumers on the general
owner while explicitly documenting that base-package cleanup is a separate
change. Do not introduce a reverse dependency or leave two full implementations
under a new compatibility alias. Audit every old retained-belief and
continuation comparator hypothesis when replacing callers. The SE capstones'
statements and scope can stay fixed.

**Savings/risk.** ~130–230 net lines after moving—not counting a move as a
deletion—and adapting callers. Algebraic `ratio_domination_bound` is separately
duplicated verbatim in base `Math/Probability/Domination.lean:88` and passage
extension line 30. Exposing one lower-level scalar ratio lemma, or deriving the
event bound by pushforward, saves ~25–35 more lines; charge its API and avoid
double-counting this in the overall estimate. Mathematical subsumption high
confidence; cross-package ownership is the material engineering risk.

## 5. `UnitClose` and `WithinTV` describe the same distance

**Owners.** `Math/Probability/ApproximateLumping.lean:26`, `UnitClose`, and
`Math/Probability/TotalVariation.lean:24`, `PMF.WithinTV`.

**Exact equivalence.** `WithinTV e μ ν` implies `UnitClose e μ ν` by applying
`WithinTV.expect_sub_le` in both directions with interval `[0,1]`. Conversely,
apply `UnitClose` to each event indicator and use the indicator expectation
identity. Arbitrary ambient carriers are permitted; unit payoffs are bounded,
so all needed expectations are integrable. No measurability issue occurs for
ordinary discrete PMFs.

**New proof shape.** Pick one owning closeness predicate. The event form has
the larger existing map/bind/domination API. Rephrase approximate lumping using
that API instead of maintaining an independent bounded-test calculus. The
two-outcome/classes results still require their actual decoding hypotheses;
the equivalence does not discharge those premises.

**Immediate independent reductions.** `WithinTV.bind_right` is the constant
error case of `bind_right_expect` after moving the latter earlier.
`WithinTV.of_bind_point` is the domination theorem with retained factor equal
to the selected branch's probability: `timing index * branch index a` is one
nonnegative term of the bind mass. Its existing ~50-line expectation proof can
become a short domination calculation. Existing core probability domination
and `toReal_bind_apply` supply the adapters.

**Accounting/risk.** Equivalence/API cost ~15–30, affected callers ~10–25,
removed duplicate derivations ~70–150; estimate 45–110 net, overlapping finding
3. If moving TV into the base probability library would violate current
package scope, prove equivalence externally first and measure one consumer;
do not create an API alias solely for compatibility. High mathematical
confidence, medium dependency-surgery cost.

## 6. Continuation domination charges inactive players unnecessarily

**Owner.** `Analysis/Protocol/SupportedChoiceContinuation.lean:29,49,84`,
`runBehavioralFrom_one_domination_of_choices`,
`runBehavioralFrom_domination_of_supported_choices`, and its TV consequence.

**Current statement.** A common per-choice factor `r` yields continuation
domination `r^(Fintype.card Player * fuel)`. This is safe but pays a factor for
every player at every step, including chance steps and inactive players whose
legal choice law is identically the point mass at `none`.

**Stronger building block.** Use per-player factors in the one-step product,
setting the factor to one at inactive players. The existing
`prob_pi_ge_prod_mul` already accepts a factor function. Prove that inactive
choice types are subsingletons and both profile laws are the same pure law.
For a single-mover protocol, the per-step factor is at least `r`, hence the
global domination is `r^fuel` and TV loss `1-r^fuel`. Against a unilateral
change, unchanged opponents also have factor one, leaving only actual focal
decision occurrences to count.

**Missing hypotheses.** The factor lies in `[0,1]` for the monotone exponent
comparison. State single-mover/active-cardinality or a proved bound on focal
decision count explicitly; source-support-only lower bounds must remain
source-support-only. Administrative/terminal absorption steps contribute no
extra loss. Do not infer active counts merely from syntactic event counts.

**Payoff insight/risk.** This can materially improve tremble and comparison
constants in many-player implementations, without new probability or execution
semantics. It is useful even if code grows. Estimated new primitive+single-mover
adapter +25–70 lines; no compression claim. High confidence in one-step math;
support-dependent accumulated-exponent bookkeeping merits a focused hostile
test containing both chance and inactive steps.

## 7. Bounded stochastic Kuhn adapters reprove later general prefix-law adapters

**Owner.** `GameTheory/GameTheory/Stochastic/Kuhn.lean:625–735`:
`arbitraryPolicyMeasureStageIntegrable_of_bounded`,
`arbitraryPolicyMeasureStageExpectation_eq_behavioral_of_bounded`, and
`kuhn_arbitraryPolicyMeasure_discountedPayoff`. General versions already occur
at lines 741,766,802: `arbitraryStageIntegrable_of_prefixLaw`,
`arbitraryStageExpectation_eq_of_prefixLaw`, `discountedPayoff_eq_of_prefixLaw`.

**Old/new proof.** The bounded versions manually rewrite the same arbitrary
policy-measure prefix law into the behavioral PMF measure and transport
integrability/integrals. The later general theorems do exactly that from an
arbitrary prefix-law equality and actual guards, including hybrid deviations.
Move the general declarations before the specializations and instantiate them
with `kuhn_arbitraryPolicyMeasure_allFinitePrefixes` plus the existing bounded
behavioral integration and summability theorems. Keep the interpretation of the
fallback and policy measures unchanged.

**Scope.** The general statements already omit finite-action assumptions where
only the law equality is used and allow any real discount with a supplied
series guard. The bounded strict-discount forms remain convenient sufficient
conditions, not a second mathematical implementation. An `rg` caller search
found the bounded arbitrary-policy expectation adapters used locally in this
file; the general prefix-law adapters also serve the later hybrid discounted
deviation proofs.

**Accounting/risk.** No new general API required. Removing repeated bodies and
using the existing guarded equality should save ~40–85 lines after the
specializations and explicit proof witnesses. If unused specialization headers
are removed as well, update all local callers; do not count hypothetical deleted
public wrappers twice. High confidence; dependent proof arguments may need
proof-irrelevance/definitional equality cleanup.

## 8. Consistent completion can use countability and tightness already available

**Owner.** `Analysis/Protocol/ConsistencyCompletion.lean:29,56`,
`BehavioralAssessment.exists_consistent_completion_subsequence` and
`...exists_sequentiallyConsistent_subsequence`.

**Stronger statement.** For a prescribed strategy limit, replace finite
decision sites and finite information-history fibers by a countable family of
decision sites and uniform tightness of each sequence of belief laws. Run
`exists_subseq_pmfConvergesPointwise_pi_of_uniformlyTight`; compose the supplied
strategy convergence with the selected subsequence. For varying strategies,
require tightness of both strategy laws and belief laws and use the already
proved model-level
`GameTheory/Analysis/Protocol/AssessmentCompactness.lean:67`,
`exists_subseq_behavioralAssessmentConvergesPointwise_atSites_of_uniformlyTight`.
The latter already is used by `AgentCompletion`.

**Boundaries.** Tightness is a genuine missing hypothesis, not derivable from
countability: point masses can escape to infinity. This proves consistency
completion, not sequential rationality, local optimality, a uniform compiler,
or preservation of designated source beliefs. Preserving designated
projections still needs the current explicit projected convergence premises.

**Proof/cost.** The fixed-profile proof is the current ~15-line proof with a
different compactness call. The varying-profile proof can avoid its separate
ad hoc reconstruction by using model-level assessment compactness. A finite
specialization gets tightness via `uniformlyTight_of_finite`. Expect −20 to +15
net lines depending on the retained specialization surface; the benefit is a
stronger theorem with no new compactness machinery. High confidence. A useful
independent test uses infinitely many possible histories with a geometric
common dominating tail, plus an escaping point-mass counterexample to dropping
tightness.

## 9. Pooled component best responses do not need finite outcome carriers

**Owner.** `Analysis/Protocol/ComponentCompletion.lean:104`,
`exists_pooled_bestResponses`; its private `componentGame` at line 45.

**Current use of finiteness.** `[Finite F.sig.Outcome]` is used to construct
`G.HasIntegrableUtility utility`, where `G` is the game of component indices.
The fixed point operates over finite component simplices. The original
strategy carrier and the supports of the component laws may be infinite.

**Proposed statement.** Retain finite nonempty pool parts and continuity of
importance. Replace finite outcomes by actual integrability of every pure
component-profile law:
`∀ choice who, PayoffIntegrable (F.mixed.play (fun p => component p (choice p)))
  (fun outcome => utility outcome who)`.
This exactly supplies `G.HasIntegrableUtility`; existing polynomial payoff and
finite-component mixing lemmas handle subsequent steps.

**Why meaningful.** This permits countably/infinite supported outcomes with
bounded or otherwise integrable utility, while keeping the same conclusion and
same independent component-mixture semantics. It is not a certificate containing
the desired best-response conclusion; integrability is an independently
checkable analytic hypothesis.

**Plan/cost/risk.** Replace the local finite-outcome instance and integration
construction by the supplied hypothesis. Adapt finite-history consumers using
their existing finite-support integration proofs. Estimated API/adapter cost
0–15 additional lines, no substantial deletion expected. Test one infinite
outcome distribution with a bounded utility, not a merely renamed finite
fixture. High confidence from inspection of all uses of the outcome-finiteness
instance in the proof. This does not by itself remove finite histories from the
larger sequential completion theorem, whose compactness and continuity needs
are separate.

## 10. Negligible counterpart bounds can use fiber multiplicity

**Owner.** `Analysis/Protocol/ProjectedBeliefTransport.lean:100,144`,
`sum_reach_le_of_counterpart` and `sum_belief_le_of_counterpart`.

**Current proof exposes the better result.** It rewrites the sum over bad
histories as a sum over good histories of
`card {bad h | counterpart h = good} * reach good`, then bounds every fiber
cardinality by the cardinality of the entire information-history type.

**Stronger statement.** Accept a number `multiplicity` bounding the bad
preimage of each good counterpart. Replace the global-card factor by
`multiplicity * ratio`; an injective counterpart gives multiplicity one. The
proof is the same sum-fiber identity and a better cardinality inequality.
The existing *Fintype.card* result follows from the trivial fiber bound.

**Missing hypotheses.** The counterpart must still send every bad history to a
good one, the reach domination must hold for every bad history, and ratio is
nonnegative. For the normalized belief result retain Bayes consistency and
positive finite site mass. Multiplicity cannot be inferred from the mere
existence of a counterpart; several bad histories may share one witness.

**Insight/cost.** A large history tree can have a simple bounded-to-one repair
map. This removes a needlessly exponential site-cardinality penalty and can
change the asymptotic perturbation-rate requirement. The generalization costs
roughly −10 to +10 lines rather than promising compression. A test with two bad
histories sharing one good witness distinguishes the necessary multiplicity-two
bound from an invalid injective assumption. High confidence; no new game model
or normalization engine required.

## 11. Retained-policy expectation comparison belongs at the law level

**Owner.** `Analysis/Protocol/RetainedDeviation.lean:315`,
`expect_deviation_le_retained`, and line 416, `isεNash_extends_of_debt`.
Existing lower owner:
`Math/Probability/GatedExpectation.lean:26,65`,
`expect_option_le_of_dominated`, `expect_le_of_gated`.

**Old proof.** After establishing the actual embedded law domination and
absorbing debt classification, the proof assumes a finite entire target-history
type, chooses the least retained supported payoff, shifts both payoffs by that
floor, drops nonpositive outside terms, and reindexes a finite sum along the
history embedding. This is generic dominated-subprobability reasoning.

**First safe extraction.** Encode membership in the embedding image by an
optional source-history decoder. The domination of successful readouts is the
already proved `runBehavioral_embedded_le`; outside histories have payoff at
most the floor. Apply the existing gated expectation theorem rather than
repeating shifted-sum comparison. Keep debt absorption/incurrence and completion
in the protocol adapter.

**Stronger version.** With explicitly bounded source/target payoffs and a
declared floor, the comparison no longer needs a finite whole history carrier.
More generally, an actual coupling reconstructed from
`PMF.exists_residual_of_le` should remove even the attained-minimum requirement,
under actual payoff integrability and the existing outside-versus-all-source
support inequality. That latter strengthening needs a support proof for the
residual; do not claim it merely from integrability.

**Accounting/risk.** For the bounded version, generic decoder/adapter ~25–45
lines against ~60–100 removed finite-sum plumbing: net ~15–55. The fully
integrable residual-coupling version may grow by ~50–100 lines; useful math,
not a compression promise. Medium confidence until the optional decoder and
supported-residual cases are probed. Preserve all expectation guards in the
equilibrium adapter; law-level domination alone never supplies integrability.

## 12. Strategic bridges should consume coordinate equivalences and payoff laws

**Owners.** `GameTheory/GameTheory/Languages/Bridges/FOSGToEFGStrategic.lean:50,79,170`,
`projectBehavioral_update`, `translateBehavioral_update`,
`isεNash_serialized_iff_source`; `Languages/MAID/Strategic.lean`'s profile
equivalence application near line 402. Existing primitives:
`Core/Signature.lean`, `Profile.map_update`;
`Core/Transform.lean:279`, *Profile.unrelabelStrategies_update*;
`Core/Approximate.lean:49`, exact profile-equivalence transport;
`Math/Probability/ExtendedExpectation.lean:174,180`, observed-law transport.

**Old proof.** FOSG defines coordinatewise policy translations as whole-profile
functions, then manually proves coordinate update equations in both directions
and constructs forward/backward witnesses for the generic Nash equivalence.
It separately passes expectation-existence equivalences and extended-value
equalities derived from the same erased-history law. MAID repeats the pattern.

**New shape.** Expose the independently proved per-player behavioral policy
equivalence, use the standard profile relabeling/update lemmas, and add one
general theorem taking exact observed payoff-law equality for a coordinate
equivalence. Derive both `HasExpectation` guards and extended utility from that
law once. The law and equivalence are meaningful independently of equilibrium;
there is no new certificate whose field is the desired Nash statement.

**Stronger reachable results.** Since these are coordinatewise equivalences,
finite coalitional overrides also commute; group/strong Nash transfer is within
reach using existing `UtilitySimulation`/group Nash infrastructure. Coalition
utility must be compared jointly if the class couples players, as the existing
zero-sum/cone tests correctly demonstrate.

**Cost/risk.** Generic law transport and coordinate adapters ~40–65 lines;
remove ~80–145 manual witness/guard glue across reviewed consumers: net ~35–80.
Do not claim this for arbitrary profile bijections, which need not preserve
unilateral or coalition deviations. Keep the scaled source/serialized horizons
and full expectation-existence guards. High confidence.

## 13. Shapley proofs contain reusable finite-set mathematics

**Owner.** `GameTheory/GameTheory/Core/Shapley.lean:129`,
`shapleyValue_symmetric`; line 250, efficiency; line 612,
`unanimity_decomposition`.

**Concrete reduction.** Symmetry builds a custom swap of coalitions, proves
its domain/codomain property, inverse and cardinality preservation, then
reindexes the weighted sum. The map is the action of
`Equiv.swap first second` on a `Finset`. Existing finset/equivalence map
cardinality, inverse, membership and sum reindexing should eliminate most of
the custom `swapMember_*` machinery. A more useful public statement is
equivariance of Shapley allocation under arbitrary player relabeling; pairwise
symmetry follows by a transposition plus the existing value symmetry premise.

**Further building blocks.** Efficiency is a 243-line proof of cancellation of
weighted insertion edges on the Boolean lattice. A general weighted-coalition
edge-sum identity would expose the coefficient of each coalition value;
efficiency follows from the factorial-weight recurrence and boundary terms.
Unanimity decomposition is Boolean-lattice Möbius inversion, currently proved
by a bespoke interval-subset reindexing. Mathlib already has
`Combinatorics.Enumerative.IncidenceAlgebra` inversion, but its required
Boolean-lattice Möbius formula and dependency cost need checking. Do not claim
the inversion import alone replaces the proof; the searched file did not expose
a ready-made finite-set cardinality formula.

**Scope/cost.** Transposition refactor: ~35–100 net lines after useful
equivariance/API adapters; high confidence. General edge-sum and Möbius work:
medium confidence and no justified net-saving estimate until a finite-set probe
exists. The genuinely reusable target is finite-set sum/inversion algebra, not
a structure storing Shapley efficiency as a premise. Uniqueness still needs its
existing efficient/symmetric/null/additive hypotheses; none can be silently
dropped.

## 14. Discounted head/tail algebra should be proved below game models

**Owners.** `GameTheory/GameTheory/Repeated/Discounted.lean:223`,
`discountedContinuationPayoff_eq_head_add`; monitored analogue
`Repeated/MonitoringDiscounted.lean:299`, `discountedPayoff_eq_head_add_expected`.
Existing low owner: `Math/Discounted.lean`, `normalizedDiscountedSum`.

**Old proof.** Both game-model proofs split a weighted tsum at one, rewrite
`discount^(n+1)`, pull out the scalar and rearrange the normalization factor.
The ordinary theorem spends most of its body on this scalar calculation; the
monitored theorem repeats it after doing the genuinely different conditional
tower/interchange work.

**General statement.** For a real sequence `payoff` with
`Summable (fun n => discount^n * payoff n)`, prove
`normalizedDiscountedSum discount payoff =
 (1-discount)*payoff 0 + discount*
 normalizedDiscountedSum discount (fun n => payoff(n+1))`.
No positivity or strict-discount premise is needed for this algebraic identity;
summability is the operative hypothesis. Boundedness and `0≤discount<1` remain
sufficient conditions in game consumers.

**New proof.** The ordinary continuation theorem instantiates the sequence at
`start+n` and simplifies indices. The monitored theorem first uses its actual
conditional expectation/series interchange certificates, then invokes the same
identity. Prefix-law equality adapters in Stochastic.Kuhn are another potential
consumer, but no additional saving is counted there.

**Accounting/risk.** Scalar API/proof ~15–25 lines, two adapters ~10–20,
removed repeated scalar algebra ~50–100: net ~25–65. High confidence. Preserve
the monitored series integrability/interchange hypotheses: equal formal
geometric expressions do not justify exchanging a conditional expectation and
an infinite sum.

## 15. Enforcement prose describes an exact detector theorem that is absent

**Confirmed mismatch.** `GameTheoryExtensions/Analysis/Enforcement.lean:18`
says the largest sound detection probability equals the deviating mass outside
the lawful support. Current declarations are only `alarm_zero_iff` and
`alarm_zero_of_support_subset`. `Analysis/ObservableEnforcement.lean:6–11`
describes finite sound-sanction existence iff positive mass outside the admitted
set, but current declarations provide only monitored utility evaluation and its
expectation. An entire-tree search found no corresponding theorem there or in
the imported incentive-cone owner. This is prose outrunning checked results,
not a counterexample to an existing theorem.

**Reachable exact result.** For an admitted observation set `A`, a sound alarm
has firing probability zero at each admitted observation. Its detection under a
deviating law is at most `deviating(Aᶜ)`. The deterministic alarm firing exactly
outside `A` attains the bound. No finite-support assumption is needed for PMFs:
indicator expectations, `expect_mono`, and `alarm_zero_iff` suffice.

For one pair of actual laws with a strictly positive finite base-utility gain
and integrable base utility, a nonnegative finite automatically collected
penalty deters the deviation iff positive outside detection is possible. Choose
penalty at least `gain/detection` for sufficiency; zero detection proves
necessity. If soundness must cover every permitted source law, assume their
observable supports lie in `A` and quantify that requirement explicitly.

**Important boundary.** Pairwise existence does not give one finite deposit
for an infinite deviation family. A uniform sanction needs a uniform bound on
gain/detection, or an equivalent positive detection floor and gain ceiling.
There is no SE, reporting, collection-delivery or source compilation conclusion
from this detector theorem alone.

**Plan/cost.** Either correct prose to the actual checked surface, or prove the
two explicit theorems and add a hostile observation-alias example. Expected
growth ~40–90 lines including the precise integrability and soundness
hypotheses; high mathematical confidence. This would supply useful game-theory
insight and a clean obstruction boundary, rather than merely rearranging proofs.

## Additional concrete cleanup queue and boundaries

These are lower-impact engineering items, not extra ranked findings.

1. `Core/FictitiousPlayPotential.lean:273`,
   `mixedPotential_abs_le_of_abs_bound`, manually compares to positive/negative
   constants in ~23 lines. Existing `expect_abs_le_of_bounded` yields it after
   obtaining nonnegativity of the bound from a supported profile. Probe a
   ~3–5-line body; no new abstraction is required.
2. `Core/MixedPotential.lean:55,94,118`, the private/public
   `mixedPotential_update*` helpers ask each supported conditional for
   integrability AND equality to a total value. Whole updated-law integrability
   already gives every supported conditional guard through
   `payoffIntegrable_bind_conditional_on_support`. Only the value equality is
   an independent adapter hypothesis. Dropping that duplicated conjunct can
   simplify dependent caller witnesses without weakening a result.
3. `Math/Probability/ExpectationConditioning.lean:44,76` duplicates the filtered
   mass/scaling calculation in `payoffIntegrable_filter` and its stronger iff.
   Put the iff first, then derive the one-way result using
   `payoffIntegrable_indicator`. Keep positive conditioning explicit.
4. `Math/Probability/ExpectationBind.lean` has an inlined support-kernel extension
   in `expect_bindOnSupport_mono_on_support`, followed later by the same private
   `supportKernelExtend` abstraction for other dependent-bind lemmas. Reorder
   and use it once. `expect_bind_le_constant_on_support` is also a direct
   wrapper around `expect_bind_le_of_forall_on_support`; if consolidation removes
   redundant names, update callers rather than add another alias.
5. `Analysis/Protocol/StoppedTerminalBound.lean:199,230` repeats the same stopped
   invariant induction in `runBehavioralUntil_support_closed` and the stronger
   `..._of_going`. Reorder general first and specialize. The history-level
   invariant in `StoppedHistoryInvariant` is a further possible owner;
   preserve the distinction between state predicates and history predicates.
6. `Core/Arrow.lean:895,972` has near-dual 75-line dictatorship lemmas, plus
   mirrored top/bottom ranking helpers. Relation reversal can derive one from
   the other, but its ~30–50-line duality adapters must be charged. This is a
   promising local cleanup, not a reason to create a new social-choice hierarchy.
7. `Math/Probability/ConditionalComparison.lean`,
   `toOuterMeasure_eq_of_involution`, already needs only a law-preserving map
   and supportwise event exchange; it does not assume involutivity. Its name
   understates its actual generality. Prefer clean map-preservation terminology
   if editing this area; there is no theorem-correctness bug.
8. `Analysis/Protocol/ConsistentLikelihood.lean` defines
   `FactoredHistoryLikelihood` but has no declaration consumer found by `rg`.
   Its prose describes a type-exclusion consequence not proved in that module.
   `RestrictedComponentCompletion.lean` only defines
   `RestrictedExtensionApproximation`; its apparent occurrence in
   `Vegas/Game/CommitRecoveryOpeningMass.lean:116` is only a trailing variable
   declaration, with no theorem using it and no constructor in its owner.
   Neither structure is evidence that its mathematical obligations have been
   discharged. By contrast `NearProductWeights` has actual derived bounds
   and a concrete constructor in ProjectedBeliefTransport. Do not replace a
   difficult actual producer by a record whose fields demand its conclusion.
9. `Math/Probability/GatedExpectation`, `PresentConditional`, and
   `PMF.exists_residual_of_le` overlap in subprobability mass
   reasoning. A small common residual/optional-law owner could reduce imports,
   but avoid an unmeasured universal probability hub. No savings counted yet.

## Tests and proof-level correctness observations

The inspected hostile tests protect distinctions that should survive shrinking:

- `CorrelatedSequentialGap` separates correlated/normal-form preservation from
  sequential outcome preservation. Do not retire it because a generic law
  theorem covers its easy calculations.
- `CoalescingEquilibrium` distinguishes per-outcome implementation from one
  uniform strategically valid compiler; no existential swapping is justified.
- `MonitoredSignaling` and `PreservationContracts` keep observation aliasing,
  soundness for all permitted source behavior, and scope quantifiers visible.
- `ZeroSumOutcomeLaws` separates identical equilibrium values from identical
  realized payoff laws.
- Correlated-audit and quasilinear-bound tests preserve outcome/cash correlation,
  shared audit randomness, unfinished zero before deduction, and utility that
  can vary even when cash is fixed.

No proposed optimization should replace actual joint laws by separate marginals,
remove positive conditioning hypotheses, infer a fallback posterior identity at
zero mass, or replace guarded extended utility by unguarded totalized real
expectation. These are specific proof contracts visible in the reviewed APIs,
not hypothetical policy restrictions.

## Scratch proof probes and next checked steps

| File | Exact import | Checked claim | Status |
| --- | --- | --- | --- |
| `ProportionalBayesProbe.lean` | `GameTheoryExtensions.Analysis.Protocol.PublicScheduling` | Derive scale finiteness; complete local Bayes map theorem without finite expanded histories | PASS centrally, session 58992, exit 0 |
| `ExpectationContractionProbe.lean` | `GameTheory.Math.Probability.ExpectationAlgebra` | Absolute-expectation and difference L1 contraction with actual integration guards | PASS centrally, session 82481, exit 0 |
| `DiscretePushforwardProbe.lean` | `GameTheory.Math.Probability.Measure` | AE measurability and lintegral transport through a measurable projection with PMF pushforward | PASS centrally, session 60754, exit 0 |

All three files remain scratch artifacts. A successful scratch check establishes
the displayed mathematical statements against the current imports; it does not
establish the estimated savings, a completed consumer migration, or a merged
production API. The review performed no production Lean edits or builds.

Recommended first production measurements after probes: remove the redundant
scale-finiteness premise and instantiate one PublicScheduling consumer; rewrite
ProductDecorrelation completely with the L1 primitive; rewrite both
PolicyMeasure measurability blocks with the discrete-pushforward primitive.
Measure whole files including helpers and adapters, rerun exact theorem guards,
then decide whether the larger restriction-completion ownership change is worth
the package work. This ordering yields concrete mathematical improvements and
measurable compression without touching language design or fixed capstone scope.
