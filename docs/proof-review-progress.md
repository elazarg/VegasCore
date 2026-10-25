# Proof implementation ledger

This ledger records verified proof-library changes and explicit retention
decisions. Open proposals are in the [current review](proof-review.md). A checked
checkpoint includes the common API, all migrated callers, owning builds and
axiom guards, and measured net size.
A rejected approach is reverted before its reason is recorded. Mathematical
strengthening may justify modest API growth; it is not called compression.

GameTheory source and its submodule pointer remain unchanged. Findings owned
there are assessed for useful local extensions; copying a frozen implementation
solely to rename or shorten it is not an acceptable substitute. Source semantics,
SE targets and result strengths remain fixed.

Statuses distinguish queued/in-progress work, checked integration, rejected and
reverted approaches, and work constrained by the frozen dependency. A constraint
is not a claim that the mathematical result has been proved.

| Finding | Subject | Status | Evidence or next action |
| --- | --- | --- | --- |
| M1 | Proportional scale finiteness is derivable | Checked | Scale finiteness is derived from antichain mass and positive source mass; public-scheduler Bayes transport drops finite expanded histories. Both owners and regression pass, replayed Bayes probe passes, exact Bayes root retains standard axioms; zero net production lines |
| M2 | Finite-coordinate measure arguments repeat the same discrete pushforward step | Checked locally | Discrete-pushforward AE measurability/integration and uncountable-carrier regression pass, both exact roots use standard axioms. Four core PolicyMeasure consumers remain frozen; new local API, no compression claim |
| M3 | Add the missing guarded L1 contraction once | Checked | Guarded L1 calculus, all three probability families and both concrete affine callers pass the full build; exact three contraction roots use standard axioms. Whole family net14 fewer lines, not the estimated70–120 |
| M4 | Passage-based completion already subsumes the common-depth implementation | Checked locally | Enforced SE extension uses the existing passage theorem and drops depth/clock; owning module/test and exact standard-axiom audit pass. Local production−3 and test−13 lines; base duplicate implementations stay frozen in GameTheory |
| M5 | `UnitClose` and `WithinTV` describe the same distance | Checked | One total-variation predicate replaces UnitClose across all local consumers; partial-class transport and actual binding kernels improve 2δ to δ under the same hypotheses. Generic, iterator, all ten consumer files and two-unclassified-output regression pass; exact class root retains standard axioms. Combined M5/M11/A9 net128 fewer lines before umbrellas |
| M6 | Continuation domination charges inactive players unnecessarily | Checked | Per-player one-step factors and reference-supported uniform active-count bounds share one continuation induction. Chance/idle regression and concrete stopped-honest caller pass, three exact roots retain standard axioms; feature growth. Chance one-step law is exact; uniform multi-step exponent can remain conservative |
| M7 | Bounded stochastic Kuhn adapters reprove later general prefix-law adapters | Frozen dependency | Both bounded and general prefix-law owners and all specialization calls are inside GameTheory; no external caller found. Reordering them locally would require copying the frozen implementations, so no duplicate was added |
| M8 | Consistent completion can use countability and tightness already available | Checked | Subsequence and projection completion use countable sites and actual belief tightness; varying-strategy completion also requires strategy tightness. Existing compactness engine reused, finite existence corollary preserved; all three owners and exact roots pass |
| M9 | Pooled component best responses do not need finite outcome carriers | Checked | Pooled best responses require integrable actual component-profile laws instead of finite outcome carriers; finite-history caller supplies the guard. All three owning modules and exact pooled root pass; M8/M9 combined net zero production lines |
| M10 | Negligible counterpart bounds can use fiber multiplicity | Checked | Generic bounded-fiber estimate, sharper normalized c/(1+c), two-bad-to-one-good regression and all three concrete belief consumers pass. Both exact generic roots retain standard axioms; strengthening with API growth |
| M11 | Retained-policy expectation comparison belongs at the law level | Checked | Actual residual-law comparison removes finite ambient histories and attained payoff minima, preserving both integrability guards and full deviations. Generic, gated, retained and both actual game callers plus infinite geometric regression pass; comparison/Nash roots retain standard axioms. Shared accounting is recorded under M5 |
| M12 | Strategic bridges should consume coordinate equivalences and payoff laws | Frozen dependency | FOSG/MAID policy equivalences and their strategic consumers are inside GameTheory. Local source-protocol transport is generalized under S5; no parallel bridge implementation was added |
| M13 | Shapley proofs contain reusable finite-set mathematics | Frozen dependency | Shapley symmetry, efficiency and unanimity consumers are inside GameTheory. No VegasCore consumer justifies a duplicate Shapley implementation or an unused inversion framework |
| M14 | Discounted head/tail algebra should be proved below game models | Frozen dependency | Both discounted head/tail consumers and their scalar owner are inside GameTheory. Their analytic guards remain intact; no unused local copy was introduced |
| M15 | Enforcement prose describes an exact detector theorem that is absent | Checked | Arbitrary-carrier sound detection upper bound is attained; strictly profitable integrable comparison admits a finite sound sanction iff observable unlawful mass is positive. Both owners, hidden/visible regression and five exact axiom roots pass; pairwise result only, feature growth |
| R1 | Give accepted-event ownership one owner | Checked | Single owner retained; original opponent-frame proof unchanged; owning target and both standard-axiom audits pass; net46 fewer lines |
| R2 | Finish using the existing invariant hierarchy before inventing another | Checked | Provenance and input recall instantiate the existing ServiceInvariant; unused specialized predicates/transition proofs removed, both actual alias callers migrated. All owners/callers and five exact standard-axiom roots pass; net43 fewer lines |
| R3 | Factor the four-way environment lift, without discarding execution data | Checked | Exact existing environment-step support eliminator reused by15 proofs in10 callers; primitive and all callers pass, exact standard-axiom audit passes; net84 fewer lines including umbrella |
| R4 | Automatic draining already has the trace needed for almost every frame | Checked | Two trace-based induction owners replace18 repeated frame inductions across12 files; all owners/leaves pass and three exact roots use standard axioms; net79 fewer lines |
| R5 | Ordinary exclusion evidence is the zero-frontier instance of suffix evidence | Checked | One frontier-indexed ExclusionEvidence covers ordinary and suffix evidence; three duplicate owners removed and all callers migrated. Exact iff, accepted-unusable distinction and both unconditional native frame laws retained. Full build and exact environment/phase guards pass; net243 fewer lines across126 paths |
| R6 | Count-verdict persistence and collection are application-independent | Checked | Interaction owns ordered-input and continuation persistence facts; six concrete menu/collection proofs migrated. Recall equivalence needs only InputRecall; owning builds and two standard-axiom guards pass; net29 fewer production lines including umbrella |
| R7 | Candidate freshness should use one generic recorded-resource invariant | Checked | Actual-issued response-key membership is generic in the key and reuses existing provenance/invariant machinery; native/phase callers retain full catalogue guards. One phase emission theorem has one lower owner. All callers and exact generic guard pass; net37 fewer lines |
| R8 | Prove a useful elimination theorem for `PhaseRuntimeState.settle` | Checked | Lean generated functional induction supplies the exact settle eliminator, with no duplicate API. Ten proofs across five owners pass; four exact physical/invariant/archive roots retain standard axioms; net50 fewer lines |
| R9 | Share first-attempt-exit metadata, not the phase-specific snapshot conclusion | Checked | Generic entering/final-transition witnesses and actual stopped-prefix metadata replace receipt/origin inductions, retaining exact requests, traces and arbitrary legal policies. All callers and three exact runtime guards pass. Whole family grows34 lines including both generic kernels; no compression claim |
| R10 | Move typed handler success/inversion certificates below value swaps | Checked | Typed commitment/opening acceptance iff lives below swaps, with exact next states and actual failed-resolution results. Both public observation statements remain unchanged; all inversion callers and exact certificate guards pass; net218 fewer lines |
| R11 | Two typed partial-environment readers can share a dependency traversal | Checked | One typed collector replaces three reader families, with selected-lookup iff and no unique-name premise. All owners and type-sensitive missing/repeated-position regressions pass; net48 fewer lines. Exact iff uses propext/Quot.sound, availability uses standard three axioms |
| R12 | Behavioral realization has a nearby stronger player-memory joint law | Checked | Full execution/final-memory joint law and old marginal-as-projection pass, including continuation/test callers; both exact roots retain standard axioms. Net24-line growth; arbitrary opponents and schedulers retained |
| R13 | A common service contract needs physical episode identity; timeliness does not imply blindness | Assessed; retain existing contracts | Native, recovery and phased contracts quantify over different histories and physical episodes; recovery native transport requires public clearance, and retry restores readiness stamps at the current clock. A common record would merely repackage those obligations with additional adapters. No contract equivalence or restricted-blindness theorem is claimed; all-view erasure blindness remains a distinct hypothesis |
| R14 | Strengthen completion bounds by dependency height; reuse the existing progress service | Checked height bound | Actual dependency depth/height and one-layer-per-window theorem give height*(maxDeadline+1); old event-count theorem is a corollary. Both owners and empty/parallel/chain regressions pass; all four exact roots retain standard axioms. Net56 production lines added including graph umbrella; no rollback rank refactor claimed |
| R15 | Generalize hidden-value symmetries only after exposing handler frames | Assessed; retain existing symmetry operators | All examined owner/splice consumers use pair swaps; simultaneous per-field transpositions already fit SwapPairs. Arbitrary composition is not involutive, and sequential guards must be transported. No concrete non-involutive consumer justifies a new permutation hierarchy. Typed handler frames are pursued under R10; no general hidden-permutation result is claimed |
| G1 | Prove owned-completion provenance once, with all the facts consumers need | Checked | Exact native classifier and single-message source certificate own five completion-proof families; all seven owners/consumers pass, five exact classifier/consumer roots retain standard axioms. Net371 fewer lines before umbrellas |
| G2 | Add the missing initialized decoded-invariant induction | Checked | Initialized decoded invariant owns the induction; all three original caller conclusions retained. Owner and three consumers pass, exact generic root retains standard axioms; net21 fewer lines |
| G3 | Expose one residual-head operational correspondence, then derive masses | Checked atom kernel | One residual syntax proof also gives exact fixed-action ENNReal atoms with the same successor witness; chance/owned readers migrated. All four modules and exact native/residual roots pass; net120 fewer lines before umbrella. Full behavioral head-law refactoring is not claimed |
| G4 | Factor phase-boundary advancement out of honest/deviation/withhold induction | Checked | One lower owner derives actual seeded event/block boundary and horizon facts; five event triples and four block readers migrated in three complete law proofs. All owners/callers pass; net66 fewer lines including the new owner |
| G5 | Make mapped reactive-round congruence an Interaction API | Checked | Generic round-law kernel congruence and all three concrete consumers pass; exact generic root retains standard axioms. Whole family grows8 lines, retained for three actual consumers |
| G6 | Lift the hidden-seed path-likelihood identity out of reserved-tape replay | Checked | Immutable-seed command/step/whole-trace density lives in Interaction, using the actual initial prior and same recorded trace. Generic and concrete Likelihood owners plus original concurrent capstones pass; exact generic root retains standard axioms. Net31-line growth including the explicit posterior adapter |
| G7 | Extract conditioning-cost bounds with explicit excluded mass | Checked | Filtering costs excluded probability times supportwise payoff oscillation, without finite carriers or independence. Generic and concrete clean-binding history-sum adapter plus capstones pass; permanent exact guard passes. Net30-line growth |
| G8 | Publish retained/residual gain algebra, without global finite carriers | Checked | Integrable retained-gain algebra and actual clean-binding consumer pass on arbitrary carriers; both exact generic roots retain standard axioms. Net51-line API growth |
| G9 | Remove the exact duplicated support-order expectation theorem | Checked | Generic support-order theorem, slack corollary and both concrete gain callers pass; exact axioms pass. Exact dedup shrinks8 lines, slack API makes family grow6 |
| G10 | Share domination operations rather than model-specific map/mix lemmas | Checked | Map/common-mixture/right-retention owner and both actual domination callers pass; exact map/mix roots retain standard axioms. Net9-line API growth |
| G11 | Give approximate local comparisons monotonicity and finite-case algebra | Checked | Gain comparison monotonicity and common-sequence finite error budget plus both comparison callers pass; exact error-budget/lottery roots retain standard axioms. Net42-line API growth; source assessment sequence preserved |
| G12 | Repair the dependent provenance interface before attacking giant bodies | Checked | Dependent reference/config transport requires no ResultTypes premise; five actual provenance adapters replace local equality eliminations. Full correspondence/alignment/replay and capstone chain plus both exact transport guards pass; whole family net57 fewer lines |
| G13 | Generalize owner-prior transport to public-fiber independence, cautiously | Checked conditional base laws | Canonical source splice, prior scaling and two-site/late base-law proofs accept independence within an observed public initial fiber. All-history membership and same-key support closure are proved; unconditional callers use Unit with unchanged capstone hypotheses. Full-support noisy public-bit regression and exact roots pass. Production grows256 lines after removing duplicated engines; conditional-prior recovery SE remains unproved |
| G14 | Obtain event-sensitive Nash errors before changing runtime contracts | Checked per-player result; event refinement assessed | Two per-player best-response bridges retain complete audited payoff ranges, full deviations and expectation guards. Every scalar caller and all11 scalar theorem headers remain intact; exact roots and full build pass. Four files grow3 lines; Paper adapter grows1. Event-weighted continuation sensitivities need additional actual hybrid-payoff guards and are not claimed |
| G15 | Turn strict enforcement margins into a local support-exclusion theorem | Checked | Effective-menu silence is a feasible zero-charge continuation against arbitrary admitted opponents. Strict coverage/deposit margin excludes a forbidden choice at every own-clean information fiber under rationality, with actual runner factorization and integrability. Generic/concrete owners, timing example and exact guards pass. Whole family grows423 lines; original example CountRecall conjunct retained |
| S1 | Factor the legal action translation inside the two repair inductions | Checked | Constructive legal-joint coordinate update and both actual reveal-translation callers pass. The broad menu-level helper was rejected because its signature erased savings. Minimal kernel and all adapters grow one line; exact generic root needs no axioms |
| S2 | One typed compiler metadata theorem can own two structural inductions | Checked | Typed output/revealed-cell metadata belongs to Compile; one label-parametric structural proof owns typed and name projections. Both compiler owners and both Game readers pass; three exact roots use standard axioms; net54 fewer lines |
| S3 | Share observation-codec traversal, retaining visibility and absence | Checked | Exact typed collector correspondence shares visible congruence, agreement and missing-publication proofs. Decoder definition and five public headers stay unchanged. All compiler/game consumers pass and exact permanent congruence guard retains standard axioms; net77 fewer lines |
| S4 | Bundle the residual embedding already used by the compiler | Checked | Derived ordering for actual residual tail references owns nine repeated proofs across three compiler/game readers. All owners/callers pass; exact generic root retains standard axioms. Net31 fewer lines |
| S5 | The private-parameter source-protocol payoff law is within immediate reach | Checked | General terminal-observation reader owns payoff-law, expectation guards and same-error Nash equivalence; private-parameter specialization has no independence/finite-parameter premise. Both owners and executable runtime example pass; two exact Nash roots retain standard axioms. Feature growth, not compression |
| S6 | Purification needs finite explored action support, not finite payload types | Checked | Finite-support kernels replace finite binding alphabets; owner, integer-report regression and original runtime caller all pass. Both exact purification roots retain standard axioms; one pure-policy mixture is drawn before setup/chance. Infinite-support kernels remain outside this finite-mixture construction |
| S7 | Classify departure from the intended game before duplicating induction | Checked | One departure classifier additionally records an admitted forfeiture site; debt-only and arbitrary-admission results are corollaries. Owners and actual preservation/deviation callers pass; all three exact roots retain standard axioms. Net31 fewer lines |
| S8 | Erased-history continuation needs one step law and legality transport | Checked | Removed two unused private proofs and their unused import; continuation and support-splice owners pass, both public erasure results retain standard axioms; net47 fewer lines |
| S9 | Make the auction's executable transfers a separate concrete application | Checked | New bounded-report auction evaluates integer second-price transfers in ret; all-outcome settlement/utility equality, full-deviation compiled Nash iff and conditional-withholding counterexample for every integer charge pass. Four exact roots retain standard axioms; original unbounded real-forfeiture result unchanged. Feature growth |
| S10 | Reuse positive service fixtures without erasing adversarial timing | Existing implementation retained | Positive payment fixture already uses the proved roster-to-async constructor. The late-opening fixture has distinct adversarial timing evidence, so replacing it would change its purpose; no redundant fixture framework was added |

## Additional cleanup queue

| Item | Subject | Status | Evidence or next action |
| --- | --- | --- | --- |
| A1 | Fictitious-play best-response factoring | Frozen dependency | Owner and consumers are inside GameTheory; preserve its implementation |
| A2 | Mixed-potential conditional guard redundancy | Frozen dependency | The dependent certificate and its consumers are inside GameTheory; no local replacement |
| A3 | Conditioning integrability iff owns the one-way proof | Frozen dependency | Both declarations are inside GameTheory; no duplicate local conditioning API |
| A4 | Supported-bind kernel extension | Frozen dependency | Existing lower owner and all redundant proof bodies are inside GameTheory |
| A5 | Stopped support invariance | Checked | One general unstopped-history invariant proof owns all seven migrated callers; all pass the full build and exact root retains standard axioms. Net31 fewer lines |
| A6 | Arrow relation-reversal factoring | Frozen dependency | Social-choice proofs and duality adapters are inside GameTheory; no local consumers |
| A7 | Law-preserving conditional-comparison terminology | Frozen dependency | Rename would change GameTheory; no external caller found |
| A8 | Likelihood and restricted-completion certificate obligations | Checked | Removed two unused certificate modules and a trailing variable with no theorem consumer; corrected false existence prose. Projected-belief, actual approximate factorization, opening owner and umbrella pass; exact factorization/type-exclusion and restricted-completion existence are not claimed proved |
| A9 | Optional/residual law overlap | Checked | One small optional-domination owner owns the residual producer and two real comparison families; all pass. PresentConditional remains separate because normalization and residual completion are different operations. Shared M5/M11 accounting is not counted twice |

A frozen-dependency disposition records an ownership constraint, not a proved
strengthening or an implemented cleanup. The relevant core declaration surfaces
and external callers were searched; creating unused local copies would not
address the duplicated implementations. These remain available for a separately
authorized GameTheory change.

The proposed shared erased-step API was unnecessary: the duplicate in the
continuation owner had no consumer. That API change was reverted, and the unused
step and terminal-until proofs were deleted. The support-splice implementation
and its observation-local legality argument remain in their existing owner.

The integrated probability, evidence, round-congruence, stopping and purification
checkpoint passes the full ordinary build (5750 jobs), including all original
capstones and Paper guards. Exact new roots use only `propext`, `Classical.choice`
and `Quot.sound`. Lean still reports a recursion-depth diagnostic while exporting
optional premise-suggestion metadata for the existing timing-audit example; its
checked theorem build succeeds. This diagnostic is tracked separately from proof
acceptance. Remaining queued and partial findings remain open.

The service-contract and hidden-permutation proposals are deliberately limited
after inspecting their actual consumers. Readiness is a physical episode: raw
native histories, public-clear recovery projections and retry-aware attempt
coordinates have different domains. Merely giving all three records the same
field names does not prove their equivalence. Late-packet blindness also covers
counterfactual erased views; timing guarantees alone do not supply that law.
The existing contracts therefore remain separate, with their current scopes.

Hidden-swap composition has a separate algebraic obstruction: two overlapping
transpositions on three values compose to a non-involutive cycle. Disjoint
per-field swaps are already represented by one pair family. The existing
guarded StateSymmetry interface can represent non-involutive maps, but a useful
composition result would need the second guard in the first transformed state
and an actual caller. No such caller was found in the inspected owner/splice
proofs, so no unused permutation hierarchy was added. These assessments do not
claim new equivalence, privacy or asynchronous SE theorems.

The probability/typed-reader/trace-density checkpoint passes the full ordinary
build (5761 jobs), all original capstones, eleven added permanent axiom guards,
all seven review probes and 94 Python tests. The ten migrated library families
remove 295 physical lines after including their common APIs and every concrete
caller; the three public library aggregators add eight lines, for a net library
reduction of 287. New independent regression files add 219 lines, test aggregators
six, and permanent axiom guards/imports 67. Documentation is counted separately.
The separate dependency-height feature and its regression are excluded from
these totals. The optional premise-suggestion diagnostic noted above persists;
kernel proof acceptance and every exact axiom guard pass.

The evidence, continuation and conditional-prior batch passes the full ordinary
build (5767 jobs), all original capstones, 24 added permanent axiom guards,
all seven review probes and all 94 Python tests. Module boundaries, strict
source policy and documentation references pass. GameTheory source and its
submodule pointer are unchanged.

The four evidence/handler/resource/context refactor families remove 555 physical
lines after including their common APIs and all actual adapters. The stopped
trace family adds 34 lines; the conditional-prior theory adds 256 after removing
duplicated engines; strict audit support exclusion adds 423; and the per-player
Nash family adds three plus one Paper adapter line. These are different scopes,
so their figures are not combined with test and aggregator counts. Across the
whole batch the library grows 182 lines, examples/regressions 159, and Paper
147 (144 guard lines, two imports and the one adapter line). Mathematical
feature growth is not reported as proof compression.

Every item in this implementation ledger has a disposition. A frozen dependency
or retained contract is not an implemented strengthening. Event-sensitive timing
errors need actual hybrid-continuation payoff guards; the conditional-prior
source-splice adapter is checked only as an isolated review probe. Full recovery
SE propagation remains unproved; neither capstone extension is claimed.
The existing optional premise-suggestion diagnostic persists independently of
successful kernel builds and axiom checks.
