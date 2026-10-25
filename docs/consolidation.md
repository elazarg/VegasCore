# Consolidation ledger

This ledger tracks the reduction of VegasCore to one source language, one
compiled contract on one chain model, and the theorems about them. It holds the
target, the codebase review measured at commit `8c67dad2`, the step order, the
owner decisions the steps depend on, and the index of retired results.

Rules:

1. Steps follow the dependencies below. A step closes when its exit criteria
   hold on a green `lake build` with the repository checks passing.
2. A finding closes with the commit that resolves it; tick its box in that
   commit.
3. Anything removed that carries a checked result worth citing gets an annotated
   tag first and a row in [retired results](#retired-results).
4. Step and finding labels stay in this file. They never appear in Lean names or
   docstrings (see AGENTS.md).

## Target

**Source language.** Straight-line commit–reveal programs: private inputs,
public chance, guarded commitments and reveals, and payoffs computed by the
program. Branches and loops are out of scope; the design should not preclude
them. One operational semantics must specify failure, exit, continuation and
commitment-phase retries, including what players observe and remember. The
intended game is a derived analysis view in which commitments succeed and
reveals open, not another independently maintained source semantics. The exact
failure semantics remains decision D3.

**Payoffs and utility.** The program's payoffs are what the compiler sees.
Players' utilities are quasi-linear: `u_i(theta, z) = v_i(theta_i, z) + t_i(z)`,
where the program computes the monetary transfer $t_i$ and the analysis supplies
the private valuation $v_i$. Deposits, forfeits and exit payments are monetary
transfers; the valuation bounds they need are declared parameters, not
properties the compiler reads from the program. A constant exit payment gives
a constant exit utility only under an explicit valuation hypothesis, for
example that an excluded bidder receives nothing and values that outcome at
zero. Unknown private valuations and
externalities cannot in general be cancelled by a compiler-chosen payment.

**Truthfulness.** The designer can specify truthfulness, for example that
truthful bidding is dominant in a second-price auction. Preserving it through
compilation requires additional conditions. Conditional withholding already
refutes dominance in the current commit–reveal auction, for every forfeiture
amount; see [truthfulness](#truthfulness-and-failure) and decision D4.

**Compiled output.** One compiled contract with one verdict and audit model on
the `Interaction` chain model. The environment (builder, observation, audit
coverage) is a parameter, and the strength of the preserved notion depends on
it.

**One result family.** The same source semantics, contract, audit and observation
types underlie compiler correctness, Nash correspondence and SE preservation.
Their hypotheses and conclusion directions remain explicit. In particular,
forward SE preservation does not imply reflection of every target equilibrium,
and it does not replace the existing ε-Nash correspondence or deferral bounds.
Preserve the joint law of original inputs, outcomes and realized monetary
transfers, with no charges or exits on the lifted intended-equilibrium paths.
The existing capstones' utility-valued settlements need adapters to this
monetary observation; the target is not yet their checked statement.

The two SE environments remain distinct sufficient conditions within this
family. A reserved tape with correlated inputs and complete observation is not
interchangeable with an adaptive timely builder whose private inputs are
independent given an observed public initial signal. Neither
current SE theorem implies the other. Extending concurrent SE to arbitrary
timely builders is a separate research question, not an exit criterion for
consolidation.

**Theorem ladder and current evidence.** The checked statements below retain
their present source games and utilities until the semantic adapters are proved.

| Result | Environment | Graph | Present state |
| --- | --- | --- | --- |
| Compiler correctness: terminal law, unilateral deviation law, Nash equivalence on the ideal graph | none | any mode | checked: `canonical_setup_law`, `canonical_setup_deviation_law`, `Vegas.Paper.concurrent_event_nash_iff` |
| Nash preservation | any timely builder | sequential and concurrent | checked on the plain contract (`Vegas.Paper.async_first_turn_nash_iff` and siblings); to port |
| Non-concurrent sequential-equilibrium preservation | any timely builder, private inputs independent given a public initial signal | sequential | checked on the phase contract (`Vegas.Paper.sequential_phase_intended_raw_sequential_equilibrium`), preserving the original joint typed readout and settled utility law |
| Concurrent sequential-equilibrium preservation | reserved-epoch tape, complete pending observation | concurrent | checked on the phase contract (`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`) |
| Intended game to source game | none | none | checked: `Vegas.Paper.intended_sequential_equilibrium`, `Vegas.Paper.intended_nash` |
| Late-leak impossibility | abstract game | none | checked: `Vegas.Paper.late_leak_intended_outcome_not_preserved` and siblings |

**Size.** The owner's estimate is 50–80k lines of Lean outside the GameTheory
submodule. [Measurements](#measurements) give the current floor and explain any
excess.

## Mathematical feasibility

**Assessment, not a checked theorem.** Consolidation appears feasible using
established finite extensive-game methods. It requires substantial semantic
design and adapter proofs; no new equilibrium concept is needed. This does not
establish that the missing adapters hold or that a stronger environment theorem
is true.

| Work | Mathematical status | Required evidence |
| --- | --- | --- |
| Program payments plus private valuations | Standard quasi-linear utility model | Payment evaluation is used by the games and compiler; valuation and exit hypotheses are explicit |
| One source semantics with exit and retries | Semantic design, with nontrivial correspondence proofs | Account for missed commitments, permanent exit, surviving players' retries and retained observations |
| Nash on the phase contract | Existing deviation-simulation methods; port unproved | Compare old and new source deviations, payoffs, environment quantifiers, ε and deferral bounds |
| Sequential SE on the phase contract | Checked with singleton phases under the original conditional-independence and physical service assumptions | Actual phase completion, pure-deviation comparisons and audited joint-law preservation; common monetary-language integration remains separate |
| Existing concurrent SE in the common family | Checked theorem under its current hypotheses; integration unproved | Instantiate the common payoff and readout interfaces without weakening the result |
| Concurrent SE for arbitrary adaptive timely builders | Research question | A new sufficient-condition theorem or a counterexample for the specified contract and quantifiers |
| Unrestricted dominant truthfulness for the current auction | Refuted at source level | Existing conditional-withholding witness; positive claims need different conditions or mechanics |
| 50–80k lines | Unmeasured compression goal | Compress one proof module and measure before extrapolating |

### Reusable mathematics and proof APIs

Nash preservation uses a simulation of unilateral target deviations against
compiled honest opponents. Sequential equilibrium additionally needs rational
continuation at every information set, including implementation-only histories,
and beliefs obtained from a common sequence of fully mixed profiles. Equal
terminal laws alone do not establish this. The relevant existing APIs include
[local comparison limits](../GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean),
[proportional belief transport](../GameTheoryExtensions/Analysis/Protocol/ProportionalBeliefTransport.lean)
and [terminal-audit extension](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean).
Instantiate these and identify the missing operational hypotheses before adding
another general preservation framework.

The [proof-review implementation ledger](proof-review-progress.md) records the
preparatory extractions separately from the semantic consolidation steps.
Probability comparison, typed collection, continuation and evidence proofs have
reusable owners. Conditional-public-prior base laws and player-specific audited
Nash errors strengthen the analysis without choosing failure or retry semantics.
Strict count-audit support exclusion uses terminal-supported payoff bounds,
observed own-output cleanliness and a feasible safe continuation. Source-cell
and native-view adapters carry conditional public priors through the full
recovery SE capstone, including its joint settled/readout law; a Unit signal
recovers the unconditional scope. Product retention sharpens the timing error
through the Nash and actual-payment capstones. These results leave the semantic
adapters and common-contract language decisions open. The
[proof review](proof-review.md) records all sixteen checked findings.

The [phase application](../Vegas/Pending/PhaseApplication.lean) already accepts a
general event graph; the concurrent capstone fixes `.concurrent`. The
[sequential phase proof](sequential-phase-preservation.md) instantiates singleton
phases with the sequential compiled graph. Clear histories have checked physical,
information and belief transport; actual phase completion optimizes the richer
continuations after public exclusion. This proves intended SE preservation on
the existing phase contract while retaining attempt metadata, readiness,
deadlines, network traffic and recall. The source-language, failure and monetary
interfaces still require their separate consolidation decisions and adapters.

Preservation from the intended restriction and preservation from every
equilibrium of the full failure semantics are separate claims. The existing SE
capstones start from the intended game. Defining operational exit does not by
itself strengthen their premise to every source equilibrium.

### Truthfulness and failure

In [the commit–reveal auction](../Vegas/Examples/CommitRevealAuction.lean),
`Vegas.Examples.CommitRevealAuction.truthful_not_dominant` proves that truthful
binding and disclosure is not dominant, for every withholding forfeiture. Alice
values the item at 5; Bob commits to 4 and reveals precisely when Alice reports
5. Reporting 5 gives Alice utility 1, while reporting 6 gives her utility 5
against the same opponent policy. Dominance quantifies over that policy even
when withholding is costly for Bob.

`Vegas.Examples.CommitRevealAuction.translated_truthful_not_dominant` carries
the obstruction to translations preserving the relevant profile utilities.
This does not refute truthful auctions with other disclosure or settlement
rules. A positive preservation result must state the permitted opponent
strategies and information channels, and prove the required comparison over
them. Nash or SE preservation against equilibrium opponents is insufficient to
deduce dominance against arbitrary opponents.

### Primary research

- [Halpern, Pass and Seeman, *Computational Extensive-Form Games*](https://arxiv.org/abs/1506.03030)
  relates abstract games to cryptographic implementations and proves Nash and
  computational SE preservation under representation assumptions. It supports
  separating strategic analysis from cryptographic realization; its hypotheses
  are not automatically satisfied by the Vegas scheduler and failure semantics.
- [Geffner and Halpern, *Communication games, sequential equilibrium, and mediators*](https://arxiv.org/abs/2309.14618)
  constructs equilibrium-preserving communication protocols, with consistent
  off-path beliefs as a central obligation. Its mediator model and resilience
  assumptions differ from this contract's enforcement assumptions.
- [Geffner and Halpern, *Security in Asynchronous Interactive Systems*](https://arxiv.org/abs/1906.02069)
  studies bidirectional simulation with scheduler influence. It motivates
  checking scheduling quantifiers rather than treating scheduling as an
  unobservable execution detail.
- [Ferreira and Weinberg, *Credible, Truthful, and Two-Round (Optimal) Auctions via Cryptographic Commitments*](https://arxiv.org/abs/2004.01598)
  gives positive auction constructions under stated distributional and
  cryptographic assumptions. Such mechanism-specific guarantees do not imply
  unrestricted truthfulness preservation by this compiler.
- [Reny, *A simple proof of the sufficiency of Dilmé’s power-sequence test for Kreps-Wilson consistency*](https://doi.org/10.1007/s00182-026-00997-z)
  derives a simple certifying-sequence characterization through Farkas' lemma.
  It is a candidate for simplifying finite-game consistency proofs. Applying it
  still requires actual runtime likelihood and information-set correspondence;
  no proof-size reduction is established here.

## Measurements

Measured at `8c67dad2` with a declaration-level dependency walk: from the root
theorems, follow the constants each declaration uses through the project
libraries, then merge the source ranges of the reached declarations per module.
File headers, `variable` lines and notations are not counted, so whole files
run 10–20% larger. `#print axioms` pins do not count as uses.

| Root theorems | Lines in cone | Beyond the concurrent SE cone |
| --- | ---: | ---: |
| Concurrent SE | 210k | |
| Turn-based SE (forced-exit contract) | 109k | 90k |
| Calendar SE | 74k | 60k |
| Calendar Nash | 60k | 47k |
| Asynchronous Nash | 49k | 36k |
| Ideal-graph Nash (compiler correctness) | 9k | 4k |
| One-packet SE | 8k | 3k |
| Late leak | 8k | 8k |
| Intended to source, exclusion | 5k | 1k |
| Public scheduling | 2.5k | 2k |
| All 26 Paper theorems | 317k | |
| Whole tree (files, without GameTheory) | 871k | |
| Whole tree after Step 3 pass one | 597k | |
| In modules no Paper theorem, test or example reaches, after Step 0 (438 modules) | 80k | |
| Whole tree after Step 3 pass two | 494k | |
| Whole tree after unreached declarations | 445k | |
| Whole tree after Step 3 | 442k | |

The concurrent SE cone by layer: Vegas/Game 136k, Vegas/Pending 32k,
Vegas/Source 24k (17k of it the `CommitRecovery*` and `ProposalRecovery*`
carriers), Interaction 7k, GameTheoryExtensions 4k, Vegas/EventGraph 3k,
Vegas/Compile 3k. Within Vegas/Game: `QualifiedBinding` about 53k,
`PhaseProposal*` 42k, `ProposalRecovery*` 13k, `ReservedEpoch*` 11k.

**Why the floor exceeds 50–80k.** The language, compiler, chain model and phase
contract fit in about 55k lines, and the source language with its compiler and
Nash equivalence on the ideal graph in 9k. The excess is the proof of concurrent
SE preservation: about 150k lines (Vegas/Game plus the source-side carriers).
Removing unreached code reaches about 250k for concurrent SE and both Nash
forms, or about 340k with turn-based SE kept on its own contract. Reaching
50–80k would need the concurrent proof to shrink by a factor of four or more,
which nothing measured so far supports. The slack indicators are real (F-S4,
F-S2; 12.5% of six-line windows recur in another file), but their yield is
unmeasured. Step 3a measures a model-independent extraction pilot; Step 6 uses
that evidence and a proof-compression pilot before any size target is fixed.
Extrapolating a factor of 1.5–2.5 on
the proof layer gives an end state of roughly 100–170k lines; this is an
estimate, not a measurement.

## Model inventory

Each construction gets one disposition: keep, merge, carrier (a labelled proof
device in the proof layer), tag and remove, or remove.

**Source-level games.**

| Construction | Role | Proposed disposition |
| --- | --- | --- |
| `SourceProgram.gameForm`, `Setup.gameForm` | Source semantics as a game form | keep one; `Vegas.SourceProgram.Setup.protocol_runBehavioral_eq` relates it to the protocol |
| `Setup.executionProtocol`, `Setup.informationModel` | Source semantics as an information model, parameterized by a commitment interface | keep |
| `Setup.intendedModel` | Analysis view: commitments hold predicted values, reveals open; premise of every SE theorem | keep |
| `Setup.exclusionModel`, `Setup.exclusionMoveModel` | Analysis view with a fixed exit payoff | decision D3 |
| `commitRecoveryModel`, `commitRecoveryErasedModel`, `proposalRecoveryModel` | Proof carriers of the concurrent SE theorem (26k of the 47k lines in Vegas/Source) | carrier: move to the proof layer and label |
| `Setup.valueBindingGame` | Pure value-binding game form, used only by the commit–reveal auction example; its behavioral edge ([`Vegas/Game/ValueBindingEdge.lean`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/ValueBindingEdge.lean)) is unused | remove the edge; keep the game form only with the example |
| `SourceProgram.Initial` | Duplicate of `Setup` with a point-mass initial state | removed; tests use a `Setup` with a point-mass law, and `Vegas.SourceProgram.Setup.revealed` states the accounting theorem |
| `Vegas/Language` | Surface-syntax prototype with no semantics or elaboration | tag and remove |

**Compiled contracts.** All three run on the same `Interaction` chain model.

| Contract | Packets and verdict | Results on it | Proposed disposition |
| --- | --- | --- | --- |
| Plain (`serviceApplication`) | `WitnessedPacket`, settled-record verdict | Nash (all forms), calendar SE, one-packet SE | remove after the Nash port |
| Forced exit (`recoveryApplication`) | `WitnessedPacket`, count verdict | turn-based SE | remove after the turn-based SE port |
| Phase (`phaseApplication`) | `CommitAttemptPacket`, phase count verdict | concurrent SE | keep: the contract |

**Audit models.** The settled-record authentic sampler (calendar) and the count
evidence report service (forced exit and phase). Keep the count service.

**Environments.** Calendar rosters, `AsyncContract`, `Recovery.AsyncContract`
and the reserved-epoch tape. Keep one timely-builder contract (for Nash and
turn-based SE) and the reserved-epoch tape (for concurrent SE).

## Steps

Order: guardrails, documentation and independent pruning come first (Steps 0–3
and the documentation parts of Step 7). Step 3a extracts model-independent
mathematics from the checked models before their contracts change, and starts
the payment integration with a concrete program. It can proceed while the
remaining semantic choices in Step 2 are being settled. Step 4 implements those
choices and proves the correspondence adapters before Step 5 ports the
preservation family and removes the duplicate contracts. Step 6 compresses the
surviving proof layer. The tag `research-tree` makes removals recoverable; build
and theorem comparisons still establish that kept results survive.

### Step 0. Record

- [x] Commit this ledger.
- [x] Annotated tag `research-tree` on `main` holding the full research tree,
      so every later removal is recoverable by tag.
- [x] Pin `recovery_intended_raw_sequentialEquilibrium_preserved` in Paper, as
      `Vegas.Paper.recovery_intended_raw_sequential_equilibrium`; the paper cites
      it as `thm:recovery`.

### Step 1. Guardrails that make removal cheap

- [x] Remove `warn.sorry = false`, the open-obligation registry,
      `scripts/report-open-obligations.py` and its CI step. With
      `warningAsError` a `sorry` then fails the build. A `sorry` is allowed only
      temporarily during a large planned proof effort, and none is planned.
- [x] Remove the hand-written pins in `VegasTests/AxiomAudit`. The axiom audit
      is the pins in Paper.lean; the build rejects `sorry`, and the source
      policy rejects `axiom` declarations.
- [x] Reduce `scripts/check-lean-options.py` to the central options, the ban on
      `sorry` and `axiom`, the Paper pin format with its expected axiom list,
      and a ban on escape hatches: declaration-adding metaprograms, skipped
      kernel checks, native evaluation, and options set per library or through
      command-line definitions.
- [x] Add the dependency walk as a script: list modules with no declaration
      used by Paper, a test or an example, counting names that test and
      example source mentions. Report only until Step 6
      (`scripts/report-unreached.py`).

Exit: green build with sorry warnings as errors; the walk script is committed.
This step comes first because every removal would otherwise edit audit pins.

### Step 2. Fix the contract

- [ ] Owner decisions D1–D8, including a written failure, retry, information and
      payment specification before the theorem ports. Recommendations below do
      not settle the remaining choices.
- [ ] Paper.lean states exactly the kept theorems, under the naming scheme of
      D8.
- [x] One results table in README keyed to the Paper pins, with scope and
      hypotheses; ARTIFACT.md folded into it.
- [ ] Stale or contradictory status statements fixed or deleted (findings
      F-D1 to F-D4).

Exit: README, Paper and the docs agree; the documentation checks pass.

### Step 3. Prune to the kept cone

Two passes. The first removes every module outside the import closure of the
kept roots: the modules holding declarations used by the kept Paper theorems
and by `recovery_intended_raw_sequentialEquilibrium_preserved`, plus the kept
tests and instance examples. No kept module imports a removed one, so this pass
cannot break the build. At `0a2dbc66` it removes 1,508 modules (295k lines) and
keeps 2,306 (594k). The second pass shrinks the closure: unused imports, then
unreached declarations inside kept modules, rebuilding as it goes.

Removed results are indexed under [retired results](#retired-results).

Pass one, done:

- [x] `archive/`.
- [x] The calendar theorems in Paper and the calendar checklist with its
      evidence script.
- [x] `CommitSeedBroadcast*`, `CommitSeedSignalling*`, `CommittedResolution*`
      and `LateOpeningRuntime*` examples, except the two instance files
      `LateOpeningRuntimeNash` and `LateOpeningRuntimeSourcePreservation` and
      the modules they need.
- [x] `PhaseTiming*` and most of `PhaseRecovery*`.
- [x] `Vegas/Language`, the Communication chain, `CommitmentEvidence`,
      `EventGraphEvidence`, `PayoffTransport`, `ValueBindingEdge`.
- [x] `VegasTests/AxiomAudit`, `VegasTests/Language`, and the
      GameTheoryExtensions modules that only their own tests used.

Pass two:

- [x] The 438 modules (80k lines) none of whose declarations Paper, a test or
      an example reaches, as `scripts/report-unreached.py` lists them, and the
      407 declarations in 143 kept modules (23k lines) that use them. Each import
      of a removed module became the surviving modules it imported, and module
      docstrings that described removed results were rewritten.
- [x] Unreached declarations inside kept modules: 1,812 declarations (48k
      lines) in 572 modules, and the 5 modules that left empty. A declaration
      stays when surviving source outside comments mentions its name (rfl
      lemmas used by `simp`, `show` types, `variable` binders), when it is an
      instance or an rfl `@[simp]` lemma, or when it lies in
      `ExclusionMoveGame` (decision D3) or in the language and compiler layers.
- [x] Unreached declarations in `Vegas/Foundation`, `Vegas/Expr`,
      `Vegas/EventGraph` and `Vegas/Compile`, reviewed by hand. Removed 91
      (1.6k lines): helpers of removed proofs (commit-prefix filling, encoding
      inverses, configuration restriction, output coupling), and the
      nullable-commitment, substitution and default-value helpers of the simple
      expression language with its unused `CommitPayloadTy` and `DefaultVal`
      classes. Kept as specification, though nothing uses them yet: dependency
      soundness of the expression interface (`Vegas.IExpr.expr_deps_sound`),
      the guard characterizations, compiler correctness for expressions, payoffs
      and payouts (`Vegas.canonical_payout_law`) and under public scheduling
      (`Vegas.scheduled_setup_law`), the event graph's information-flow lemmas,
      the guarantees on resolution fields and published guards, and the
      relation between the sequential and concurrent execution modes
      (`Vegas.EventGraph.canonical_fromSequential_store_law`), which a
      derivation of the sequential results from the concurrent ones would start
      from.
- [x] Unused imports: 1,524 project imports removed and 423 added where a
      module had reached a dependency only through a removed one (net 1,101 of
      7,059), and the last unreached module. A library module imports the
      modules owning the constants its declarations use, the rfl `@[simp]`
      lemmas whose left sides they use, and the names its `open`, `variable`
      and notation lines and `simp` lemma lists mention.
- [ ] The calendar's remaining `ServiceRoster` and `SourceService*` modules,
      `MessagePool` and most of `OnePacket*` stay because the turn-based SE and
      asynchronous Nash theorems use them on the plain and forced-exit
      contracts; they wait for Step 5.

Exit: the walk reports only modules on its allowlist; measurements updated.

### Step 3a. Extract model-independent mathematics and connect payments

The purpose is to separate mathematical obligations from facts about a
particular source language, contract or scheduler before consolidating those
models. Merely moving a file or replacing concrete types with a record of the
same obligations does not achieve that separation. Existing abstract results
already cover local comparison limits, proportional belief transport, pooled
affine-score ranking and terminal-audit extension; extend or instantiate their
owning APIs before introducing replacements.

Keep source and contract semantics, scheduler quantifiers, payoff functions and
public capstone statements fixed during each mathematical extraction. Payment
integration is an explicit semantic change with its own checkpoint, rather than
an unnoticed change inside a refactor. No extraction closes an SE checklist box
or proves a new environment guarantee.

Independent checkpoints may be developed in parallel in the shared checkout,
with disjoint file ownership and coordinated builds. Commit and push each
stable, verified checkpoint; dependent adapters follow their owning API.

- [x] Map the mathematical dependencies of the retained capstones using `rg`,
      `lean-defs.py` and the module map. For each extraction, identify the
      existing owning API, the concrete facts its callers must prove and the
      repeated proof argument it will replace. Record affected callers, proof
      size and verification scope before editing.
- [x] Pilot the extraction on conditional-law normalization and disintegration
      in [the qualified-binding posterior proof](../Vegas/Game/QualifiedBinding/ForeignPosterior.lean).
      Some local helpers already quantify over arbitrary probability spaces
      and observation maps. Reuse existing conditioning APIs where sufficient;
      otherwise extract the missing probability theorem and replace the local
      proof. Keep positivity and zero-probability conditioning explicit. Measure
      the general proof plus all remaining adapters, not just lines moved out
      of Vegas.
- [x] Establish the generic separation of monetary settlement from valuation,
      including audit charges and the joint realized transfer law. Then wire a
      concrete source program's nonzero `ret` payments into its strategic
      utility and compiled readout, using the existing
      `Vegas.canonical_payout_law`. Prove a strict incentive comparison that
      depends on those evaluated payments. Changing the program payment must
      change the actual game payoff; an unused evaluator or a caller-supplied
      replacement utility does not satisfy this checkpoint. Step 4 still owns
      the full capstone migration and exit-valuation hypotheses.
- [x] Factor the common conditional-collection and audited extension arguments
      from [the plain](../Vegas/Game/OnePacketExtension.lean),
      [forced-exit](../Vegas/Game/RecoveryOnePacketExtension.lean) and
      [phase](../Vegas/Game/PhaseOnePacketExtension.lean) proofs through
      [terminal-audit extension](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean).
      Keep packet validity, authentic evidence, response-menu membership and
      report delivery as separately proved backend facts. Reuse the result in
      the existing contracts before any contract is removed.
- [x] Extract continuation indifference and payoff-floor comparisons, with
      [observable failure](../Vegas/Game/PhaseProposalObservableDebtPayoff.lean)
      and [current-binding gain](../Vegas/Game/PhaseProposalCurrentBindingGain.lean)
      as candidate callers. The mathematical theorem should use continuation
      payoff conditions, not bindings or phase identifiers. Constant utility
      under every continuation gives zero deviation gain; the concrete model
      must still prove that condition. Reuse the existing gated-expectation,
      affine-decorrelation and pooled-ranking APIs for nonconstant cases.
- [x] Extract any remaining common argument from factored history likelihoods
      to conditional comparisons and a consistent SE limit. Keep reconstruction
      of actual histories, readiness, rollback, callback occurrences and
      scheduler likelihoods in the model adapters. Preserve a common tremble
      witness and the order in which rates, pooled policies and equilibria are
      chosen. Compose through the existing local-comparison limit theorem;
      do not assume its desired gain bound as the entire new abstraction.

Use `GameTheoryExtensions.Math.Probability` for probability results and
`GameTheoryExtensions.Analysis.Protocol` for results about arbitrary execution
protocols and information models. Generic message-network facts belong in
`Interaction`; language and contract adapters stay in their owning Vegas
layers. Moving results into the separately managed GameTheory submodule is not
required for this phase. A model-independent theorem has no Vegas dependency;
it must prove a mathematical consequence from conditions that make sense in
other models.

Each checkpoint replaces its old proof callers, removes superseded local
helpers and passes the relevant builds, capstone standard-axiom checks and
repository checks. Demonstrate reuse across existing models where available;
otherwise include a small independent application that exercises the extracted
hypotheses. Review both the abstract theorem and its concrete adapters so that
the difficulty is not merely shifted into a large assumption. Record total
proof size and the remaining model-specific obligations. Reduced line count is
useful evidence, not a reason to weaken a statement.

**Extraction inventory and evidence.**

| Mathematical API | Checked consumers | Conditions still proved by the model |
| --- | --- | --- |
| [Restricted disintegration](../GameTheoryExtensions/Math/Probability/RestrictedDisintegration.lean): `GameTheory.Math.Probability.observation_mass_of_scaled_restriction`, `GameTheory.Math.Probability.fiberPosteriors_of_factored_restriction` and `GameTheory.Math.Probability.fiberPosteriors_of_independent_restriction` | `Vegas.PhaseProposalQualifiedBinding.foreign_posterior_cut_pair_atoms`, `Vegas.PhaseProposalQualifiedBinding.foreign_posterior_cut_pair`; independent-bit and absent-observation applications in [the tests](../GameTheoryExtensionsTests/RestrictedDisintegration.lean) | The actual joint word law, conditional kernels, independence and positive observations |
| [Clean settlement transport](../GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean): `GameTheory.Enforcement.TerminalAudit.settlement_transport_of_normalized_law` | The plain and forced-exit raw one-packet SE extensions; quasi-linear clean settlement | Projected state law, invariant base payoff and audit observation, and zero collection on the reference support |
| [Continuation indifference](../GameTheoryExtensions/Analysis/Protocol/SourceGainTransport.lean): `GameTheory.Protocol.InformationModel.historyGain_eq_zero_of_constant_payoff`, `GameTheory.Protocol.InformationModel.gain_eq_zero_of_constant_continuations` | The phase contract's saved-failure history and information-site comparisons; an independent [responder with a sunk fee](../GameTheoryExtensionsTests/ContinuationIndifference.lean) | The focal payoff is fixed under every continuation from each history in the information fiber |
| [Perturbation calibration](../GameTheoryExtensions/Math/Probability/PerturbationScale.lean): `GameTheory.Math.Probability.exists_positive_rate_with_ratio_bound` | `Vegas.exists_phaseProposal_common_perturbations`, for both source and native posterior denominators | Actual positive response floors, multiplicities and the choice of rates before pooled policies |
| [Quasi-linear settlement](../GameTheoryExtensions/Analysis/QuasilinearSettlement.lean) and [program payment utility](../Vegas/Game/ProgramPayoffs.lean) | `Vegas.Examples.ProgramPayments.payment_reverses_incentive`, `Vegas.Examples.ProgramPayments.audited_expectedUtility`, `Vegas.Examples.ProgramPayments.compiled_transfer_law` | Program evaluation determines transfers; valuation is separate analysis data |

The count-audit collection proofs in all three contracts use the existing
supported-bind expectation bound. The payoff-floor comparisons and outer SE
limit argument retain the existing gated-expectation, affine-decorrelation,
pooled-ranking and local-comparison APIs. No additional certificate hierarchy
is needed for those arguments. Reconstruction of actual histories, callback
occurrences, readiness, rollback, traffic observations and scheduler
likelihoods remains in the concrete adapters.

The extracted theorems make three conditions explicit. A scaled restriction
identifies its observation mass even when that mass is zero; identifying the
posterior requires positive mass, while finiteness follows from normalization.
For continuation indifference, the fixed payoff may differ between hidden
histories. This does not relax the existing exit-payoff hypotheses for choices
made before failure. The perturbation calibration needs a positive denominator,
without an upper bound on it; the model still supplies that denominator before
the rate is chosen.

The payment instance evaluates a nonzero conditional bonus in `ret`. Publishing
true has valuation minus one. A bonus of two makes publishing true a Nash
equilibrium; a bonus of zero makes publishing false a Nash equilibrium. The
opposite selected profile is not an equilibrium in each case. These results
quantify over every legal randomized whole-policy deviation, including failed
bindings and withheld publication. The corresponding compiled profiles have
the same equilibrium and non-equilibrium properties under every public scheduler,
with utility reading the actual compiled payment instructions.

Whole-file measurements against extraction baseline `019d848a` include the new
general modules and all changed concrete adapters, including imports and
docstrings. Independent test modules are excluded. These are not the
declaration-cone measurements in [measurements](#measurements).

| Surface | Baseline lines | General API plus adapters | Difference |
| --- | ---: | ---: | ---: |
| Qualified-binding posterior | 3,408 | 3,436 | +28 |
| Three audit extensions plus terminal-audit API | 1,381 | 1,355 | −26 |
| Source gain API plus saved-failure comparisons | 262 | 288 | +26 |
| Common perturbations plus rate calibration | 277 | 283 | +6 |
| These mathematical extractions together | 5,328 | 5,362 | +34 |

The independent posterior and continuation applications contain 58 and 62 test
lines. Monetary settlement, program utility, joint payment laws, source-protocol
correspondence, ideal and runtime equilibrium bridges, and concrete incentive
examples provide the payment interface. Independent examples exercise correlated
audits, unfinished outcomes and valuation-sensitive exit utility. Paper guards
the axioms of the payment results. These APIs isolate
reusable mathematics and connect payments to equilibrium results; they do not
establish a substantial overall size reduction or a compression factor for the
remaining preservation cone.

Acceptance: the full default `lake build` passes, including all
Paper axiom pins. The 89 repository Python tests, source-policy, module-boundary
and documentation-reference checks pass. The dependency walk reports zero
unreached modules. Existing public statements in the changed Vegas proof modules,
the retained Paper statements, the concurrent preservation specification and the
central Lean options are unchanged. Paper includes additional payment axiom
guards. Focused audits of the
extracted results and their concrete consumers use only `propext`,
`Classical.choice` and `Quot.sound`.

Exit: the selected extractions have checked consumers and the concrete payment
checkpoint is checked; the retained capstones keep their exact statements and
standard axioms. The resulting API and adapter inventory identifies which
later consolidation changes affect mathematical hypotheses. Extracting most of
the proof is an objective to measure, not an assumed result.

### Step 4. Language and semantic correspondence

The following payment results use the existing semantics and are available
without choosing a new failure, exit or retry policy. They supply parts of the
interfaces below; the checklist remains open until those interfaces cover the
common language and retained capstones.

- [Joint cash and utility laws](../GameTheoryExtensions/Analysis/QuasilinearSettlement.lean)
  convert `(outcome, receipt vector)` to `(outcome, utility vector)` by adding
  valuation, and recover receipts by subtraction. Both maps are inverse on
  entire probability laws. The audit identities preserve correlated verdicts
  and require neither independence nor integrability. Retaining the outcome
  is necessary because it determines the valuation being subtracted.
- [Program payment observations](../Vegas/Game/ProgramPaymentLaws.lean) retain
  the actual initial draw, full typed terminal state, public result and actual
  compiled receipt vector jointly. Every public scheduler preserves this law
  for a compiled source profile. This statement permits arbitrary initial
  distributions, including correlated private data; it concerns completed
  source and ideal-graph runs.
- [Payment-based Nash correspondence](../Vegas/Game/ProgramPaymentNash.lean)
  preserves and reflects the same ε under every public scheduler, against all
  legal unilateral graph deviations. Its monetary term is the sum of the
  actual compiled payment instructions. Valuation may depend on an immutable
  initial parameter jointly with the public result. This parameter is an
  analysis readout of the existing source execution; strategies and their
  observations are unchanged. The theorem requires finite commitment alphabets
  and finite support of the initial distribution, without requiring a finite
  parameter type or independent private inputs.
- [Audited runtime payments](../Vegas/Game/ProgramPaymentAsyncNash.lean)
  separate the program's transfer from valuation on the existing typed runtime
  readout. Their expected quasi-linear utility is computed from the actual
  randomized monetary settlement after deposit charges. For every builder
  satisfying the existing asynchronous contract and timeliness assumptions,
  first-opportunity clients preserve and reflect the same ε-Nash property in
  the source protocol and bounded raw response game. Clients that defer have
  the additional error `2 * δ * R` in both directions, where δ is
  `1 - product(event, 1 - deferral(event))` and R is the audited utility range.
  This error is at most the sum of event deferrals without an extra
  independence assumption. The assumptions
  retain barrier ordering, authentic audit samples, nonnegative deposits and a bounded
  interval covering every terminal utility, unfinished readout and possible
  charge. For every admitted source profile, a separate theorem preserves the
  exact joint typed terminal state and cash-settlement vector without assuming
  equilibrium. Both pre-audit transfer and valuation are zero on an unfinished
  readout, following the existing convention. This is an analysis settlement,
  rather than an implementation of escrow.
- [Declared monetary bounds](../GameTheoryExtensions/Analysis/QuasilinearBounds.lean)
  derive the runtime payoff interval from separate valuation, transfer and
  deposit bounds. If completed values lie in `[Vlo,Vhi]`, receipts in
  `[Tlo,Thi]`, and collectible deposits in `[0,D]`, every audited payoff lies in
  `[min 0 (Vlo + Tlo) - D, max 0 (Vhi + Thi)]`. The zero terms are essential:
  an unfinished readout contributes zero before a possible charge, even if
  every completed utility is positive. This interval may be conservative when
  valuation and receipts are correlated; callers may supply tighter bounds.
- [Source-protocol Nash correspondence](../Vegas/Game/SourceProtocolNash.lean)
  uses the existing observation-local policy equivalence and preserves the
  entire utility-vector law, including expectation-existence conditions and
  infinite expected utilities. Restricting commitment admission preserves a
  full-source equilibrium whose policies are admitted. When admission permits
  every source policy, Nash preservation and reflection have the same ε.
- [The concrete payment runtime](../Vegas/Examples/ProgramPaymentsRuntime.lean)
  instantiates the proved roster scheduler, a bounded raw response menu,
  authentic full-evidence audit and deposit of one. Every service assumption is
  checked for that fixture. Bonus two makes publishing true Nash, bonus zero
  makes publishing false Nash, and each opposite selected profile is not Nash.
  The proofs retain failed bindings, withholding and all allowed raw deviations.
  The exact complete typed terminal-state and cash law holds for either choice
  and every integer bonus.
- [SE valuation adapters](../Vegas/Game/SequentialPaymentValuation.lean)
  separate ordinary and excluded valuation from cash in both existing runtime
  bases. A fixed exit receipt yields fixed exit utility exactly when valuation
  is also fixed there. Agreement with program payments on failed source
  publications additionally requires the program's own transfer to equal the
  declared exit receipt. These are explicit hypotheses, not properties of an
  arbitrary valuation or a compiler-selected compensation.
- [Concurrent monetary SE preservation](../Vegas/Game/ConcurrentPaymentPreservation.lean)
  instantiates the original concurrent theorem with program-computed ordinary
  transfers, separate valuation bounds and declared constant exit valuation and
  cash. It retains the reserved tape, complete pending observation, operational
  and funding assumptions, quantifier order, source equilibrium, and original
  preservation conclusion. Its additional cash law retains all original input,
  typed-state and public-result coordinates. The original no-exclusion and
  no-charge conclusions justify recovery of actual audit cash on its support.
  The utility used for equilibrium is proved to be the expectation of valuation
  plus that monetary settlement on every runtime state.

The nonconcurrent recovery theorem preserves an optional typed readout and
utility-valued settlement, with zero audit charges and no runtime exclusions on
its equilibrium paths. The no-exclusion conclusion follows from an explicit
runtime exclusion-flag probability bound and convergence of the actual common
completion, independently of payoff equality or audit cleanliness.
[The recovery cash adapter](../Vegas/Game/RecoveryPaymentReadout.lean) recovers the
joint monetary law when runtime valuation is determined by the retained source
readout. For the constructed preserving equilibrium, the additional condition on
supported excluded states is vacuous. The general adapter retains that condition
for arbitrary runtime laws, which may include exclusions and whose exit
valuation may differ from the retained readout. The source valuation includes the
existing failed-publication exclusion rule and is zero on an absent readout;
ordinary valuation agrees with it only under the separate failure hypothesis.
Exit receipts remain declared analysis settlement data until a compiler/runtime
implementation proves them.

These results keep the existing contracts distinct and leave the source failure,
exit and rollback choices open. They provide conditional monetary adapters for
the retained SE scopes without claiming a common operational contract.

- [ ] Implement the source failure semantics chosen under D3, specifying missed
      commitments, participation after failure, remaining players' continuation
      and any phase retries with retained observations. Derive the intended
      analysis view from it; distinguish intended-equilibrium extension from
      preservation of every full-source equilibrium.
- [ ] Program payments are load-bearing: utility is valuation plus monetary
      transfer. State valuation bounds, the hypothesis making exit utility
      constant, and the treatment of unfinished executions. Re-establish
      publication accounting, guard safety and source–graph correspondence.
      Extend Step 3a's payment-dependent program instance to the capstone family.
- [ ] Prove the sequential phase-contract adapter against the forced-exit
      contract. Investigate singleton commitment phases first; compare
      observations, deviations, retries, deadlines, payments and continuations.
      An adapter that changes the old game is not an equivalence.
- [ ] Define the common joint observation of original inputs, outcomes and
      realized monetary transfers, and prove its relation to the existing
      capstones' utility-valued settlements.
- [ ] A truthfulness specification (D4), with the conditional-withholding
      obstruction and explicit hypotheses for any positive preservation claim.

Exit: the chosen operational semantics and payment interfaces are checked, and
the adapters needed for the ports have checked proofs. No stronger SE premise
or environment is inferred from the existence of these interfaces.

### Step 5. One contract and one result family

Before a theorem moves to the phase contract, a written comparison of the old
and new statements shows that the move does not weaken it: source game,
environment and quantifier order, observations, deviations, payoffs, ε,
deferral bound and the preserved joint law. Changes in source failure semantics
need an explicit correspondence theorem. Paper states one clear Nash
correspondence and the two SE guarantees over the common interfaces.

If a required correspondence fails, retain the affected result and report the
obstruction before changing its scope or retiring its contract.

- [ ] Nash preservation on the phase contract under timely builders
      (first-turn clients and the deferral bound).
- [ ] Non-concurrent SE on the phase contract over the sequential graph, using
      the checked adapter and retaining the timely-builder, observation and
      independent-input scope of the existing result.
- [ ] Concurrent SE instantiated through the common semantics, payments and
      readout interfaces, retaining correlated inputs, the reserved tape and
      complete pending observation. Generalizing its environment is separate
      research, not a prerequisite for this step.
- [ ] Every Paper theorem applied to a concrete program in which some player has
      a strict incentive; impossibility statements include existence of the
      equilibria they quantify over.
- [ ] Remove the plain and forced-exit contracts, `WitnessedPacket` and the
      settled-record audit only after the theorem comparisons and instances
      pass.

Exit: every preservation theorem uses `phaseApplication` and the common monetary
and valuation interfaces; both existing SE scopes and Nash correspondence are
retained; every Paper theorem has an instance.

### Step 6. Proof compression and naming

- [ ] Compress one self-contained proof module and measure the reduction
      before choosing a size target or replacing proof machinery. Evaluate
      power-sequence consistency only where it simplifies an actual obligation.
- [ ] Recurring hypothesis groups bundled into structures; repeated terms
      named with API lemmas; declarations over 500 lines split.
- [ ] Duplicate private helpers and near-copy files merged.
- [ ] Directories by layer and concept; namespaces only `Vegas` and
      type-attached ones; the naming scheme of D8 applied throughout.
- [ ] Examples in their own library; abstract examples outside `Vegas`.
- [ ] The walk script gates CI.

Exit: size within the target, or the excess explained in
[measurements](#measurements).

### Step 7. Documentation and CI

- [ ] README (purpose, results, build), design notes, research notes behind one
      index; the module map generated or replaced by per-directory headers.
- [x] CI: separate documentation job on `main` only, concurrency group,
      GameTheory build cache, actions pinned by commit (F-I1; F-I2's root
      cache remains).

## Owner decisions

- **D1. Kept theorem set.** Decided: the ladder in [target](#target), without
  the calendar results. A calendar is a fixed instruction plan
  (`rosterScheduler` reads `rosterPlan` by round), so every player knows the
  schedule in advance; its sequential-equilibrium and Nash theorems are
  retired. Non-concurrent SE stays the turn-based theorem under any timely
  builder. Deriving it from the concurrent theorem waits: the environments
  differ, so the derivation is not expected to be routine.
- **D2. The single contract.** Proposed: the phase contract.
- **D3. Source failure semantics.** Commit–reveal with exit
  (semantics-and-enforcement.md III.1), or the intended game with forfeit and
  exclusion payoff rewrites as analysis views only. Recommended: operational
  exit and explicit phase-retry semantics, with an intended restriction derived
  from the same semantics. Specify retained information, survivors' payments
  and the valuation hypothesis behind constant exit utility before porting
  results. This also decides the fate of `exclusionModel`; the choice remains
  open.
- **D4. Truthfulness.** Decided meaning: truthfulness preservation, for example
  that truthful bidding stays dominant when a second-price auction is compiled.
  The language must be able to state it. Conditional withholding already
  refutes unrestricted dominance for the current auction settlement, including
  translations preserving its profile utilities. Positive preservation under
  additional conditions or different mechanics remains open.
- **D5. Impossibility results kept on `main`.** Proposed: the late-leak family
  (abstract, about 8k lines, motivates the exit payoff), moved out of the
  `Vegas` namespace. The runtime obstructions (`LateOpeningRuntime*`,
  `CommitSeedSignalling*`) at tags.
- **D6. Tags or branches.** Proposed: annotated tags for retired results;
  branches only for a result to be maintained against the evolving core.
- **D7. `public_scheduling_sequential_equilibrium`.** Keep (about 2k lines
  beyond the concurrent cone) or tag.
- **D8. Naming scheme.** Settle before Step 2 renames anything, so every name
  changes once. Proposed: "contract" for compiled output, never "runtime";
  theorem names of the form premise game, target, notion (for the concurrent
  theorem: concurrent, intended, raw, sequential equilibrium).

## Findings

Severity: H high, M medium, L low. "Step" is the step that resolves the finding.

### Claims and evidence

- [ ] **F-C1 (H, Step 2).** `concurrent_source_raw_sequential_equilibrium`
  assumes an SE of the intended game (`SourceEquilibrium`,
  `Vegas/Game/ConcurrentRawSequentialPreservation.lean:102`), not of the
  source game; its name and README say "source".
- [x] **F-C2 (M, Step 2).** README omits scope conditions of the concurrent
  theorem: a non-strategic first-in-first-out service that clears every pending
  packet at each processing cycle, complete pending observation, a constant exit
  payoff, and payoff zero for a run unfinished at the horizon.
- [ ] **F-C3 (H, Step 5).** Ten of the 23 Paper theorems are never applied to
  a concrete program: exclusion SE, public-scheduling SE, the one-packet SE,
  turn-based SE, and six of the asynchronous Nash forms (only `Vegas.Paper.async_first_turn_nash_iff`
  has an instance). The retired calendar theorems had none either. The
  late-opening examples now also apply exclusion SE
  (`Vegas.Examples.LateOpeningRuntimeSource.intended_equilibrium_extends_to_exclusion`)
  and the two deferring-client Nash forms; seven remain.
- [ ] **F-C4 (H, Step 5).** The only instance of the concurrent hypotheses
  (`VegasTests/ConcurrentRawHypotheses.lean`) has no strategic content: Bob's
  payoff is identically zero and every profile gives Alice one half
  (`honest_alice_value`). The capstone is never applied to it.
- [x] **F-C5 (M, Step 5).** `settle_late_not_preserved_for_every_margin`
  quantifies over the SEs of a game with no proof that it has one; the
  `late_leak_*` and `CommitSeedSignalling` obstructions omit existence from
  their statements although it is proved nearby. Every late-leak and
  settle-late Paper theorem now states that the late game has a sequential
  equilibrium (`Vegas.lateLeak_exists_sequentialEquilibrium`, and
  `Vegas.settleLate_exists_sequentialEquilibrium` through
  `Vegas.settleLate_decisionRecall`); the `CommitSeedSignalling` obstructions
  are at the tag.
- [ ] **F-C6 (L, Step 5).** The concurrent joint law reads the initial inputs
  from the terminal store rather than from the native initial draw.
- [x] **F-C7 (L, Step 2).** `one_packet_raw_sequential_equilibrium` uses
  `IsSequentialEquilibriumFor` with a truncated context instead of
  `IsSequentialEquilibrium`. It and `recovery_intended_raw_sequential_equilibrium`
  now state `IsSequentialEquilibrium`, through the raw protocol's horizon bound.

### Trust base

Verified faithful: Kreps–Wilson consistency (`IsSequentiallyConsistent`),
sequential rationality at every information set against whole-policy
deviations, Nash and ε-Nash, beliefs as distributions over information sets,
perfect recall proved for every model, horizons equal to proved bounds.

- [ ] **F-T1 (L, Step 4).** Unfinished runtime executions pay a literal zero
  (`serviceBaseUtility`, `phaseExclusionBase`); make it a named parameter or
  prove every terminal history reads out.
- [ ] **F-T2 (L, upstream).** Library information fibers may contain terminal
  histories (`BehavioralAssessment.lean:62-69`); inert in Vegas, where every
  model proves its sites nonterminal.

### Proof policy

- [x] **F-P1 (H, Step 1).** `warn.sorry = false` with an empty obligation
  registry: a `sorry` produced by a macro passes the build and the text check
  (core `stop` expands to `repeat sorry`). Only declarations under an axiom pin
  are protected.
- [x] **F-P2 (M, Step 1).** The pin check accepts `#guard_msgs (drop all)`,
  ignores the expected axiom text, and misses theorems with attributes or
  modifiers.
- [x] **F-P3 (M, Step 1).** The option check reads only the top-level option
  table; options set per library or through command-line definitions pass.
- [ ] **F-P4 (M, Step 6).** `backward.isDefEq.respectTransparency = false` is
  global; nothing records which proofs need it. Prefer `@[implicit_reducible]`
  on the carriers.

### Language and models

- [ ] **F-L1 (H, Step 4).** The existing capstones and Paper accept utility
  parameters without deriving transfers from `ret`; the two unbounded auction
  examples write `.ret []` and keep real-valued valuations in the analysis. The
  [program payment interface](../Vegas/Game/ProgramPayoffs.lean) and
  [strict-incentive instance](../Vegas/Examples/ProgramPayments.lean) connect
  evaluated payments to a source game and compiled transfer law. The
  [bounded auction](../Vegas/Examples/BoundedPaymentAuction.lean) computes its
  integer second-price receipts in `ret`, proves agreement with economic utility
  and full-deviation compiled Nash correspondence, and retains the conditional
  withholding counterexample. Common capstone integration remains open.
- [ ] **F-L2 (H, Steps 3–5).** About eight source-level games and three
  compiled contracts; see [model inventory](#model-inventory).
- [x] **F-L3 (M, Step 2).** The language's limits (straight-line, fixed actors,
  every move a commit and a reveal, guards cannot read their author's private
  inputs) are not stated in README or source-semantics.md.
- [ ] **F-L4 (L, Step 4).** A guard failure lands on whichever reveal completes
  the guard (`Vegas/Source/Semantics.lean:355-363`): a value may violate its own
  guard and publish as a success while a later reveal fails.
- [x] **F-L5 (M, Step 3).** `check-module-boundaries.py` checks only imports into
  `Vegas.*`; it cannot see Source importing the Interaction runtime or analysis
  layers. Foundation, Expr, Source, EventGraph and Compile may now import neither
  `Interaction` nor the analysis libraries, except that the commit- and
  proposal-recovery carriers in Source may use analysis until they move to the
  proof layer.

### Size, duplication and proof engineering

- [x] **F-S1 (H, Step 3).** 2,165 of 3,777 modules (about 428k lines) contain no
  declaration used by Paper or by a test declaration; 35% of declarations are
  reached from Paper. After Step 3 the report lists no module.
- [ ] **F-S2 (H, Step 5).** Parallel runtime stacks: 269k lines mention
  `WitnessedPacket`, 244k `CommitAttemptPacket`, 46 files both. Three copies of
  the one-packet raw extension theorem (`OnePacketExtension.lean`,
  `RecoveryOnePacketExtension.lean`, `PhaseOnePacketExtension.lean`; 81% and
  67% line overlap).
- [x] **F-S3 (M, Step 3).** 67 `CommitSeedBroadcast*` files are near copies of
  `CommitSeedSignalling*` files.
- [ ] **F-S4 (H, Step 6).** Eight declarations exceed 1,000 lines
  (`source_admitted_binding_row` about 1,957); statements with up to 83 explicit
  binders; one term spelled out 183 times in one file; the initial-law equation
  re-proved inline 39 times; 601 copies of one `local notation`.
- [ ] **F-S5 (M, Step 6).** 13 grouping namespaces with no type of that name
  hold 2,523 declarations (for example `Vegas.PhaseProposalQualifiedBinding`).
- [ ] **F-S6 (M, Step 6).** Flat directories: 1,496 files in Vegas/Game and 887
  in Vegas/Pending; the aggregators are unordered import lists.
- [ ] **F-S7 (M, Step 6).** The 136k lines of examples ship inside the `Vegas`
  library; the late-leak examples use no Vegas code.

### Tests

- [x] **F-X1 (M, Step 1).** 17.3k of the 21.2k VegasTests lines are 2,961
  hand-written axiom pins covering about 16% of theorems.
- [ ] **F-X2 (M, Step 5).** No small concrete tests for the pending runtime, the
  reserved-epoch scheduler, the count audit or belief transport; no `#eval` or
  `#guard` checks.

### Documentation and repository

- [x] **F-D1 (H, Step 2).** Docs describe the concurrent theorem as unproved or
  admitted: se-reserved-service-preservation.md:4-11,
  se-concurrent-code-inventory.md:39-43, se-concurrent-replay-analysis.md:5-6,
  module-architecture.md:17-19 and 2929-2937.
- [x] **F-D2 (H, Step 2).** ARTIFACT.md omits the concurrent theorem and 12
  other Paper pins; se-async-checklist.md:68 names the fixed-calendar theorem as
  the headline; two docs claim Paper pins that Paper no longer has
  (se-async-checklist.md:409, standard-runtime-se-status.md:71).
- [x] **F-D3 (M, Step 2).** LICENSE is MIT; every Lean header says "All rights
  reserved", two say Apache 2.0. Every header now names the MIT license.
- [ ] **F-D4 (M, Step 7).** module-architecture.md is 2,937 lines under one
  heading; 53 of 81 Markdown files are unreachable from README; six overview
  documents overlap. The module map is now grouped by layer, and
  [docs/README.md](README.md) reaches every Markdown file; the overlap remains.
- [x] **F-D5 (M, Step 3).** `archive/` keeps 1,105 tracked files; live docs link
  into it.
- [x] **F-D6 (L, Step 7).** scripts/README.md says investigation scripts are in
  the archive; 14 are tracked in scripts/experiments.
- [ ] **F-D7 (L, Step 7).** About 22 documentation sites encode history.
- [x] **F-D8 (L, Step 2).** AGENTS.md says to commit and push every checkpoint;
  an agent's note said to push only on request. The owner keeps the AGENTS.md
  rule.

### CI

- [x] **F-I1 (M, Step 7).** The documentation job takes 89–138 minutes against
  a build of about 10, deploys Pages from any branch, and holds Pages
  permissions for the whole job; there is no concurrency group. The API
  documentation is now its own job, run after the build and only on pushes to
  `main`, and only it holds Pages permissions. Each ref has a concurrency group:
  off `main` a newer push cancels the running check, while on `main` it waits.
  The job still takes about 95 minutes, but no build result waits on it.
- [ ] **F-I2 (L, Step 7).** `GameTheory/.lake` is not cached, so each run
  rebuilds the submodule; each run saves a 4.8 GB cache. `GameTheory/.lake` is
  now cached by the submodule revision (32 MB). The root `.lake` cache that
  `lean-action` saves under each commit is still 3.8 GB per run on `main`.
- [x] **F-I3 (L, Step 1).** The checkers' comment and string strippers miss
  character literals, raw strings and guillemet names; the documentation check
  passes vacuously outside the repository root. Both checks now share one
  lexer that handles them, and the documentation check fails without a
  `lakefile.toml` in the working directory.

## Why the concurrent theorem assumes what it does

These counterexamples explain assumptions of
`Vegas.Paper.concurrent_source_raw_sequential_equilibrium`. The late-leak family
stays on `main`; the others are checked at the `research-tree` tag. The
arguments are in [semantics-and-enforcement.md](semantics-and-enforcement.md),
Sections I.5 and I.7.

These obstructions concern the games and contracts named in each row. In
particular, an obstruction for continued play after failure on the plain
contract does not refute concurrent preservation on the phase contract under
arbitrary timely builders. The reserved-tape environment is a checked sufficient
condition; its necessity for the phase contract is not established here.

| Assumption | Counterexample | Shows |
| --- | --- | --- |
| A failing player's payoff is a constant exit payoff, at most every terminal utility | `Vegas.Paper.late_leak_intended_outcome_not_preserved`, `Vegas.Paper.late_leak_outcome_preserved_by_failure_costs` | With continued play after failure, a forfeit charge, and late openings included with probability close to one, no sequential equilibrium of the late game keeps the intended outcome law; failure costs that make the failure branch worth the same to every type restore it. |
| The service is the reserved-epoch tape, which processes every pending packet at each cycle, not an arbitrary timely builder; collateral is fixed before the service | [`exists_service_with_no_preserving_equilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimeUniformSeObstruction.lean#L28), with variants under [all-or-none traffic sampling](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimeAllOrNoneSeObstruction.lean#L77) and [partial sender auditing](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/LateOpeningRuntimePartialAudit.lean#L190) | For a positive reward and any sufficiently large forfeit and deposits fixed first, one exogenous, commonly known finite builder meeting the timely-service requirements, with an arbitrarily small positive late-opening failure, has native sequential equilibria, and none realizes the source joint law. |
| The exit loss lies below every payoff a participant could receive | [`exists_honest_sequentialEquilibrium_without_native_preservation`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedSignallingNonpreservation.lean#L59); [the note](se-private-seed-signalling.md) | When packet timing reveals a hidden coin, a player controls which useful observations another receives. With the exit loss below the reward range, every native sequential equilibrium gives Alice at least one quarter, while every honest source profile gives her zero. |

The three-owner fixture behind
[se-strong-exclusion-signalling.md](se-strong-exclusion-signalling.md), which
tests an exit loss above the reward range, is at the tag with its native
obstruction unfinished.

## Retired results

Each row names the declaration or files at the `research-tree` tag, what they
show, and the models they need. They are checked at the tagged commit only.

| Result at the tag | Shows | Needs |
| --- | --- | --- |
| [`Vegas.Paper.source_audited_raw_sequential_equilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L43), [`Vegas.SourceServiceSpec.intended_audited_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/IntendedServiceCompilation.lean#L42) | SE preservation, from the source and from the intended game, on a fixed calendar that every player knows in advance | Plain contract, settled-record audit, calendar roster |
| [`Vegas.Paper.source_audited_raw_nash_iff`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L292), [`Vegas.Paper.source_audited_raw_nash_reflection`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L258), [`Vegas.Paper.intended_audited_raw_nash`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L428), [`Vegas.Paper.raw_service_horizon`](https://github.com/elazarg/VegasCore/blob/research-tree/Paper.lean#L114) | Nash correspondence and horizon on the same calendar | As above |
| The late-opening and seed-signalling counterexamples | See the previous section | Plain contract, specific services |
| [`CommitSeedBroadcast*`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommitSeedBroadcast.lean) | Three-owner timing fixture; obstruction unfinished | Plain contract |
| [`certain_late_inclusion_with_joint_contract`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Examples/CommittedResolutionErasure.lean#L69) and the other `CommittedResolution*` examples | The service and erasure contracts do not force a positive late-failure floor | Plain contract |
| `PhaseTiming*`, most of `PhaseRecovery*` | An unfinished timing route for SE on the phase contract | Phase contract |
| [`Vegas/Language`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Language.lean) | Surface-syntax prototype, without semantics or elaboration | None |
| [`VegasTests/AxiomAudit`](https://github.com/elazarg/VegasCore/blob/research-tree/VegasTests/AxiomAudit.lean) | 2,961 hand-written axiom pins | None |
| [`archive/se-generalization`](https://github.com/elazarg/VegasCore/blob/research-tree/archive/se-generalization/README.md) | Uncompiled earlier designs, experiments and probes | None |
| [`docs/se-proof-checklist.md`](https://github.com/elazarg/VegasCore/blob/research-tree/docs/se-proof-checklist.md), [`scripts/check-se-evidence.py`](https://github.com/elazarg/VegasCore/blob/research-tree/scripts/check-se-evidence.py), [`docs/se-compilation-stack.md`](https://github.com/elazarg/VegasCore/blob/research-tree/docs/se-compilation-stack.md), [`ARTIFACT.md`](https://github.com/elazarg/VegasCore/blob/research-tree/ARTIFACT.md) | The calendar checklist, its evidence check, and overviews of the calendar proof | The calendar theorem |
| [`Vegas.onePacket_intended_sequentialEquilibrium_of_openInputs`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketCertificateDischarge.lean#L4461), [`Vegas.onePacket_intended_raw_sequentialEquilibrium_of_blindInputs`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketCertificateAssembly.lean#L443) and the rest of the one-packet certificate | Turn-based SE preservation of the one-packet game and its bounded raw runtime, assuming the certificate's open inputs (value blindness, late commitments); a route left conditional | Plain contract on the sequential graph, count audit |
| [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/CommitRecoveryPreservation.lean#L22), [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_commitRecovery_continuing`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/CommitRecoveryContinuingExtension.lean#L24) | Intended SE extends to the source game with end-of-block rollback and permanent exclusion, keeping strategies, beliefs and the joint readout and payoff law | Source commit-recovery game |
| [`Vegas.phase_counted_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/PhaseRawReadoutLaw.lean#L27) | The raw count-audit extension of a phase-contract equilibrium keeps the typed readout jointly with the realized payoffs, for every scheduler | Phase contract, count audit |
| [`Vegas.SourceProgram.Setup.intended_sequentialEquilibrium_extends_without_voluntary_failure`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/ExclusionMoveExtension.lean#L64) | Intended SE extends to the full exclusion game without voluntary failure at nonexcluded decisions, under a continuation payoff floor | Source exclusion-move game (decision D3) |
| [`Vegas.watched_raw_equilibrium_extends`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/RevealServiceWatcher.lean#L123) | An equilibrium with a silent watcher extends to the full bounded raw game of the reveal service | Plain contract, reveal service |
| [`Vegas.onePacket_intended_sequentialEquilibrium_of_certificates`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketSequentialPreservation.lean#L71), [`Vegas.onePacket_intended_raw_sequentialEquilibrium`](https://github.com/elazarg/VegasCore/blob/research-tree/Vegas/Game/OnePacketSequentialPreservation.lean#L131) | Intended SE extends to the one-packet game and its bounded raw runtime, given the one-packet certificates and a deposit covering the spread of the exclusion payoff | Plain contract with exit payoff, count audit |
| [`GameTheory.Protocol.InformationModel.ActionRestriction.exists_deposits_preserving_sequential_equilibria`](https://github.com/elazarg/VegasCore/blob/research-tree/GameTheoryExtensions/Analysis/Protocol/TerminalAudit.lean#L269) | One finite nonnegative deposit vector extends every source SE to an audited target when each excluded action is collected with positive conditional probability | An action restriction and a sound terminal audit |
| [`GameTheory.Enforcement.exists_sound_deterrent_iff`](https://github.com/elazarg/VegasCore/blob/research-tree/GameTheoryExtensions/Analysis/ObservableEnforcement.lean#L168) | A sound alarm with a finite penalty deters one profitable deviation iff the deviation puts positive observable mass outside the admitted observations | None |
