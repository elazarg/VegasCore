# Sequential-equilibrium proof: cold handoff

## Read this first

The full-language end-to-end theorem is proved and audited. The fixed
completion ledger is [se-proof-checklist.md](se-proof-checklist.md): S1–S5 and R1–R4 are
checked, and E1 composes them
(`Vegas.Paper.source_audited_raw_sequential_equilibrium`). The E2 validation
and claims audit is done; E2 closes when the reviewed result is pushed.
Do not create new milestone boxes for helper lemmas or close existing boxes
using conditional theorems with unproved compiler premises.

Consult the actual Git state when resuming; never overwrite existing work
blindly.

Do not modify the GameTheory submodule. Generic mathematics belongs in
`GameTheoryExtensions/`, generic execution in `Interaction/`, pending-message
semantics in `Vegas/Pending/`, and source/compiler proofs in `Vegas/Game/`.
Read `AGENTS.md`; all Lean options come from `lakefile.toml`.

## Fixed theorem and semantic decisions

Fix the program, initial distribution, utilities, bounded native interface,
backend service, audit rule and deposits **before choosing a source SE**.
Every source SE must have a full bounded raw-runtime SE preserving the joint
initial-type, public-result and realized net-payoff law. The source retains
private inputs, fresh commitments, public chance, guards and withholding.
The theorem is existential preservation; it does not assert reflection or a
fixed playerwise strategy translation.

Commitment meanings are fixed at submission. Player responses are atomic;
local computation is free and private scratch representation is not modeled.
Inclusion is at most once, including rejected calls. Passive partial leaks of
foreign traffic are hidden from the scheduler. The present theorem retains
bounded interaction and a finite response interface. PMF/unbounded interaction,
cryptography and an EVM implementation are separate refinements.

The audited backend assumes authentic partial signed phase/ledger evidence,
positive conditional collection coverage, protected service and collectible
fixed deposits. Missing samples are not evidence of omission. Every permitted
source choice must remain available. Utilities for the raw extension depend
on initial parameters and public outcomes, not on repaired future private
values. See [the stack document](se-compilation-stack.md) for exact scope.

## Checked interfaces to use

- S1: `SourceServiceLaw.lean` and `SourceServiceAudit.lean` establish initialized
  source execution and settlement for the full language.
- S2: `SourceServiceChoiceSupport.lean` gives one fully supported Bayes source
  sequence, and `TimedApproximant.ofSource` compiles each stage to a fully
  mixed native Bayes assessment; the SE limit theorem takes one common
  consistent subsequence. Consistency alone is not rationality.
- `SourceServiceBayes.lean` and `SourceServiceAssessment.lean` connect actual
  owner histories and native state beliefs to finite mixtures of comparisons
  in the **original** source assessment. Do not assume an SE or convergence of
  normalized source assessments.
- `SourceServiceTimedLaw.lean` identifies every timed native approximant's
  initialized typed-readout law with its original source strategy.
- `SourceServiceTimedContinuation.lean` gives the exact whole typed continuation
  law from any supported initialized phase boundary.
- `SourceServiceActiveBindingLaw.lean` and
  `SourceServiceActiveBindingCheckpoint.lean` start after the current passive
  sample and retain the current response, source value and remaining service.
- `SourceServiceAvailableOpening.lean` retains passed disclosure timing slots:
  these may represent an earlier silent source choice. Do not discard them as
  is valid for an unsent binding.
- `SourceLocalPolicy.lean` constructs one admitted syntactic alternative for
  an arbitrary finite local source choice law, shared across hidden histories
  at that observation. Its exact continuation is the replacement step followed
  by the original profile.
- `Vegas/Pending/ReactiveResponseConditioning.lean` recovers the actual selected
  current-response continuation by conditioning the full execution law on its
  persistent recall entry. It does not sample the activation twice.
- `Vegas/Pending/ReactiveSilentApplication.lean` preserves application laws
  through transport-only windows; it claims no equality of network or recall.
- `Vegas/Pending/ReactiveActiveOpening.lean` proves exact application settlement
  from an already sampled owner response, an unpassed optional opening slot,
  remaining visits and inclusion/ticks/expiry. Its assumptions include clean
  published traffic, a valid candidate and acceptance of the canonical opening.
- R2: `SourceServiceEvaluatorRepair.lean` supplies one legal repair policy
  before quantifying over hidden histories and identifies both marginals with
  the actual continuation evaluator.
- R3: `SourceServiceContinuationComparison.lean` proves conditional settlement
  dominance for one fixed deposit, uniformly over finite beliefs and profiles.
- R4: `SourceServiceRawExtension.lean` extends any permitted-runtime SE to the
  full bounded raw runtime, including rational off-path completion and raw
  aliases, preserving the initialized joint observation/settlement law.

These are existing lemmas, not open premises to restate in a new model.

## S4 proof design

Use a **fixed** positive timing law for every source approximant. The existing
roster timing construction with weight `1/2` mixes uniform opportunities and
the final opportunity equally. Every slot remains possible and remaining
timing mass is at least `1/2` at every owner decision. This is a strategy
witness, not a restriction of target menus.

`GameTheoryExtensions/Math/Probability/DeferredChoice.lean` contains the checked
conditional-regret bound: if both original binary pure gains are at most an
error and remaining timing mass is at least a positive lower bound, every
conditional replacement mixture has gain at most error divided by that lower
bound. Thus the fixed timing witness needs only a factor of two. No timing
convergence or minimum over all roster sizes is needed.

For unopened disclosure, with source probability q and remaining timing mass
T, survival is D = 1 - q(1-T), and eventual disclosure probability is qT/D.
The unfinished operational proof must derive these probabilities from the
actual own response history and sampler, then identify the two complete
continuation values. The scalar theorem alone does not discharge S4.

For unsent binding, condition the checked full source-value/timing execution
law on the actual current response. The resulting source-value distribution
must be common across the native information fiber. Use the admitted local
source-policy theorem and the original-assessment comparison.

For public sampling, foreign visits and already recorded choices, prove exact
equality of actual continuation outcomes for permitted alternatives, then
average under the actual native belief. Do not assert that foreign native
observations equal source observations: early observations remain in recall.

## S4 interface and remaining cases

[SourceServiceLocalComparison](../Vegas/Game/SourceServiceLocalComparison.lean)
fixes the interface every S4 case uses. `SourceServiceSpec` bundles the
service and its compiler side conditions. `TimedApproximant` bundles one fully
mixed timed stage. `TimedApproximant.ofSource` builds the stage of the common
S2 sequence for a fully supported source strategy, and `ofSource_bayes` gives
its Bayes consistency. Every actual decision has a `DecisionPhase`
(`SourceServiceSpec.exists_decisionPhase`). Three generic steps are proved
once:

- `TimedApproximant.response_continuation_law`: after any legal response, the
  complete typed source terminal law is the source continuation from the next
  event boundary, averaged over the actual application law of the phase.
- `TimedApproximant.local_law_readout`: a local lottery runs as the lottery
  over current responses.
- `TimedApproximant.comparison_eq_of_phase_invariant`: if every legal response
  leaves the same next-boundary application law at every history of a site,
  prescribed and alternative assessment laws are equal for every local lottery.

Checked instances: public-sampling sites
(`TimedApproximant.sample_comparison_eq`), foreign visits to binding and
disclosure events (`TimedApproximant.foreign_binding_comparison_eq`,
`TimedApproximant.foreign_disclosure_comparison_eq`), and owner visits after a
recorded binding or opening (`TimedApproximant.recorded_comparison_eq`,
`TimedApproximant.recorded_disclosure_comparison_eq`). The
[completion plan](se-completion-plan.md) orders the remaining work: E2
validation. Without an available opening the
owner's disclosure site has zero gain
(`TimedApproximant.absent_opening_comparison_eq`); with one, it gains at most
the source comparison error divided by the remaining timing mass
(`TimedApproximant.available_opening_gain_le`). Owner visits
to an unsent binding are an exact simulation by original source deviations
(`TimedApproximant.unsent_binding_comparisons`).
Every site has a `DecisionSiteKind` (`SourceServiceSpec.exists_siteKind`), which
selects its comparison. `SourceServiceSpec.exists_native_sequentialEquilibrium`
combines them into the S5 theorem.

## Build and validation discipline

Check any module, including a draft that no aggregator imports, with
`lake --wfail build Module.Name`. It applies every option in `lakefile.toml`
and needs no setup file; the per-module setup JSONs and direct checker commands
in the lane notes are unnecessary. Bare `lake env lean file.lean` omits the
central options and can produce unrelated elaboration failures. Run one Lake
build at a time: a build removes the oleans it is replacing, so a concurrent
check can fail on a missing import that is not a real error. The lane notes'
coordination instructions (build queues, lane ownership, process handles) do
not apply.

The last reviewed proof batch passed a configured 3,756-job targeted build and
the module-boundary, documentation-reference, central-options and whitespace
gates. The active-opening leaf separately passed its configured 1,876-job
build. These are targeted checks, not the outstanding E2 full-repository audit.

For readable batches, freeze released files, stage only those files, run the
static gates against an index snapshot, and verify staged/snapshot/worktree
bytes agree before committing and pushing. Keep unfinished drafts out of the
main build roots. The source paper abstract and first half of the introduction
are outside the requested revision scope; no paper changes are part of this
handoff.
