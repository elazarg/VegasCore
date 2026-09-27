# Sequential-equilibrium proof: cold handoff

## Read this first

The full-language end-to-end theorem is **not proved**. The fixed completion
ledger is [se-proof-checklist.md](se-proof-checklist.md): S1, S2 and R1–R4 are
checked; S3–S5 and E1–E2 remain open. The main mathematical work is S3–S4.
Do not create new milestone boxes for helper lemmas or close existing boxes
using conditional theorems with unproved compiler premises.

The working branch is `spe`. The separate branch `spe-handoff-20260927`
preserves unfinished proof files and detailed lane notes. Its draft files are
not all checked and are deliberately absent from the main build roots. The
ordinary `spe` branch contains the reviewed, checked proof batches. Consult
the actual Git state when resuming; never overwrite existing work blindly.

Do not modify the GameTheory submodule. Generic mathematics belongs in
`GameTheoryExtensions/`, generic execution in `Interaction/`, pending-message
semantics in `Vegas/Pending/`, and source/compiler proofs in `Vegas/Game/`.
Read `AGENTS.md`; all Lean options come from `lakefile.toml`. The user's
untracked `docs/Lean434BumpLessons.md` is unrelated and must remain untouched.

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
- S2: `SourceServiceTimedConsistency.lean` constructs fully mixed actual native
  profiles, Bayes beliefs and one common consistent subsequence from an original
  source consistent assessment. Consistency alone is not rationality.
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
- `SourceServiceActiveDisclosureLaw.lean` retains passed timing slots: these
  may represent an earlier silent source choice. Do not discard them as is
  valid for an unsent binding.
- `SourceLocalPolicy.lean` constructs one admitted syntactic alternative for
  an arbitrary finite local source choice law, shared across hidden histories
  at that observation. Its exact continuation is the replacement step followed
  by the original profile.
- `Vegas/Pending/ReactiveResponseConditioning.lean` recovers the actual selected
  current-response continuation by conditioning the full execution law on its
  persistent recall entry. It does not sample the activation twice.
- `Vegas/Pending/ReactiveReplayApplication.lean` preserves application laws
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

## Immediate unfinished work

The handoff branch includes three lane notes in `docs/se-handoff-notes/` with
precise draft status, diagnostics and interfaces. The principal draft files are:

1. [SourceServiceBindingContinuation](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceBindingContinuation.lean): current-response binding
   continuation and common source-choice distribution. An elaborator free-variable
   failure in the dependent statement is being isolated; this is not checked.
2. [ScheduledChoicePosterior](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Interaction/ScheduledChoicePosterior.lean) and
   [SourceServiceTimingPosterior](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceTimingPosterior.lean): actual waiting likelihoods
   and timing posterior, including initialization from dormant recall.
3. [SourceServiceDisclosureContinuation](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceDisclosureContinuation.lean): disclosure continuation
   work. The active raw opening checkpoint still needs the passed-slot/silence
   case and the typed guarded source-successor connection.
4. [SourceServiceTimedReachability](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceTimedReachability.lean): fully mixed legal response
   support and transfer back into initialized physical prefix support.
5. [SourceServiceHarmlessContinuation](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceHarmlessContinuation.lean),
   [SourceServiceSampleComparison](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceSampleComparison.lean), and
   [SourceServiceRecordedContinuation](https://github.com/elazarg/VegasCore/blob/spe-handoff-20260927/Vegas/Game/SourceServiceRecordedContinuation.lean): application-law
   congruence through the full source suffix and actual harmless local gains.

For the remaining active-opening case, reuse the checked opening frame and
replay invariants. A passed selected slot produces replay only. From clean
published traffic, replay preserves the application, reserved inclusion is
idle, and the actual deadline completes the false branch. The current
activation must not be sampled again. A future selected slot is already
handled by the checked active-opening theorem.

Once all local cases check, combine their vanishing gain bounds with
`GameTheoryExtensions/Analysis/Protocol/LocalSimulationLimit.lean`, the actual
common sequence, and the initialized timed law. This closes S5 only after
the complete source-to-permitted-runtime statement checks. Then compose R4
for E1 and perform the full integration and claims audit for E2.

## Build and validation discipline

Use `lake --wfail build Module.Name`; bare `lake env lean file.lean` omits central
options and can produce unrelated elaboration failures. A scratch checker must
load all central options and set the **actual module name** in its setup JSON.
Reusing another module's name can collide on generated private declarations.

Configured builds temporarily remove imported oleans. Do not repeatedly launch
dependent checks or restart live builds because an olean is missing. Poll the
specific live handle until terminal; only then decide whether a rebuild is
needed. Inspect authoritative process state after a cold restart.

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
