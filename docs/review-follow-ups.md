# Review follow-ups

A six-part review of the repository and paper (proof engineering, proof mining,
game theory, programming languages, cryptography, blockchain) found no proof
errors. Wording, scope and documentation defects that had a clear fix are fixed
in the code, the paper and the status documents. This file records the items
that need design work, larger mechanical changes, or a decision, grouped by
kind. Future-work areas outside the paper's scope are listed at the end.

## Lean statements and proofs

**Deposit range over terminal histories.**
`Vegas.rosterAuditDeposit`
([ServicePayoffBounds.lean](../Vegas/Game/ServicePayoffBounds.lean)) takes the
payoff range over every native history, and `Vegas.baseUtility` is zero on an
unfinished one, so the range always contains zero. The deposit is sufficient
but not invariant under adding a constant to all utilities (for payoffs in
[74, 126] it is 126/p instead of 52/p). The paper and the assumptions table now
describe the definition as it is. Tightening it needs
`rosterAuditDeposit_covers_gain` to know that both compared histories are
terminal: the repair endpoints come from the stopped couplings in
`SourceServiceRepairSettlement.lean`, and their terminality has to be threaded
from the bounded horizon. Then restrict the extrema to terminal histories and
prove invariance under adding a constant.

**The construction of the native equilibrium in the statement.** The SE theorem
now states that the audit charges no one on the equilibrium's paths and gives
the law of the typed terminal state. The paper describes the construction in
the proof sketch only: the permitted-runtime equilibrium is a subsequential
limit of `TimedApproximant.ofSource` assessments of one fully supported Bayes
source sequence, and the raw equilibrium is its canonical raw extension. The
proofs establish both and drop them in `SourceServiceEquilibrium.lean` (the
convergence component of the limit theorem),
`SourceServiceRestrictionExtension.lean` (`ExtendsProfile`) and
`SourceServiceRawExtension.lean` (the `canonicalRawPolicy` equation). Stating
them needs the source sequence and timing law as existential witnesses.

**Guard dependencies.** A guard's required inputs come from the expression dependency function, an
expression-interface field constrained only to over-approximate what the code
reads (`Vegas/Foundation/Guard.lean`, `Vegas/Foundation/ExprInterface.lean`).
Two expression languages with the same evaluation but different sound
dependency functions therefore define different source games, and a
meaning-preserving rewrite of guard code can move where the guard is checked.
The paper now says the dependency set is part of the program. Two fixes: use
the guard's declared `schema`, which `GuardCode` already carries, as its read
set, with a congruence lemma for codes of equal meaning; or add an interface
law that determines the dependency function from the code's syntax.

**A concrete service.** No `SourceServiceSpec` is constructed anywhere, so no
concrete program is shown to meet the service hypotheses together.
`SourceServiceSpec.completeAudit_raw_sequentialEquilibrium_preserved` removes
the audit hypotheses. What remains is a constructor for programs with finite
binding payload types: one activation per event actor
(`ActorOpportunities` holds by construction), the message values enumerated
from the finite payload types together with the supported initial binding
tables, and one candidate slot per event. With it, the two-reveal monitored
guessing program or Odds–Evens becomes an unconditional corollary.

**Odds–Evens.** The paper's running example has no Lean program. Its settlement
is expressible in the current expression language (conditional, failure test,
equality, result default). Mechanizing it, with the source Nash argument,
would replace the one remaining informal incentive argument in the paper.

**Guard blame.** A rejected guard fails the publication at its completing
reveal, and the guard-read discipline makes that reveal the guard author's.
The paper could state this, but it should first be a Lean lemma.

## Engineering

**Unused modules.** A dependency walk from every `Paper.lean` statement, axiom
pin and test finds modules with no reached declaration. Deleting them needs the
importing modules repaired first, and some are cited in documents:

| Module (`Vegas/Game/`) | Imported by | Cited in |
| --- | --- | --- |
| `SourceServiceResolution` | `SourceServiceResolutionBoundary`, `SourceServiceSettlement` | `se-compilation-stack.md`, `research/se-runtime-assumptions.md` |
| `SourceServiceActiveDisclosureLaw` | `SourceServiceDisclosureContinuation`, `SourceServiceTimingPosterior` | `se-compilation-stack.md`, `se-handoff.md` |
| `SourceServiceBindingExecution` | `SourceServiceTimedBinding` | `research/se-runtime-assumptions.md` |
| `SourceServiceBindingCheckpoint` | `SourceServiceBoundary` | `research/se-runtime-assumptions.md` |
| `SourceServiceBindingWindow` | `SourceServiceBindingSupport` | |
| `SourceServiceBindingRepair` | | `research/se-runtime-assumptions.md` |
| `SourceServiceCandidateStep` | `SourceServiceBindingCheckpoint` | |
| `SourceServiceCandidateObservation` | `SourceServiceFactorization` | `research/se-runtime-assumptions.md` |
| `SourceServiceDisclosureContinuation` | | |
| `SourceServiceDisclosureMemory` | `SourceServiceFactorization` | `research/se-runtime-assumptions.md` |
| `SourceServiceDisclosurePosterior` | `SourceServiceDisclosureMemory` | |
| `SourceServiceTimedConsistency` | | `se-compilation-stack.md`, `se-handoff.md` |
| `RevealServiceOwnerContinuation` | `RevealServiceOwnerResponse` | |
| `RevealServicePrefixContinuation` | `RevealServiceOwnerContinuation`, `RevealServicePrefixResponse` | |
| `RevealServiceRosterBoundaryPosterior` | | |
| `RevealServiceRosterConsistency` | | `research/se-ambient-rosters.md` |
| `RevealServiceRosterWindowContinuation` | `RevealServiceRosterWindowValue` | |

`SetupSubgame` and `SourceObservationRecall` are also unreached. The theorem
`sourceServiceCompiledProfile_settlement_law` (`SourceServiceAudit.lean`) is
unused; the checklist no longer cites it.

**Namespaces.** The full-language development opens
`namespace Vegas.SourceProgram.RevealService`, but no `RevealService` type
exists. That breaks the flat-namespace rule and gives the headline theorem a
name that suggests the reveal-only fragment. Moving the declarations to
`Vegas` or to real type namespaces such as `SourceServiceSpec` is mechanical
but touches about 250 files and the documents that cite the names.

**Named interfaces.**
- `sourceService_decision_boundary` returns about 30 components that 21 call
  sites destructure by position; `initialized_sourceService_prefix_support` has
  22. A structure with named fields, in the style of `DecisionPhase`, makes
  them robust to reordering.
- The timing-law type is written out 106 times and the source information model
  58 times; name them a timing-law type and a source-model
  abbreviation on `SourceServiceSpec`.
- About 80 declarations take the value coverage, capacity, opportunities and
  initial values separately; lower layers could take a bundled structure.
- Generic finite-distribution lemmas are copied as file-private helpers:
  two copies of a fibre-conditioning support lemma, four copies of a kernel
  iteration lemma, and two copies of a cast-transport lemma with a variant. They belong in
  `GameTheoryExtensions/Math/Probability`, as do
  a coupling interface for the 97
  repeated coupling-marginal equations.
- The `nodeView` case analysis after its output and code equations appears 44
  times; one lemma would replace it.
- `rosterTiming` duplicates the unused `FinDist.finalTiming`.

**Reachability gate.** The module gate checks import reachability, which the
aggregators make trivially true. A gate that walks declarations from
`Paper.lean`, and checks that every evidence name in the checklist is reached
from the SE theorem, would catch unused proof towers and stale evidence.

**Paper annotations.** `check-doc-references.py` does not scan the `% Lean:`
annotations in `overleaf/`; extending it would catch renamed declarations.

## Paper presentation

These are within scope but cost page budget:

- A figure with the core grammar, the typing judgment (the open-commitment
  index as a linear obligation set) and big-step rules.
  `overleaf/operational-core.tex` has the material.
- Name the correctness criterion, the mixture simulation between game forms
  and its vertical composition, and say what it preserves and what it does not.
- Separate notation for the source public-outcome law and the graph and native
  terminal-state laws, and a glossary for reveal, resolve, disclosure, opening
  and publication.

## Future work

Listed for completeness; none is needed for the current claims.

- Equilibria: a checked non-reflection witness from the opening-timing channel;
  necessity witnesses for actor opportunities and for the audit; refinements
  beyond SE; welfare.
- Quantitative: a transfer bound for the explicit timed approximants without a
  limit, and an SE-implies-Nash corollary for the audited runtime.
- Assumptions: coverage only on reachable transcripts, admitting fixed-budget
  auditors; sharper regret constants and other timing weights; per-player
  errors.
- Cryptography: a UC-style refinement to computational equilibria, deposit
  slack for negligible errors, author-signed phase context with strongly
  unforgeable signatures, and non-transferable openings.
- Chains: realizable audits (phase-bound envelopes, hashed evidence filings,
  recipient reporters, state channels); strategic sequencers and adaptive event
  order for SE; fees as an error term; finality; encrypted mempools; an EVM
  target via EVMYulLean with case studies.
- Language: a checked front end, public branching, composition, private chance
  after setup, parametric program families, program equivalence, a computable
  reference interpreter, and integer operations in the expression language.
- Codebase: retire or re-derive the reveal-only tower from the full-language
  theorem; split `Vegas/Game`; runtime regressions; restatements for results
  that only have axiom pins.
