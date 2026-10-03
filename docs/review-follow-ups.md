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

**Unreached modules that are cited or used.** A dependency walk from every
`Paper.lean` statement, axiom pin, test and example reaches no declaration in
the modules below. Each is still cited as a result in `ARTIFACT.md` or a
design or research note, or used by another module's proof, or is kept
intentionally standalone (`docs/module-architecture.md`), so deleting it is a
decision about the claim, not about dead code. For each, the choice is to pin
the cited result in `Paper.lean` or to retire it together with its citation.

| Module | Cited in |
| --- | --- |
| `GameTheoryExtensions.Core.RegularChoiceSimulation` | `inclusion-and-spe.md`, `inclusion-assumptions.md`, `reactive-recovery.md` |
| `GameTheoryExtensions.Math.Probability.FirstDeparture` | `ARTIFACT.md` |
| `GameTheoryExtensions.Math.Probability.NegligibleContamination` | `ARTIFACT.md` |
| `GameTheoryExtensions.Math.Probability.RegularCoupling` | `inclusion-and-spe.md`, `inclusion-assumptions.md` |
| `GameTheoryExtensions.Math.Probability.WeightedSet` | `inclusion-assumptions.md` |
| `GameTheoryExtensions.Protocol.BehavioralIncentives` | `spe-incentive-criterion.md`, `spe-obstructions.md` |
| `Interaction.MessageApplicationLocality` | `module-architecture.md` |
| `Interaction.MessageApplicationPending` | `module-architecture.md` |
| `Interaction.PendingWeighted` | `inclusion-and-spe.md`, `inclusion-assumptions.md` |
| `Interaction.ReactiveKnowledge` | `module-architecture.md`, `passive-eavesdropping.md`, `spe-obstructions.md` |
| `Interaction.ReactivePendingRetention` | used by other modules |
| `Interaction.ReactivePublishedResponses` | `ARTIFACT.md` |
| `Interaction.ReactiveRecallInvariant` | `ARTIFACT.md` |
| `Interaction.ReactiveRecordedResponse` | `ARTIFACT.md` |
| `Interaction.ReactiveSubmissionRounds` | used by other modules |
| `Vegas.Compile.EventGraphEvidence` | `ambient-communication.md`, `module-architecture.md` |
| `Vegas.Game.BindingRepairOpening` | `research/se-hidden-binding.md` |
| `Vegas.Game.ReactiveCompilation` | `module-architecture.md`, `network-and-compilation.md`, `spe-obstructions.md` |
| `Vegas.Game.SetupSubgame` | `ARTIFACT.md`, `preservation-contracts.md`, `source-semantics.md`, `subgame-preservation.md` |
| `Vegas.Game.SourceObservationRecall` | `ARTIFACT.md` |
| `Vegas.Game.SourceServiceDisclosureMemory` | `research/se-runtime-assumptions.md` |
| `Vegas.Game.SourceServiceDisclosurePosterior` | used by other modules |
| `Vegas.Pending.EventFreshCandidates` | `ARTIFACT.md`, `preservation-contracts.md` |
| `Vegas.Pending.NativeRecall` | `action-coalescing.md` |
| `Vegas.Pending.ReactiveActiveOpening` | `se-handoff.md` |
| `Vegas.Pending.ReactiveAuthorizationProgress` | `ARTIFACT.md`, `reactive-spe-service.md` |
| `Vegas.Pending.ReactiveBindingAdmission` | `ambient-communication.md` |
| `Vegas.Pending.ReactiveBindingFrameExpiry` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveBindingFrameLaw` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveBindingGuardedInclusion` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveBindingLegalContinuation` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveBindingObservation` | `ARTIFACT.md`, `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveBindingPosterior` | `research/se-runtime-assumptions.md` |
| `Vegas.Pending.ReactiveBindingRequiredStep` | `research/se-runtime-assumptions.md` |
| `Vegas.Pending.ReactiveBindingResources` | `research/se-pmf-interaction.md`, `research/se-runtime-assumptions.md` |
| `Vegas.Pending.ReactiveBindingService` | `ambient-communication.md`, `sequential-equilibrium-design.md` |
| `Vegas.Pending.ReactiveBindingServiceRepair` | used by other modules |
| `Vegas.Pending.ReactiveBindingStopped` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveDisclosureService` | `ambient-communication.md`, `zero-sum-runtime-bridge.md` |
| `Vegas.Pending.ReactiveFiniteConsistency` | `finite-reactive-responses.md`, `private-memory-and-subgames.md`, `sequential-equilibrium-design.md`, `zero-sum-runtime-bridge.md` |
| `Vegas.Pending.ReactiveFreshCandidates` | `network-and-compilation.md`, `spe-obstructions.md` |
| `Vegas.Pending.ReactiveHiddenEnvironment` | `research/se-hidden-binding.md` |
| `Vegas.Pending.ReactiveOpeningPosterior` | `research/se-ambient-rosters.md`, `research/se-opening-timing.md` |
| `Vegas.Pending.ReactiveRegularity` | `inclusion-and-spe.md`, `inclusion-assumptions.md`, `reactive-recovery.md` |
| `Vegas.Pending.ReactiveSelection` | `inclusion-and-spe.md`, `inclusion-assumptions.md` |
| `Vegas.Pending.ResponseProtocolRefinement` | `action-coalescing.md` |
| `Vegas.Source.SetupProtocolPolicy` | used by other modules |

**Positional destructuring of the decision boundary.**
`Vegas.sourceService_decision_boundary` returns about 30 components that 21
call sites destructure by position. A structure with named fields was
considered and not adopted: most call sites take apart the residual program
(`cases` on it) or substitute the event, which needs local variables, so they
would still destructure positionally, and projections would add casts where
the event is rewritten. The positional patterns also name fields
inconsistently between files; aligning those names is the cheaper
improvement.

**Bundled service data.** About 80 lower-layer declarations take the value
coverage, capacity, opportunities and initial values separately. They are
stated over a bare setup and message bounds so that the reveal-only
development can use them with its own bounds; bundling them into
`SourceServiceSpec` would couple them to the full-language service. A smaller
bundle for the bounds alone is possible but was not needed by any proof.

**Roster timing.** `Vegas.rosterTiming` repeats the construction of the
generic `finalTiming`. The two are indexed differently
(`Fin ((rosters event).count owner)` against `Fin (last + 1)`), so defining one
through the other adds a cast to every use; the duplication is three short
lemmas.

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
