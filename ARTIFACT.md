# VegasCore proof and artifact guide

This artifact checks the active sequential-source, event-graph, and native
public-message results. It is not a verification of a Kotlin frontend,
blockchain ledger, deployed contract, or EVM.

## Reproduction

Use the pinned Lean toolchain and dependency revisions:

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

Do not run `lake update` when reproducing a pinned revision. The cache is only
a build optimization; the subsequent build checks the proof terms.

## Reading route

| Question | Main location |
| --- | --- |
| What is a checked source program? | `Vegas/Core/` |
| What is its written-order execution? | `Vegas/Core/SmallStep.lean`, `Vegas/Core/Strategy.lean` |
| How is the event graph built? | `Vegas/Compile/Compiler.lean`, `Vegas/EventGraph/` |
| How are source decisions and graph reads related? | `Vegas/Compile/SourceLaw.lean` and adjacent compiler laws |
| What executes public messages? | `Interaction/`, `Vegas/Compile/SealedSource.lean` |
| Which retained applications use that runtime? | `Vegas/Game/SealedMessages.lean`, `SealedRelease.lean`, `SealedTimeoutApplication.lean`, and `Windowed.lean` |
| Which claims are paper-facing? | The single root audit, `Paper.lean` |

Read the owning theorem and definitions, not only its paper-facing restatement.
The audit pins theorem axioms; it does not prove that prose and formal
statements agree.

The manuscript's complete target remains registered in `paper-claims.json`.
Run `python scripts/check-paper-claims.py` for the strict paper-completion gate;
it fails on the explicit entries in `paper-obligations.json` until active proofs
replace them. The `--allow-open-obligations` development mode checks structural
integrity while reporting open obligations. Neither this mode nor an archived
proof is an active proof of the paper's claim. Without the separate manuscript
checkout, `--allow-missing-paper` omits prose/snapshot validation, not proof checks.

## Trust and scope

Proved audit entries use Lean's standard logical axioms reported by
`#print axioms`. Open targets in `Paper.lean` explicitly use `sorry` and have
axiom reports containing `sorryAx`. Their expected admission warnings are
guarded; other warnings still fail the build. Production libraries cannot
import the audit or contain admissions. A successful build therefore checks
the target statements' types, not their unproved conclusions.

The repository does not treat generated code, test vectors, or an executable
compiler alone as a refinement proof.

Native support theorems say that supported message executions decode to
reachable graph prefixes, and terminal prefixes reconstruct source executions
with matching public results. Independently, the fixed windowed block service
has an honest source law and a whole-program arbitrary randomized unilateral
deviation-mixture theorem. With its exact public-read, binding-origin,
fallback, roster, and unchanged-relay premises, this yields public-outcome
guarantees and same-error approximate-Nash preservation and reflection at
compiled profiles.

For the pending-message service, generalized checkpoint and prefix machinery,
the first-poll source law, preservation of acceptance across delivery and
reaction, and the paired delivery/reaction segment are checked. A complete
delivery block for an unrestricted binding now has a source successor and a
next checkpoint, including recipient delivery and reaction slots; progress is
proved from a duplicate-free unchanged relay and a source-certified fallback.
The whole-prefix pure-deviation extraction and final whole-program law remain
open. Local handler and service lemmas do not by themselves imply adaptive
progress or deadline fairness.
