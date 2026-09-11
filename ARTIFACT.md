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
| How are source decisions and graph reads related? | `Vegas/Compile/Compiler.lean`, `SourceAdequacy.lean`, and the event-graph laws |
| What executes public messages? | `Interaction/`, `Vegas/Compile/SealedSource.lean` |
| Which active games use that runtime? | `Vegas/Game/SealedMessages.lean`, `SealedRelease.lean`, `SealedTimeoutApplication.lean`, and `SealedStrategic.lean` |
| Which claims are paper-facing? | The single root audit, `Paper.lean` |

Read the owning theorem and definitions, not only its paper-facing restatement.
The audit pins theorem axioms; it does not prove that prose and formal
statements agree.

The separate manuscript checkout still contains the earlier claim registry and
is not synchronized with this migration. The active audit therefore records
only the strict sealed edge and the generic strategic interface below; archived
fused claims are not silently presented as current results. Until the manuscript
is rewritten, the paper-claim checker is not a completion gate for the active
tower. `--allow-missing-paper` only omits prose/snapshot validation; it does not
turn an unproved theorem into a proof.

## Trust and scope

Proved audit entries use Lean's standard logical axioms reported by
`#print axioms`. The active `Paper.lean` file is intentionally a small
direct-delegation audit surface and currently contains no admissions. Open
strategic work is documented as an obligation in `docs/active-tower.md`; it is
not disguised as a proved paper theorem. Production libraries cannot import
the audit or contain admissions.

The repository does not treat generated code, test vectors, or an executable
compiler alone as a refinement proof.

Native support theorems say that supported sealed-message executions decode to
reachable graph prefixes, and terminal prefixes reconstruct written-order
source executions with matching payout evaluation. The same support guarantee
holds for arbitrary bounded policy executions, including public pending
messages, delivery, inclusion, replay, malformed traffic, and withholding.
Ideal-service hiding is proved separately. These results are operational and
support-level; they do not identify an arbitrary runtime policy with a source
policy.

Strategic preservation is exposed by
`Vegas.SealedCompilation.StrategicCertificate`. A concrete runtime must provide
the honest outcome law and finite-mixture backtranslation for its considered
unilateral deviations. The generic GameTheory layer then proves expected-
utility guarantees and same-error approximate-Nash preservation and
reflection. The pending-message certificate is the next open proof obligation;
support refinement and hiding alone do not discharge it.

The reusable mechanism-design step for a designated quit is proved in
`GameTheoryExtensions/Core/QuitTransfer.lean`. It transfers a strict source
improvement whenever the runtime supplies a support-level law identifying the
target quit with the source quit. This law is a field-level obligation of a
concrete runtime certificate, not an assumption hidden in the sealed compiler.
