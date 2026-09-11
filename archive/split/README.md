# Proof reference archive

This directory preserves readable sources for reuse. It is not a Lean library,
is not on the import path, and supplies no active compiler theorem. Source files
have a `.lean.txt` suffix so neither Lake nor documentation generation treats
them as modules. The module-boundary checker rejects imports of archived-only
modules, including imports that a stale compiled artifact might otherwise allow.

The complete checked reference checkout is VegasCore commit
`82cc606`; its manuscript checkout is
`236f22715e10f5ed47f5d6d0bab082bbaae9ff6f`. File paths below reproduce their
original locations. Files retained in the active tower are available at that
same source revision when reproducing a reference proof.

| Sources | Material to inspect when porting |
| --- | --- |
| `Vegas/Runtime/` | Outcome/utility distinctions, strategic simulations, quitting and information conditions, request-policy proofs. Generic results belong in GameTheory when reused. |
| `Vegas/Scheduled/` | Public-order replay, predrawing and scheduler-information arguments. These do not themselves establish a pending-message runtime theorem. |
| `Vegas/Game/` and selected `Vegas/Compile/` files | Graph-game presentations and their source/request correspondences. |
| `Vegas/Machine/` and `VegasEVM/` | Machine refinements, storage/ABI representations, instruction semantics and local code-generation proofs. Whole-backend refinement was not discharged. |
| `VegasTests/` | Concrete witnesses and regression proofs, including originals of mixed fixtures whose native portions remain active. |
| `Paper/`, `Paper.lean.txt`, and `overleaf/` | Audit statements, axiom reports and manuscript context for the reference results. |
| `docs/`, `README.md.txt`, `ARTIFACT.md.txt` | Detailed design arguments, limitations, and proof-reading guides. |

Port a result against the native semantics of its destination layer and build
it there. Copying a statement or proof does not establish its applicability to
that layer. In particular, private request windows cannot stand in for
observable in-flight messages, and a graph-state refinement cannot stand in
for a strategic theorem about a ledger or VM.

The active manuscript and its target claim registry remain unchanged. Explicit
open obligations identify missing active replacements; this archive does not
satisfy the paper's proof-completion gate.
