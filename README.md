# VegasCore

VegasCore is a Lean 4 foundation for executable games with partial information.
Its strict compiler path is:

```text
sequential checked source
  -> typed event graph
  -> explicit sealed-message program
  -> native public-message execution
```

The source language gives choices an explicit owner and visible environment.
Compilation retains typed fields, dependencies, guards, probability tables,
and payoff code in an event graph. The native endpoint uses the shared
`Interaction` message pool and explicit commitment service.

The checked results include source execution and event-graph correspondence,
support-level reconstruction of native executions, and a constructed coupling
between source deviations and the actual pending-message round game. The
round-game theorem gives same-error Nash and epsilon-Nash equivalence under
timely service, normal source/native utility agreement, and an explicit
conditional comparison at each supported timeout checkpoint. A uniform
settlement cap is a checked sufficient case. For utilities valuing the programmed
payout, a source-only certificate also suffices: all legal source executions
give each player at least a bound, and executions recording that player's
designated quitting value give it at most that bound. The compiler derives
normal utility agreement and the runtime timeout comparison from this certificate.
More general source continuation conditions remain open.

The former application-plan path is archived under `archive/fused/`. Its
adjacent `commit; reveal` fusion emitted a value-bearing request without a
prior opaque commitment, so it was not a commitment implementation and is not
part of the active compiler or its claims.

The pending-message target is represented by the active message pool and timed
sealed adapter. Whole-prefix deviation extraction, randomized source/native
coupling, finite completion, and the conditional strategic composition above
are checked. Every invariant completed state also has a legal written-source
execution whose payout equals the payout reconstructed solely from public
initial data and opening events, including after timeout defaults; this applies
to supported outcomes of the actual round game without a service assumption.
That public-settlement witness need not preserve private committed choices and
therefore does not by itself discharge the timeout incentive condition.
The commitment service used by the strategic theorem binds each source site at
its first private registration and rejects unregistered handles. A candidate
host of the same program also permits competing candidates and accepts handles
without openings. Its immutable binding and source-settlement laws are checked,
including a legal source quitting witness after an owner's timeout. Extending
the causal coupling and Nash theorem to that host remains open.
Censorship resistance, concrete commitment cryptography, and EVM execution
correctness remain open.

The active libraries are `GameTheoryExtensions`, `Interaction`, `Vegas`,
the retained tests, and the source/native paper audit. See
[the artifact guide](ARTIFACT.md), [module boundaries](docs/module-architecture.md),
and [compilation design](docs/compilation-design.md).

## Build

```text
git submodule update --init --recursive
lake exe cache get
python scripts/check-doc-references.py
python scripts/check-lean-options.py
python scripts/check-module-boundaries.py
python -m unittest discover -s scripts -p "test_*.py"
lake --wfail build
```

GameTheory is a pinned, separately maintained software dependency. General
game-theoretic simulation results live under GameTheory namespaces; Vegas owns
the source language, event-graph compiler, and its native integration.

## Paper target and proof status

The single active `Paper.lean` audit contains only direct delegations to proved
repository theorems; it has no admissions and does not count archived claims.
The exact active layering, source-payout pending-message theorem, and next
end-to-end target are listed in
[the active tower](docs/active-tower.md).

A successful Lean build checks the active proof terms. It is not evidence that
the separate manuscript's claims are all established. `paper-claims.json`
distinguishes active audit mappings from explicitly unverified manuscript
claims. The latter are coverage gaps, not a count or a worklist of missing
theorems. Reference material supplies neither proofs nor audit obligations.

Readable source material for porting is preserved in the
[proof reference archive](archive/fused/README.md), outside all active libraries.
