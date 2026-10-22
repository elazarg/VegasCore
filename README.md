# VegasCore

VegasCore describes finite games with partial information, compiles them to
typed event graphs, and studies their execution through signed pending messages.
Blockchain runtimes are a target; the semantic interfaces remain runtime-general.

The source language supports private inputs, fresh bindings, public chance,
guarded resolution and withholding. The pending runtime has explicit clock and
expiry commands, authentic evidence and partial observation.

Checked results include asynchronous Nash preservation, nonconcurrent recovery
sequential-equilibrium preservation, and
[concurrent sequential-equilibrium preservation under reserved service](Vegas/Game/ConcurrentRawEquilibrium.lean).
The original weighted transport, reconstruction and preservation theorems are
Lean-checked using only `propext`, `Classical.choice` and `Quot.sound`.
The [concrete contract](Vegas/Game/ConcurrentRawSequentialPreservation.lean) and
[proof status](docs/se-concurrent-mechanization.md) state the hypotheses and
checked construction.

The concurrent result covers private commitments in literal `.concurrent` mode,
with source-ordered public barriers, arbitrary correlated initial inputs of
finite support, and finite binding types. Its service samples one unconditional
exogenous tape prior for the whole execution; tape coordinates may correlate
across owners and time. Public-prefix-adaptive block priors and unbounded
binding bid/value choices are outside the contract. The operational and funded
audit hypotheses are sufficient conditions, not minimality or a chain
implementation guarantee. An unrestricted prefix density theorem is not claimed.
The weaker general asynchronous contract has
[checked preservation obstructions](docs/standard-runtime-se-status.md).
Honest outcome simulation alone does not establish equilibrium preservation.
The [module map](docs/module-architecture.md) locates the implementation.
Retired designs and experiments are in the
[uncompiled archive](archive/se-generalization/README.md).

Build and validate:

Local builds and CI use `lake build`; `lakefile.toml` makes Lean warnings errors.
The source policy rejects unregistered proof holes. The concurrent preservation
theorem has a standard-axiom regression guard. Run the checks with the build
before committing.

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python scripts/check-se-evidence.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The GameTheory dependency is managed separately as a Git submodule.
