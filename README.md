# VegasCore

VegasCore describes finite games with partial information, compiles them to
typed event graphs, and studies their execution through signed pending messages.
Blockchain runtimes are a target; the semantic interfaces remain runtime-general.

The source language supports private inputs, fresh bindings, public chance,
guarded resolution and withholding. The pending runtime has explicit clock and
expiry commands, authentic evidence and partial observation.

Checked results include asynchronous Nash preservation and nonconcurrent
recovery sequential-equilibrium preservation. Concurrent asynchronous SE
preservation under reserved service remains unproved; the
[concrete contract](Vegas/Game/ConcurrentRawSequentialPreservation.lean) and
[active proof plan](docs/se-concurrent-mechanization.md) state its exact scope
and remaining Lean transport obligations. The weaker general asynchronous contract
also has [checked preservation obstructions](docs/standard-runtime-se-status.md).
Honest outcome simulation alone does not establish equilibrium preservation.
The concurrent contract permits arbitrary correlated initial inputs with
finite support and requires finite binding types. Auctions with unbounded
binding bid/value choices are outside that contract. Its service uses one
unconditional exogenous tape prior for the whole execution, not
public-prefix-adaptive block priors.
The [module map](docs/module-architecture.md) locates the implementation.
Retired designs and experiments are in the
[uncompiled archive](archive/se-generalization/README.md).

Build and validate:

Local builds and CI use `lake build`; `lakefile.toml` makes Lean warnings errors.

```powershell
lake build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python scripts/check-se-evidence.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The GameTheory dependency is managed separately as a Git submodule.
