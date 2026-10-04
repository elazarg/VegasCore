# VegasCore

VegasCore describes finite games with partial information, compiles them to
typed event graphs, and studies their execution through signed pending messages.
Blockchain runtimes are a target; the semantic interfaces remain runtime-general.

The source language supports private inputs, fresh bindings, public chance,
guarded resolution and withholding. The pending runtime has explicit clock and
expiry commands, authentic evidence and partial observation.

The fixed-calendar sequential-equilibrium preservation theorem is checked.
Preservation for arbitrary admissible builders remains open. The
[design and proof plan](docs/se-schedule-generalization.md) states the semantics,
concrete issues and a finite experiment for the missing timing and belief
comparisons. Honest outcome simulation alone does not establish equilibrium
preservation. The [calendar checklist](docs/se-proof-checklist.md)
records its checked evidence; the [module map](docs/module-architecture.md) locates
the implementation. Retired designs and experiments are in the
[uncompiled archive](archive/se-generalization/README.md).

Build and validate:

```powershell
lake --wfail build
python scripts/check-module-boundaries.py
python scripts/check-lean-options.py
python scripts/check-doc-references.py
python scripts/check-se-evidence.py
python -m unittest discover -s scripts -p 'test_*.py'
```

The GameTheory dependency is managed separately as a Git submodule.
