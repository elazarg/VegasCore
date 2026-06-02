/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.Compiler
import Vegas.Compile.Checkpoint

/-!
# Compilation: checked Vegas programs to event graphs

`Compiler` lowers a `GraphProgram` / `WFProgram` into a canonical
`EventGraph.Graph` with numeric field and node ids. `Checkpoint` derives the
operational checkpoint model — the primitive downset schedule-abstraction
policy — from source guard legality.

This is the compiler layer. It is strictly below `Vegas.Frontier`: nothing here
imports the strategic frontier semantics. Dependency flows `Frontier → Compile`,
never the reverse.
-/
