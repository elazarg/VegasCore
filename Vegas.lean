/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory
import Vegas.Core
import Vegas.Source
import Vegas.Graph
import Vegas.Foundation.ViewExtension
import Vegas.EventGraph
import Vegas.Language
import Vegas.Compile
import Vegas.Game

/-! # Vegas

Failure-aware source programs compile to typed immutable graphs. The public
message host executes those graphs; its whole-program strategic correspondence
remains to be proved. The restricted `WFProgram` candidate backend has separate
checked strategic results, with its hypotheses explicit at each capstone.
-/
