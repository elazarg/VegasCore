/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory
import Vegas.Compile
import Vegas.EventGraph
import Vegas.Examples
import Vegas.Expr
import Vegas.Game
import Vegas.Pending
import Vegas.Source

/-! # Vegas

Failure-aware source programs compile to typed immutable graphs, and the public
message host executes those graphs with checked whole-program strategic
correspondence.
-/
