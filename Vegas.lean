/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import GameTheory
import Vegas.Expr
import Vegas.Source
import Vegas.EventGraph
import Vegas.Pending
import Vegas.Foundation.ViewExtension
import Vegas.Language
import Vegas.Compile
import Vegas.Game

/-! # Vegas

Failure-aware source programs compile to typed immutable graphs, and the public
message host executes those graphs with checked whole-program strategic
correspondence.
-/
