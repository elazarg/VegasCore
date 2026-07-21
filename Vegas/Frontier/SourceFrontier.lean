/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Commit
import Vegas.Frontier.SourceFrontier.Strategic
import Vegas.Frontier.SourceFrontier.Replay
import Vegas.Frontier.SourceFrontier.Checkpoint
import Vegas.Frontier.SourceFrontier.Query
import Vegas.Frontier.SourceFrontier.SourceCompletion
import Vegas.Frontier.SourceFrontier.Action
import Vegas.Frontier.SourceFrontier.Projected
import Vegas.Frontier.SourceFrontier.Strategy

/-!
# Raw source/frontier proof spine

This umbrella collects the proof modules for the raw source-local strategic
game to compiled frontier behavioral game bridge.

* `Commit` is the current source-order commit-node legality bridge.
* `Query` turns support of projected frontier node-value laws into source query
  guard legality.
* `SourceCompletion` proves that the source strategic kernel reaches terminal
  support at the source instruction-count horizon.
* `Action` extends a source-legal current value to a full available frontier
  local action.
* `Projected` proves that an active frontier legal-action law always assigns a
  concrete value to the replayed source current node.
* `Strategy` erases that projection's impossible `none` branch and packages a
  frontier-induced source commit-value law.
* `Strategic` names the source-local and frontier observed strategic surfaces.
* `Replay` connects source histories and frontier checkpoint histories to the
  same compiled graph states.
* `Checkpoint` proves the checkpoint-aligned source/frontier behavioral
  bisimulation.
-/
