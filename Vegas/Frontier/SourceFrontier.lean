/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Commit
import Vegas.Frontier.SourceFrontier.Information
import Vegas.Frontier.SourceFrontier.Law
import Vegas.Frontier.SourceFrontier.Conditioned
import Vegas.Frontier.SourceFrontier.Strategic
import Vegas.Frontier.SourceFrontier.Replay
import Vegas.Frontier.SourceFrontier.Checkpoint
import Vegas.Frontier.SourceFrontier.Bisimulation
import Vegas.Frontier.SourceFrontier.Query
import Vegas.Frontier.SourceFrontier.SourceCompletion
import Vegas.Frontier.SourceFrontier.Action

/-!
# Raw source/frontier proof spine

This umbrella collects the proof modules for the raw source-local strategic
game to compiled frontier behavioral game bridge.

* `Commit` is the current source-order commit-node legality bridge.
* `Information` is hidden-value noninterference for serializing simultaneous
  frontier rounds as source-order blocks.
* `Law` is the PMF disintegration side for decomposing frontier action laws into
  sequential source choices.
* `Conditioned` composes law and commit facts to reflect a conditioned frontier
  node value back to source guard legality.
* `Query` turns support of projected frontier node-value laws into source query
  guard legality.
* `SourceCompletion` proves that the source strategic kernel reaches terminal
  support at the source instruction-count horizon.
* `Action` extends a source-legal current value to a full available frontier
  local action.
* `Strategic` names the source-local and frontier observed strategic surfaces.
* `Replay` connects source histories and frontier checkpoint histories to the
  same compiled graph states.
* `Checkpoint` proves the checkpoint-aligned source/frontier behavioral
  bisimulation.
* `Bisimulation` packages the raw source/frontier strategy and unilateral
  deviation translations into a Nash-deviation bisimulation.
-/

namespace Vegas

namespace SourceFrontier

end SourceFrontier

end Vegas
