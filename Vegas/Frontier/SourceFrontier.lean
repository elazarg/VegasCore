/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Frontier.SourceFrontier.Commit
import Vegas.Frontier.SourceFrontier.Information
import Vegas.Frontier.SourceFrontier.Law
import Vegas.Frontier.SourceFrontier.Conditioned

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
-/

namespace Vegas

namespace SourceFrontier

end SourceFrontier

end Vegas
