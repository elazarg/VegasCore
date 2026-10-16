/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAnchoredPolicy

/-! # Owner locality of anchored response replay -/

namespace Interaction.ReactiveApplication

variable {Principal : Type} {app : ReactiveApplication Principal}

/-- An anchored owner's response depends only on that owner's continuing policy. -/
theorem anchoredPolicy_owner_congr (anchor : app.Execution) (owner : Principal)
    (first second : Principal → app.Policy) (same : first owner = second owner) :
    anchoredPolicy anchor first owner = anchoredPolicy anchor second owner := by
  funext past view
  unfold anchoredPolicy
  rw [same]

end Interaction.ReactiveApplication
