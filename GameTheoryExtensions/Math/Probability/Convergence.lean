/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Math.Probability.Compactness
import GameTheory.Math.Probability.Convergence

/-! # Pointwise limits of probability laws -/

noncomputable section

namespace GameTheory.Math.Probability

open Filter

/-- A sequence of laws has at most one pointwise limit. -/
theorem PMFConvergesPointwise.unique {α : Type*}
    {sequence : ℕ → PMF α} {first second : PMF α}
    (firstLimit : PMFConvergesPointwise sequence first)
    (secondLimit : PMFConvergesPointwise sequence second) : first = second :=
  PMF.ext fun value => tendsto_nhds_unique (firstLimit value) (secondLimit value)

end GameTheory.Math.Probability
