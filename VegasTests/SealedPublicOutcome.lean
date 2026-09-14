/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPublicOutcome
import VegasTests.PendingStages

/-! # Public sealed-outcome reconstruction regression -/

noncomputable section

namespace VegasTests.SealedPublicOutcome

open Vegas Vegas.EventGraph Interaction PendingStages

/-- Replaying the actual four-stage transcript loads both public reveal fields
without reading either accepted commitment handle. -/
theorem public_store_loads_openings (first second : Value) :
    let events :=
      (program.run (SealedProgram.State.empty PendingStages.Player Value)
        (actions first second)).events
    Store.getAs (graph.publicSealedStore (.option .bool) events) 1 (.option .bool) =
        some first ∧
      Store.getAs (graph.publicSealedStore (.option .bool) events) 3 (.option .bool) =
        some second := by
  have htarget1 : graph.nodeTarget 1 = 1 := by decide
  have htarget3 : graph.nodeTarget 3 = 3 := by decide
  rw [run_events]
  constructor <;>
    simp [Graph.publicSealedStore, Graph.replayPublicOpenings, Store.getAs, Store.set,
      TypedValue.as?, htarget1, htarget3]

end VegasTests.SealedPublicOutcome
