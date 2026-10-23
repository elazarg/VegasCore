/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.Execution

/-! # Retained semantic outputs through physical settlement -/

noncomputable section
namespace Vegas.EventGraph.Config
open GameTheory.Math.Probability
variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- The semantic frontier has retained every output already physically settled. -/
def CompletedOutputAgreement (physical frontier : graph.Config) : Prop :=
  ∀ event ∈ physical.cut.completed, physical.outputs event = frontier.outputs event

theorem CompletedOutputAgreement.completed_subset
    (physical frontier : graph.Config)
    (agreement : physical.CompletedOutputAgreement frontier) :
    physical.cut.completed ⊆ frontier.cut.completed := by
  intro event completed
  apply (frontier.output_available event).mp
  rw [← agreement event completed]
  exact (physical.output_available event).mpr completed

end Vegas.EventGraph.Config
