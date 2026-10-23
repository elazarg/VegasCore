/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Analysis.Protocol.CounterfactualReach
import GameTheory.Protocol.BehavioralBayes

/-! # The reach weight of one history

The empty history has reach weight one
(`GameTheory.Protocol.InformationModel.historyReachWeight_initHistory`), and the
reach weight of a nonempty history is the reach weight of its predecessor times
the mass of its last step
(`GameTheory.Protocol.InformationModel.historyReachWeight_eq_prior_mul`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open scoped ENNReal

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)
  (strategy : (i : ι) → M.BehavioralPolicy i)

/-- The empty history has weight one. -/
theorem historyReachWeight_initHistory :
    M.historyReachWeight strategy E.initHistory = 1 := by
  simp only [historyReachWeight, runBehavioral, runBehavioralFrom,
    ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length,
    ExecutionProtocol.runRandomizedFor_zero, PMF.pure_apply, ↓reduceIte]

/-- The weight of a nonempty history is the weight of its predecessor times the
mass of its last step. -/
theorem historyReachWeight_eq_prior_mul (history : E.History)
    (positive : 0 < history.trace.length) :
    M.historyReachWeight strategy history =
      M.historyReachWeight strategy history.prior *
        M.runBehavioralFrom strategy 1 history.prior history := by
  have lengths := history.prior_trace_length positive
  unfold historyReachWeight runBehavioral runBehavioralFrom
  rw [← lengths]
  exact E.runRandomizedFor_apply_of_trace_succ _ _ _ _ (by
    simp only [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
    omega)

end GameTheory.Protocol.InformationModel
