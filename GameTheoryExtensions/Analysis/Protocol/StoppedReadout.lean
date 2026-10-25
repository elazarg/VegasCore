/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Terminal readouts stable after an earlier stopping time -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type*} [Fintype Player] {protocol : ExecutionProtocol Player}
  (model : InformationModel protocol)

/-- A readout frozen after the chosen stop has the same terminal and stopped law. -/
theorem runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    (certificate : protocol.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who) (stopped : protocol.History → Prop)
    {Outcome : Type*} (read : protocol.History → Outcome)
    (stable : ∀ history, stopped history →
      ∀ final ∈ (model.runBehavioralTerminalFrom certificate profile history).support,
        read final = read history)
    (start : protocol.History) :
    (model.runBehavioralTerminalFrom certificate profile start).map read =
      (model.runBehavioralUntil certificate profile stopped start).map read := by
  rw [model.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate profile stopped start,
    PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support
  intro history supported
  rcases model.mem_support_runBehavioralUntil certificate profile stopped start history supported
      with halted | terminal
  · exact (map_congr_on_support _ (fun final member => stable history halted final member)).trans
      (PMF.map_const _ _)
  · simp only [runBehavioralTerminalFrom, protocol.randomizedBackwardLaw_of_terminal terminal,
      PMF.pure_map, Function.comp_apply]

end GameTheory.Protocol.InformationModel
