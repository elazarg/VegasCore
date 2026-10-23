/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # History invariants of the existing stopped behavioral law -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type*} [Fintype Player] {protocol : ExecutionProtocol Player}
  (model : InformationModel protocol)

/-- A property of full histories preserved by actual supported steps remains
true at every stopped endpoint. No state-only representation is required. -/
theorem runBehavioralUntil_support_history_closed
    (certificate : protocol.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who) (stopped : protocol.History → Prop)
    (property : protocol.History → Prop)
    (preserved : ∀ history, ¬ stopped history → ¬ protocol.terminal history.state →
      property history → ∀ next ∈ (model.runBehavioralFrom profile 1 history).support,
        property next)
    (start : protocol.History) (holds : property start) :
    ∀ final ∈ (model.runBehavioralUntil certificate profile stopped start).support,
      property final := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro final member
  by_cases halt : stopped history
  · rw [model.runBehavioralUntil_of_stopped certificate profile halt,
      PMF.mem_support_pure_iff] at member
    exact member ▸ holds
  by_cases ended : protocol.terminal history.state
  · rw [model.runBehavioralUntil_of_terminal certificate profile ended,
      PMF.mem_support_pure_iff] at member
    exact member ▸ holds
  rw [model.runBehavioralUntil_of_running certificate profile halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, supported, reached⟩ := member
  exact ih next (model.mem_support_runBehavioralFrom_one profile ended supported).1
    (preserved history halt ended holds next supported) final reached

end GameTheory.Protocol.InformationModel
