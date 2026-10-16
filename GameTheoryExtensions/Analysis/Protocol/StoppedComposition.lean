/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Splitting the existing behavioral law at an earlier stopping set -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {protocol : ExecutionProtocol Player}
  (model : InformationModel protocol)

/-- A later stopped law first reaches the earlier set and then continues with
the same profile and full history. Terminal histories retain their mass. -/
theorem runBehavioralUntil_eq_bind_runBehavioralUntil
    (certificate : protocol.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who)
    (earlier later : protocol.History → Prop)
    (nested : ∀ history, later history → earlier history) (start : protocol.History) :
    model.runBehavioralUntil certificate profile later start =
      (model.runBehavioralUntil certificate profile earlier start).bind
        (model.runBehavioralUntil certificate profile later) := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
    by_cases halted : earlier history
    · rw [model.runBehavioralUntil_of_stopped certificate profile halted, PMF.pure_bind]
    by_cases ended : protocol.terminal history.state
    · rw [model.runBehavioralUntil_of_terminal certificate profile ended,
        model.runBehavioralUntil_of_terminal certificate profile ended, PMF.pure_bind,
        model.runBehavioralUntil_of_terminal certificate profile ended]
    have going : ¬ later history := fun stopped => halted (nested history stopped)
    rw [model.runBehavioralUntil_of_running certificate profile going ended,
      model.runBehavioralUntil_of_running certificate profile halted ended, PMF.bind_bind]
    apply bind_congr_on_support
    intro next supported
    exact ih next (model.mem_support_runBehavioralFrom_one profile ended supported).1

end GameTheory.Protocol.InformationModel
