/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # Play until a stopping set stays in the start's cone

Play until a stopping set reaches only histories that the start reaches
(`Vegas.historyReaches_of_mem_runBehavioralUntil`).
-/

noncomputable section

namespace Vegas

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

section Reach

variable {ι : Type*} [Fintype ι] {E : ExecutionProtocol ι} (M : InformationModel E)

/-- **Play until a stopping set stays in the start's cone.** Every history play
until a stopping set ends at is reached from the start. -/
theorem historyReaches_of_mem_runBehavioralUntil (certificate : E.WellFoundedHistories)
    (policies : (i : ι) → M.BehavioralPolicy i) (stopped : E.History → Prop)
    (start : E.History) :
    ∀ stop ∈ (M.runBehavioralUntil certificate policies stopped start).support,
      E.HistoryReaches start stop := by
  classical
  induction start using certificate.induction with
  | _ history ih =>
  intro stop member
  by_cases halt : stopped history
  · rw [M.runBehavioralUntil_of_stopped certificate policies halt,
      PMF.mem_support_pure_iff] at member
    subst member
    exact HistoryReaches.refl E _
  by_cases ended : E.terminal history.state
  · rw [M.runBehavioralUntil_of_terminal certificate policies ended,
      PMF.mem_support_pure_iff] at member
    subst member
    exact HistoryReaches.refl E _
  rw [M.runBehavioralUntil_of_running certificate policies halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  obtain ⟨successor, reaches⟩ := M.mem_support_runBehavioralFrom_one policies ended nextMember
  exact reaches stop (ih next successor stop reached)

end Reach


end Vegas
