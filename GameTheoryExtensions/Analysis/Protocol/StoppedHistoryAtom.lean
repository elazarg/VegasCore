/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Exact atoms at the first stopped history -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (model : InformationModel E)

/-- The existing stopped evaluator reaches only genuine extensions of its full
starting history, including all old actions and observations. -/
theorem runBehavioralUntil_support_prefix
    (certificate : E.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who) (stopped : E.History → Prop)
    (start : E.History) :
    ∀ final ∈ (model.runBehavioralUntil certificate profile stopped start).support,
      TracePrefix start.trace final.trace := by
  classical
  induction start using certificate.induction with
  | _ current ih =>
  intro final member
  by_cases halt : stopped current
  · rw [model.runBehavioralUntil_of_stopped certificate profile halt,
      PMF.mem_support_pure_iff] at member
    subst final
    exact .refl
  by_cases ended : E.terminal current.state
  · rw [model.runBehavioralUntil_of_terminal certificate profile ended,
      PMF.mem_support_pure_iff] at member
    subst final
    exact .refl
  rw [model.runBehavioralUntil_of_running certificate profile halt ended,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, supported, reached⟩ := member
  have step := model.mem_support_runBehavioralFrom_one profile ended supported
  have earlier := ReachesWithin.tracePrefix
    (model.runBehavioralFrom_reachesWithin profile 1 current next supported)
  exact earlier.trans
    (ih next step.1 final reached)
/-- A supported stopped endpoint has no earlier stopping prefix along its
actual continuation. Terminal and immediately stopped starts are retained. -/
theorem runBehavioralUntil_support_first
    (certificate : E.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who) (stopped : E.History → Prop)
    (start : E.History) :
    ∀ final ∈ (model.runBehavioralUntil certificate profile stopped start).support,
      ∀ middle : E.History, TracePrefix start.trace middle.trace →
        TracePrefix middle.trace final.trace → middle.trace.length < final.trace.length →
          ¬ stopped middle := by
  classical
  induction start using certificate.induction with
  | _ current ih =>
  intro final member middle after before shorter
  by_cases halt : stopped current
  · rw [model.runBehavioralUntil_of_stopped certificate profile halt,
      PMF.mem_support_pure_iff] at member
    subst final
    have lower := after.length_le
    omega
  by_cases terminal : E.terminal current.state
  · rw [model.runBehavioralUntil_of_terminal certificate profile terminal,
      PMF.mem_support_pure_iff] at member
    subst final
    have lower := after.length_le
    omega
  rw [model.runBehavioralUntil_of_running certificate profile halt terminal,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, supported, reached⟩ := member
  have step := model.mem_support_runBehavioralFrom_one profile terminal supported
  have nextLength := model.length_of_mem_support_runBehavioralFrom_one profile terminal supported
  by_cases length : middle.trace.length < next.trace.length
  · have lower := after.length_le
    have same := after.eq_of_length (by omega)
    have sameHistory : current = middle := same
    cases sameHistory
    exact halt
  · have nextPrefix := model.runBehavioralUntil_support_prefix certificate profile stopped
      next final reached
    have middlePrefix := (nextPrefix.reachesWithin.ancestor_comparable before.reachesWithin
      (Nat.le_of_not_gt length))
    exact ih next step.1 final reached middle middlePrefix.tracePrefix before shorter

end GameTheory.Protocol.InformationModel
