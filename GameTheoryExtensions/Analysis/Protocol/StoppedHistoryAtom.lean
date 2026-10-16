/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Exact atoms at the first stopped history -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type*} [Fintype Player] {E : ExecutionProtocol Player}
  (model : InformationModel E)

omit [Fintype Player] in
private theorem reached_prefix {fuel : Nat} {start final : E.History}
    (reached : E.ReachesWithin fuel start final) : TracePrefix start.trace final.trace := by
  induction reached with
  | refl => exact .refl
  | step joint legal realized rest ih =>
      exact (TracePrefix.extend (.refl) joint legal realized).trans ih

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
  have earlier := reached_prefix
    (model.runBehavioralFrom_reachesWithin profile 1 current next supported)
  exact earlier.trans
    (ih next step.1 final reached)
/-- At a genuine first stopped endpoint, the stopped atom is the original
finite-depth continuation atom. Earlier stopping is excluded along the ACTUAL
history prefixes, rather than by an assumed kernel or mass identity. -/
theorem runBehavioralUntil_apply_of_first_hit
    (certificate : E.WellFoundedHistories)
    (profile : ∀ who, model.BehavioralPolicy who) (stopped : E.History → Prop)
    (start final : E.History) (isPrefix : TracePrefix start.trace final.trace)
    (halt : stopped final ∨ E.terminal final.state)
    (first : ∀ middle : E.History, TracePrefix start.trace middle.trace →
      TracePrefix middle.trace final.trace → middle.trace.length < final.trace.length →
        ¬ stopped middle) :
    model.runBehavioralUntil certificate profile stopped start final =
      model.runBehavioralFrom profile (final.trace.length - start.trace.length) start final := by
  classical
  generalize depth : final.trace.length - start.trace.length = fuel
  induction fuel generalizing start final with
  | zero =>
      have same := isPrefix.eq_of_length (by have := isPrefix.length_le; omega)
      have sameHistory : start = final := same
      subst final
      rcases halt with stoppedHere | terminalHere
      · rw [model.runBehavioralUntil_of_stopped certificate profile stoppedHere]
        rfl
      · rw [model.runBehavioralUntil_of_terminal certificate profile terminalHere]
        rfl
  | succ fuel ih =>
      have longer : start.trace.length < final.trace.length := by
        have := isPrefix.length_le
        omega
      have going : ¬ stopped start := first start .refl isPrefix longer
      have running : ¬ E.terminal start.state := by
        intro terminal
        have same := isPrefix.reachesWithin.eq_of_terminal terminal
        have lengths := congrArg (fun history : E.History => history.trace.length) same
        change final.trace.length = start.trace.length at lengths
        omega
      rw [model.runBehavioralUntil_of_running certificate profile going running]
      rw [show fuel + 1 = 1 + fuel by omega, model.runBehavioralFrom_add]
      rw [PMF.bind_apply, PMF.bind_apply]
      apply tsum_congr
      intro next
      by_cases supported : next ∈ (model.runBehavioralFrom profile 1 start).support
      · have step := model.runBehavioralFrom_reachesWithin profile 1 start next supported
        have before : TracePrefix start.trace next.trace := reached_prefix step
        have nextLength : next.trace.length = start.trace.length + 1 := by
          exact model.length_of_mem_support_runBehavioralFrom_one profile running supported
        by_cases reaches : TracePrefix next.trace final.trace
        · have remaining : final.trace.length - next.trace.length = fuel := by omega
          have noEarlier (middle : E.History) (after : TracePrefix next.trace middle.trace)
              (prior : TracePrefix middle.trace final.trace)
              (shorter : middle.trace.length < final.trace.length) : ¬ stopped middle :=
            first middle (before.trans after) prior shorter
          rw [ih next final reaches halt noEarlier remaining]
        · have stoppedZero :
              model.runBehavioralUntil certificate profile stopped next final = 0 := by
            apply (PMF.apply_eq_zero_iff _ _).mpr
            intro member
            exact reaches (model.runBehavioralUntil_support_prefix certificate profile stopped
              next final member)
          have finiteZero : model.runBehavioralFrom profile fuel next final = 0 := by
            apply (PMF.apply_eq_zero_iff _ _).mpr
            intro member
            exact reaches (reached_prefix (model.runBehavioralFrom_reachesWithin profile fuel
              next final member))
          rw [stoppedZero, finiteZero]
      · have zero := (PMF.apply_eq_zero_iff _ _).mpr supported
        rw [zero, zero_mul, zero_mul]

end GameTheory.Protocol.InformationModel
