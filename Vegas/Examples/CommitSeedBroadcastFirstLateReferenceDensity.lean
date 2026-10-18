/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialQuietSupport
import Vegas.Examples.CommitSeedBroadcastFirstLateSeedBelief
import Interaction.ReactiveSchedulerSeedTrace

/-! # Cancellation of the original quiet density inside every native information fiber -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every bad history has the exact original quiet density. All other genuine
histories remain in the denominator, including histories with early helpers. -/
theorem firstLate_reference_history_weights
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view))
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = [])
    (history : rawModel.InformationHistory owner site.1) :
    let density := initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile)
    let actual := (rawModel.historyReachWeight profile history.1).toReal
    let reference :=
      (rawModel.historyReachWeight (initialQuietProfile profile) history.1).toReal
    actual * firstLateBadValue history.1.state =
      density * (reference * firstLateBadValue history.1.state) ∧
        density * reference ≤ actual := by
  intro density actual reference
  rcases history with ⟨⟨state, trace⟩, informed⟩
  have physical : app.observe owner state = some (past, view) :=
    (rawMenu.info initial horizon scheduler owner trace).symm.trans (informed.trans observed)
  cases state with
  | none => simp only [ReactiveApplication.observe, reduceCtorEq] at physical
  | some current =>
      have active : current.actor = some owner := by
        by_contra inactive
        simp only [ReactiveApplication.observe, inactive, ite_false] at physical
        cases physical
      rcases current with ⟨remaining, actor, execution⟩
      change actor = some owner at active
      subst actor
      simp only [ReactiveApplication.observe, ite_true] at physical
      have sameView := congrArg Prod.snd (Option.some.inj physical)
      have originalHere : execution.application.attempt = originalAttempt :=
        (congrArg (fun localView : app.PlayerView => localView.application.2.attempt)
          sameView).trans original
      have clockHere : execution.application.current.native.clock = 2 :=
        (congrArg (fun localView : app.PlayerView => localView.application.2.native.clock)
          sameView).trans clock
      have emptyHere : execution.receipts = [] :=
        (congrArg ReactiveApplication.PlayerView.receipts sameView).trans empty
      have rawTrace := rawMenu.toRawTrace initial horizon scheduler trace
      obtain ⟨seed, _prior, ⟨fixed⟩⟩ := app.schedulerMixture_trace_fixed_seed
        nativeSeedLaw family initialState horizon ⟨remaining, some owner, execution⟩ rawTrace
      have placement := original_first_late_input_placement seed
        ⟨remaining, some owner, execution⟩ fixed owner rfl originalHere clockHere
      have late : 5 ≤
          (⟨remaining, some owner, execution⟩ : app.Control).execution.environmentRecall.length :=
        by
        rcases placement with good | bad <;> omega
      have quietDensity (quiet : EmptyEarlySnapshot execution) : actual = density * reference :=
        original_quiet_history_density profile seed remaining execution owner trace fixed late quiet
      refine ⟨?_, ?_⟩
      · by_cases badPosition : 12 ≤ execution.environmentRecall.length
        · have bad : seed.2 owner = false :=
            (original_first_late_bad_iff seed ⟨remaining, some owner, execution⟩ fixed owner
              rfl originalHere clockHere).mpr badPosition
          have quiet := bad_firstLate_empty_receipts_snapshot seed
            ⟨remaining, some owner, execution⟩ fixed owner rfl originalHere clockHere bad emptyHere
          change actual * (if 12 ≤ execution.environmentRecall.length then 1 else 0) =
            density * (reference * (if 12 ≤ execution.environmentRecall.length then 1 else 0))
          rw [ite_eq_left badPosition, mul_one, mul_one]
          exact quietDensity quiet
        · change actual * (if 12 ≤ execution.environmentRecall.length then 1 else 0) =
            density * (reference * (if 12 ≤ execution.environmentRecall.length then 1 else 0))
          rw [ite_eq_right badPosition, mul_zero, mul_zero, mul_zero]
      · by_cases positive : 0 < reference
        · have quiet := positive_initialQuietProfile_snapshot profile seed remaining execution
            owner trace fixed late positive
          exact (quietDensity quiet).ge
        · have zero : reference = 0 := le_antisymm (le_of_not_gt positive) ENNReal.toReal_nonneg
          rw [zero, mul_zero]
          exact ENNReal.toReal_nonneg

/-- The actual unnormalized full-information bad mass is bounded by the same
constant as the quiet reference, even when its initial density tends to zero. -/
theorem firstLate_reference_reach_comparison
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (owner : Player) (site : rawModel.InformationSite owner)
    (past : List app.PlayerEntry) (view : app.PlayerView)
    (observed : site.1 = some (past, view))
    (original : view.application.2.attempt = originalAttempt)
    (clock : view.application.2.native.clock = 2) (empty : view.receipts = []) :
    let density := initialQuietReach (rawMenu.decodeProfile initial horizon scheduler profile)
    (∑ history : rawModel.InformationHistory owner site.1,
      (rawModel.historyReachWeight profile history.1).toReal *
        firstLateBadValue history.1.state) =
      density * ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight (initialQuietProfile profile) history.1).toReal *
          firstLateBadValue history.1.state ∧
    density * (∑ history : rawModel.InformationHistory owner site.1,
      (rawModel.historyReachWeight (initialQuietProfile profile) history.1).toReal) ≤
      ∑ history : rawModel.InformationHistory owner site.1,
        (rawModel.historyReachWeight profile history.1).toReal := by
  intro density
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro history _member
    exact (firstLate_reference_history_weights profile owner site past view observed original
      clock empty history).1
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro history _member
    exact (firstLate_reference_history_weights profile owner site past view observed original
      clock empty history).2

end Vegas.Examples.CommitSeedBroadcast
