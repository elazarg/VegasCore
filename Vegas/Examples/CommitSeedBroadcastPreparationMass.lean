/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationForecast
import Vegas.Examples.CommitSeedBroadcastCountedInformation
import Vegas.Examples.CommitSeedBroadcastPosteriorTrace

/-! # Strict preparation mass in the original native information belief -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The original remaining seed posterior gives at least the regular-prefix
mass to the fixed-loss preparation improvement mark. -/
theorem counted_preparation_advantage_regular_lower
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = []) :
    (3 / 2 : ℝ) * regularFirstLateValue (some ⟨remaining, some owner, execution⟩) ≤
      preparationAdvantageValue (some ⟨remaining, some owner, execution⟩) owner := by
  classical
  unfold preparationAdvantageValue regularFirstLateValue
  rw [← expect_const_mul]
  apply expect_mono ?_ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  intro seed supported
  change seed ∈ (implementation.posterior execution.environmentRecall).support at supported
  obtain ⟨_supported, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, some owner, execution⟩ trace seed supported
  by_cases regular : regularFirstLateControl seed (some ⟨remaining, some owner, execution⟩)
  · rw [regular_clock_two_preparation_mark seed remaining execution owner fixed request clock
      empty regular]
    simp only [regular, ite_true, mul_one, le_refl]
  · simp only [regular, ite_false, mul_zero]
    change 0 ≤ if seed.2 owner = true ∧
      ∀ other, other ≠ owner → originalReceiptForecast seed execution other then
        (3 / 2 : ℝ) else 0
    split <;> norm_num

/-- The positive bound is inside the actual native information fiber. It uses
the original conditional seed posterior at every history and no reach floor. -/
theorem assessed_preparation_advantage_lower
    (assessment : rawModel.BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (rawMenu.decisionInformationAntichain initial horizon scheduler))
    (source : countedProtocol.History) (remaining : Nat) (execution : app.Execution)
    (owner : Player) (current : source.state = some ⟨remaining, some owner, execution⟩)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (site : rawModel.InformationSite owner)
    (atSite : site.1 = countedModel.infoOf owner source.trace) :
    (1 / 32 : ℝ) ≤ expect (assessment.belief owner site)
      (fun history => preparationAdvantageValue history.1.state owner) := by
  classical
  have sourceTrace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩) :=
    current ▸ source.trace
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler sourceTrace)
  have publicSource := (execution.application.requests_publicView valid owner
    (originalCoordinate owner)).mpr request
  have fiber (target : rawModel.InformationHistory owner site.1) :
      (3 / 2 : ℝ) * regularFirstLateValue target.1.state ≤
        preparationAdvantageValue target.1.state owner := by
    let sameInput : rawModel.InformationHistory owner (countedModel.infoOf owner source.trace) :=
      ⟨target.1, target.2.trans atSite⟩
    obtain ⟨count, next, state, ⟨countedTrace⟩, _recalled, observed⟩ :=
      counted_information_raw_fiber_control source remaining execution owner current sameInput
    have nextValid := raw_native_valid scheduler ⟨count, some owner, next⟩
      (countedMenu.toRawTrace initial horizon scheduler countedTrace)
    have publicNext : PhaseRuntimeState.requests next.application.publicView owner
        (originalCoordinate owner) := by
      change PhaseRuntimeState.requests (next.observe app owner).application.2 owner _
      rw [observed]
      exact publicSource
    have requestNext := (next.application.requests_publicView nextValid owner
      (originalCoordinate owner)).mp publicNext
    have clockNext : next.application.current.native.clock = 2 := by
      change (next.observe app owner).application.2.native.clock = 2
      rw [observed]
      exact clock
    have emptyNext : next.receipts = [] := by
      change (next.observe app owner).receipts = []
      rw [observed]
      exact empty
    rw [state]
    exact counted_preparation_advantage_regular_lower count next owner countedTrace requestNext
      clockNext emptyNext
  have integrated := expect_mono (μ := assessment.belief owner site) (fun target _ => fiber target)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  rw [expect_const_mul] at integrated
  have observedSite : site.1 = some (execution.recall owner, execution.observe app owner) := by
    rw [atSite]
    change (countedMenu.signals initial horizon scheduler).infoOf owner source.trace = _
    rw [countedMenu.info, current]
    simp only [ReactiveApplication.observe, ite_true]
  have lower := assessed_firstLate_regular_lower assessment consistent owner site
    (execution.recall owner) (execution.observe app owner) observedSite request.1.symm clock empty
  nlinarith

end Vegas.Examples.CommitSeedBroadcast
