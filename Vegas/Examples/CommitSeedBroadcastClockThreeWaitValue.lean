/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalSilentFailure
import Vegas.Examples.CommitSeedBroadcastCurrentChoiceValue

/-! # Exact value of omitting the final original opportunity -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- All original WAIT records give the fixed exclusion value under the actual
original seed posterior, with every foreign preparation and response retained. -/
theorem counted_all_original_waits_finish_value
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩)) (owner : Player)
    (entries : Fin 3 → app.PlayerEntry)
    (recorded : ∀ index, entries index ∈ execution.recall owner)
    (requested : ∀ index, PhaseRuntimeState.requests (entries index).beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : ∀ index, (entries index).action.transmission = none)
    (clocks : ∀ index, (entries index).beforeView.application.2.native.clock =
      ([0, 2, 3] : List Nat)[index.val])
    (players : Player → app.Policy)
    (covered : ∀ who past view action, action ∈ (players who past view).support →
      action ∈ countedMenu.actions who past view) :
    expect (app.finish initial horizon scheduler players
      (some ⟨remaining, none, execution⟩)) (fun state => netPayoff state owner) = -(3 / 2) := by
  have bounded (state : app.ProtocolState) : |netPayoff state owner| ≤ (9 / 2 : ℝ) := by
    have range := netPayoff_mem_Icc state owner
    exact abs_le.mpr ⟨range.1, by linarith [range.2]⟩
  rw [native_finish_original_seed_law, expect_bind_tower_bounded _ _ _ bounded,
    ← expect_constant (implementation.posterior execution.environmentRecall) (-(3 / 2) : ℝ)]
  apply expect_congr_on_support
  intro seed supported
  obtain ⟨_original, ⟨fixed⟩⟩ := menu_original_posterior_trace countedMenu
    ⟨remaining, none, execution⟩ trace seed supported
  exact counted_all_original_waits_fixed_finish_value seed remaining execution fixed owner entries
    recorded requested silent clocks players covered

/-- A literal clock-three WAIT, after the earlier two WAITs, has the fixed
loss under the unchanged raw equilibrium continuation. -/
theorem counted_clock_three_wait_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 3)
    (first second : app.PlayerEntry) (word : execution.recall owner = [first, second])
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (secondRequest : PhaseRuntimeState.requests second.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (secondSilent : second.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (secondClock : second.beforeView.application.2.native.clock = 2) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app owner ⟨none⟩⟩))
        (fun state => netPayoff state owner) = -(3 / 2) := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  let next : app.Execution := execution.respond app owner ⟨none⟩
  let third : app.PlayerEntry := ⟨execution.observe app owner, ⟨none⟩, none⟩
  let entries : Fin 3 → app.PlayerEntry := Fin.cases first (Fin.cases second (fun _ => third))
  let history : countedProtocol.History := ⟨some ⟨remaining, none, next⟩, responded⟩
  have law := counted_assessment_finish_eq assessment equilibrium history
  change app.finish initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      history.state = _ at law
  rw [← law]
  have wordNext : next.recall owner = [first, second, third] := by
    simp only [next, ReactiveApplication.Execution.respond, ite_true]
    change execution.recall owner ++ [third] = _
    rw [word]
    rfl
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have thirdRequest : PhaseRuntimeState.requests third.beforeView.application.2 owner
      (originalCoordinate owner) :=
    (execution.application.requests_publicView valid owner (originalCoordinate owner)).mpr request
  exact counted_all_original_waits_finish_value remaining next responded owner entries
    (by intro index; fin_cases index
        · change first ∈ next.recall owner
          rw [wordNext]
          simp
        · change second ∈ next.recall owner
          rw [wordNext]
          simp
        · change third ∈ next.recall owner
          rw [wordNext]
          simp)
    (by intro index; fin_cases index
        · exact firstRequest
        · exact secondRequest
        · exact thirdRequest)
    (by intro index; fin_cases index
        · exact firstSilent
        · exact secondSilent
        · rfl)
    (by intro index; fin_cases index
        · exact firstClock
        · exact secondClock
        · exact clock)
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
    (fun who past view action supported => countedMenu.decode_embedPolicy_covered
      initial horizon scheduler who (countedAssessmentProfile assessment who)
        past view action supported)

end Vegas.Examples.CommitSeedBroadcast
