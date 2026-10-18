/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperWrongTransmission
import Vegas.Examples.CommitSeedBroadcastCurrentChoiceValue

/-! # The exact assessed continuation value of a bad clock-two transmission -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A retained receipted clock-two declaration has the exclusion value under
the original posterior, with the future response kernels unchanged. -/
theorem counted_wrong_helper_record_finish_value
    (remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (material : WitnessedSubmission graph) (sent : entry.action.transmission = some material)
    (clock : entry.beforeView.application.2.native.clock = 2)
    (receipted : entry.beforeView.receipts ≠ [])
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
  obtain ⟨earlier, later, decomposition⟩ := List.mem_iff_append.mp recorded
  have bad := remembered_receipted_firstLate_seed_bad countedMenu seed
    ⟨remaining, none, execution⟩ fixed owner earlier entry later decomposition requested.1.symm
      clock receipted
  rw [← expect_constant (app.finish initial horizon (family seed) players
    (some ⟨remaining, none, execution⟩)) (-(3 / 2 : ℝ))]
  apply expect_congr_on_support
  intro state reached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, PMF.pure_bind] at reached
  obtain ⟨after, continued, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨finalTrace⟩ := countedMenu.trace_runRounds initial horizon (family seed) players covered
    0 remaining execution after (by simpa only [Nat.zero_add] using fixed) continued
  have retained : app.PolicyInvariant players (fun current => entry ∈ current.recall owner) := {
    respond := fun before actor action valid _ =>
      app.respond_recall_mono before actor owner action valid
    environment := fun before next command valid moved => by
      rw [app.environmentStep_recall before next command moved]
      exact valid }
  have kept := retained.runRounds (family seed) remaining execution after recorded continued
  exact bad_clock_two_record_terminal_payoff seed after finalTrace owner bad entry kept requested
    material sent clock

/-- The one forced transmission is followed by the literal incumbent future. -/
theorem counted_wrong_helper_assessed_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : countedProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (clock : execution.application.current.native.clock = 2)
    (receipted : execution.receipts ≠ [])
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈ countedMenu.actions owner
      (execution.recall owner) (execution.observe app owner)) :
    expect (app.finish initial horizon scheduler
      (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
        (fun state => netPayoff state owner) = -(3 / 2) := by
  classical
  obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon scheduler remaining execution
    owner ⟨some material⟩ trace offered
  let next := execution.respond app owner ⟨some material⟩
  let history : countedProtocol.History := ⟨some ⟨remaining, none, next⟩, responded⟩
  have law := counted_assessment_finish_eq assessment equilibrium history
  change app.finish initial horizon scheduler
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      history.state = _ at law
  rw [← law]
  obtain ⟨emitted, recalled⟩ := app.respond_recall_entry execution owner
    (⟨some material⟩ : app.Action)
  let entry : app.PlayerEntry := ⟨execution.observe app owner, ⟨some material⟩, emitted⟩
  have member : entry ∈ next.recall owner := by
    rw [recalled]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have valid := raw_native_valid scheduler ⟨remaining, some owner, execution⟩
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have publicRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) :=
    (execution.application.requests_publicView valid owner (originalCoordinate owner)).mpr request
  exact counted_wrong_helper_record_finish_value remaining next responded owner entry member
    publicRequest material rfl clock receipted
      (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      (fun who past view action supported => countedMenu.decode_embedPolicy_covered
        initial horizon scheduler who (countedAssessmentProfile assessment who)
          past view action supported)

end Vegas.Examples.CommitSeedBroadcast
