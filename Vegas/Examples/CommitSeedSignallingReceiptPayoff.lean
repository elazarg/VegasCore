/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingInitializedPayoff
import Vegas.Examples.CommitSeedSignallingPublicationReceipts

/-! # Native payoff bounds from missing original binding receipts -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Every actual initialized raw run completes the native graph by the fixed
horizon, independently of player response policies. -/
theorem initialized_raw_native_terminal (players : Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon initialExecution).support) :
    final.application.current.native.config.cut.Terminal := by
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom initial horizon scheduler players horizon le_rfl final
    (by simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
      initialExecution] using reached)
  have trace : (app.protocol initial horizon scheduler).Trace (some ⟨0, none, final⟩) := by
    simpa only [Nat.sub_self] using trace
  exact scheduler_completesPlay ⟨0, none, final⟩ trace ⟨rfl, rfl⟩

/-- A surviving owner receives the full reward whenever the other owner's
original binding never landed. The actual terminal publication readout, rather
than a presumed relation between exclusion and failure, supplies this bound. -/
theorem initialized_counted_netPayoff_receipt_lower_bound
    (profile : ∀ who, countedModel.BehavioralPolicy who) (owner : Player) :
    let law := app.runRounds scheduler
      (countedMenu.decodeProfile initial horizon scheduler profile) horizon initialExecution
    3 * (law.toOuterMeasure {final | owner ∉ final.application.current.excluded ∧
        ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate (opponent owner))
          (opponent owner) final}).toReal -
      (law.toOuterMeasure {final | owner ∈ final.application.current.excluded}).toReal ≤
        expect law (fun final => netPayoff (app.finished final) owner) := by
  classical
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  let law := app.runRounds scheduler players horizon initialExecution
  let missing : Set app.Execution := {final | owner ∉ final.application.current.excluded ∧
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate (opponent owner))
      (opponent owner) final}
  let reward : Set app.Execution := {final | owner ∉ final.application.current.excluded ∧
    RecoveryState.publicationFailed final.application.current.native
      (revealEvent (opponent owner)) = true}
  have contained (final : app.Execution) (reached : final ∈ law.support)
      (member : final ∈ missing) : final ∈ reward := by
    exact ⟨member.1, initialized_missing_original_binding_publication_failed players final reached
      (initialized_raw_native_terminal players final reached) (opponent owner) member.2⟩
  have lower : expect law (fun final => @ite ℝ (final ∈ missing)
      (Classical.propDecidable _) 1 0) ≤
        expect law (fun final => @ite ℝ (final ∈ reward)
          (Classical.propDecidable _) 1 0) := by
    apply expect_mono
    · intro final reached
      by_cases member : final ∈ missing
      · simp only [member, contained final reached member, ite_true, le_refl]
      · simp only [member, ite_false]
        split_ifs <;> norm_num
    · exact payoffIntegrable_ite_one_zero law _
    · exact payoffIntegrable_ite_one_zero law _
  rw [expect_indicator law missing, expect_indicator law reward] at lower
  have formula := initialized_counted_netPayoff_expectation profile owner
  dsimp only at formula
  dsimp only [law, players, reward, missing] at lower ⊢
  rw [formula]
  linarith

end Vegas.Examples.CommitSeedSignalling
