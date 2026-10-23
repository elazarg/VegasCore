/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryPayoff
import Vegas.Game.CommitRecoveryVoluntaryFailurePayoff

/-! # Checkpointed own debt forces the actual exclusion payoff under every continuation -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- Once current-block debt is checkpointed, even arbitrary foreign policies at
new information and all later resets lead to the actual permanent-exclusion floor. -/
theorem proposalRecovery_terminal_payoff_of_checkpointed_debt
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (history : setup.proposalRecoveryProtocol.History)
    (current : CommitRecoveryState setup.program) (equality : history.state = some current)
    (owed : who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point))
    (last : setup.proposalRecoveryProtocol.History)
    (supported : last ∈ (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile history).support) :
    setup.proposalRecoveryPayoff utility excludedPayoff who last = excludedPayoff who := by
  let closed : setup.proposalRecoveryProtocol.State → Prop := fun state =>
    ∃ current, state = some current ∧ (who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point))
  have retained := setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_closed
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile closed
    (fun state joint legal next holds reached => by
      obtain ⟨before, rfl, debt⟩ := holds
      obtain ⟨after, raw, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
      exact ⟨after, rfl, before.step_preserves_excluded_or_owesFailure who debt
        (proposalRecoveryJoint joint) after raw⟩)
    history ⟨current, equality, owed⟩ last supported
  obtain ⟨after, afterEquality, debt⟩ := retained
  have stopped := setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories profile history last supported
  have excluded : who ∈ after.excluded := by
    rcases debt with excluded | debt
    · exact excluded
    · exact setup.commitRecovery_terminal_excluded_of_owesFailure
        (setup.proposalRecoveryEraseTrace last.trace) after afterEquality
        who debt.2 (by
          simpa only [afterEquality, proposalRecoveryProtocol, commitRecoveryProtocol,
            Option.elim_some] using stopped)
  change setup.commitRecoveryPayoff utility excludedPayoff who
    ⟨last.state, setup.proposalRecoveryEraseTrace last.trace⟩ = _
  apply setup.commitRecoveryPayoff_of_excluded
  simpa only [afterEquality, commitRecoveryPublic, Option.elim_some] using excluded

omit [Fintype Player] in
/-- The weak exclusion floor bounds every actual enriched terminal payoff;
no assumption about unobserved failed proposal values is used. -/
theorem proposalRecovery_terminal_payoff_lower
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (who : Player) (final : setup.proposalRecoveryProtocol.History)
    (terminal : setup.proposalRecoveryProtocol.terminal final.state) :
    excludedPayoff who ≤ setup.proposalRecoveryPayoff utility excludedPayoff who final := by
  exact setup.commitRecovery_terminal_payoff_lower utility excludedPayoff below who
    ⟨final.state, setup.proposalRecoveryEraseTrace final.trace⟩ terminal

open Classical in
/-- The weak floor bounds EVERY continuation at an original enriched
information site, with its actual assessment belief and arbitrary policies. -/
theorem proposalRecovery_conditional_value_lower
    [Finite setup.proposalRecoveryProtocol.History]
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (focal : Player) (site : setup.proposalRecoveryModel.InformationSite focal)
    (policy : setup.proposalRecoveryModel.BehavioralPolicy focal) :
    excludedPayoff focal ≤
      (assessment.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
        site (setup.proposalRecoveryPayoff utility excludedPayoff focal)).value policy := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  let law := (assessment.belief focal site).bind fun history =>
    setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (GameTheory.Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
        assessment.strategy focal policy) history.1
  change excludedPayoff focal ≤ expect law _
  rw [← expect_constant law (excludedPayoff focal)]
  apply expect_mono _ (payoffIntegrable_constant _ _) (payoffIntegrable_of_finite _ _)
  intro final supported
  obtain ⟨history, _supported, child⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  exact setup.proposalRecovery_terminal_payoff_lower utility excludedPayoff below focal final
    (setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories _ history.1 final child)

end Vegas.SourceProgram.Setup
