/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Source.ProposalRecoveryVoluntaryFailure
import Vegas.Game.ProposalRecoveryDebtPayoff

/-! # Fixed exclusion value for voluntary source recovery failure -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

theorem proposalRecovery_voluntaryFailure_payoff
    [∀ who, DecidableEq (setup.proposalRecoveryModel.InfoState who)]
    (profile : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (fails : ¬ setup.CommitRecoveryContinues who
      (setup.proposalRecoveryEraseInfo who site.1) (choice.1.map (·.semantic)))
    (history : setup.proposalRecoveryModel.InformationHistory who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈ (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) profile who
        ((profile who).commit site.1 choice)) history.1).support) :
    setup.proposalRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  let model := setup.proposalRecoveryModel
  let policies := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit site.1 choice)
  have active := InformationModel.InformationSite.active (M := model) site history
  have running : ¬ setup.proposalRecoveryProtocol.terminal history.1.state := by
    intro terminal
    cases state : history.1.state with
    | none => rw [state] at active; exact active.elim
    | some current =>
        rw [state] at active terminal
        have inactive := ProtocolState.terminal_actor_none who setup.program current.point terminal
        rw [ProtocolState.actor_observe_eq, active.1] at inactive
        cases inactive
  change final ∈ (model.runBehavioralTerminalFrom
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories policies history.1).support
    at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨target, reached, child⟩ := continued
  have chosen : draw.1 who = choice.1 := by
    have marginal : draw.1 ∈ ((model.behavioralJoint policies history.1.trace running).map
        Subtype.val).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [model.behavioralJoint_map_val, independentProduct_support_iff] at marginal
    have own := marginal who
    rw [history.2] at own
    simpa only [policies, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map, PMF.mem_support_pure_iff] using own
  let actualChoice : model.Choice who (model.infoOf who history.1.trace) :=
    ⟨choice.1, by rw [history.2]; exact choice.2⟩
  have actualFails : ¬ setup.CommitRecoveryContinues who
      (setup.proposalRecoveryEraseInfo who (model.infoOf who history.1.trace))
        (actualChoice.1.map (·.semantic)) := by
    change ¬ setup.CommitRecoveryContinues who
      (setup.proposalRecoveryEraseInfo who (setup.proposalRecoveryModel.infoOf who history.1.trace))
        (choice.1.map (·.semantic))
    rw [history.2]
    exact fails
  have excluded := setup.proposalRecovery_voluntaryFailure_step who history.1.trace actualChoice
    actualFails draw.1 draw.2 chosen target reached
  cases state : target with
  | none =>
      simp only [state, commitRecoveryPublic, Finset.notMem_empty] at excluded
  | some current =>
      have member : who ∈ current.excluded := by
        simpa only [state, commitRecoveryPublic] using excluded
      exact setup.proposalRecovery_terminal_payoff_of_checkpointed_debt utility excludedPayoff who
        policies (history.1.extend draw.2 reached) current state (Or.inl member) final child

theorem proposalRecovery_voluntaryFailure_context_value
    [∀ who, DecidableEq (setup.proposalRecoveryModel.InfoState who)]
    (assessment : setup.proposalRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.proposalRecoveryModel.InformationSite who)
    (choice : setup.proposalRecoveryModel.Choice who site.1)
    (fails : ¬ setup.CommitRecoveryContinues who
      (setup.proposalRecoveryEraseInfo who site.1) (choice.1.map (·.semantic)))
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    (assessment.continuationContext setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      site (setup.proposalRecoveryPayoff utility excludedPayoff who)).value
      ((assessment.strategy who).commit site.1 choice) = excludedPayoff who := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  let continuation := (assessment.belief who site).bind fun history =>
    setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature)
        assessment.strategy who
        ((assessment.strategy who).commit site.1 choice)) history.1
  change expect continuation _ = excludedPayoff who
  calc
    _ = expect continuation (fun _ => excludedPayoff who) := by
      apply expect_congr_on_support
      intro final supported
      change final ∈ ((assessment.belief who site).bind _).support at supported
      rw [PMF.support_bind] at supported
      obtain ⟨history, _supported, child⟩ := Set.mem_iUnion₂.mp supported
      exact setup.proposalRecovery_voluntaryFailure_payoff assessment.strategy who site choice
        fails history utility excludedPayoff final child
    _ = _ := expect_constant _ _

end Vegas.SourceProgram.Setup
