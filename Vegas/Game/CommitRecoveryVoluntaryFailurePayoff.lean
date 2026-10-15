/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryVoluntaryFailure
import Vegas.Game.CommitRecoveryDebtPayoff

/-! # Fixed exclusion value for voluntary source recovery failure -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

theorem commitRecovery_voluntaryFailure_payoff
    [∀ who, DecidableEq (setup.commitRecoveryModel.InfoState who)]
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
    (choice : setup.commitRecoveryModel.Choice who site.1)
    (fails : ¬ setup.CommitRecoveryContinues who site.1 choice.1)
    (history : setup.commitRecoveryModel.InformationHistory who site.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) profile who
        ((profile who).commit site.1 choice)) history.1).support) :
    setup.commitRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  let model := setup.commitRecoveryModel
  let policies := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit site.1 choice)
  have active := InformationModel.InformationSite.active (M := model) site history
  have running : ¬ setup.commitRecoveryProtocol.terminal history.1.state := by
    intro terminal
    cases state : history.1.state with
    | none => rw [state] at active; exact active.elim
    | some current =>
        rw [state] at active terminal
        have inactive := ProtocolState.terminal_actor_none who setup.program current.point terminal
        rw [ProtocolState.actor_observe_eq, active.1] at inactive
        cases inactive
  change final ∈ (model.runBehavioralTerminalFrom
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories policies history.1).support
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
  have actualFails : ¬ setup.CommitRecoveryContinues who (model.infoOf who history.1.trace)
      actualChoice.1 := by
    change ¬ setup.CommitRecoveryContinues who
      (setup.commitRecoveryModel.infoOf who history.1.trace) choice.1
    rw [history.2]
    exact fails
  have excluded := setup.commitRecovery_voluntaryFailure_step who history.1.trace actualChoice
    actualFails draw.1 draw.2 chosen target reached
  cases state : target with
  | none =>
      simp only [state, commitRecoveryPublic, Finset.notMem_empty] at excluded
  | some current =>
      have member : who ∈ current.excluded := by
        simpa only [state, commitRecoveryPublic] using excluded
      exact setup.commitRecovery_terminal_payoff_of_checkpointed_debt utility excludedPayoff who
        policies (history.1.extend draw.2 reached) current state (Or.inl member) final child

theorem commitRecovery_voluntaryFailure_context_value
    [∀ who, DecidableEq (setup.commitRecoveryModel.InfoState who)]
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
    (choice : setup.commitRecoveryModel.Choice who site.1)
    (fails : ¬ setup.CommitRecoveryContinues who site.1 choice.1)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ) :
    (assessment.continuationContext setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      site (setup.commitRecoveryPayoff utility excludedPayoff who)).value
      ((assessment.strategy who).commit site.1 choice) = excludedPayoff who := by
  rw [InformationModel.BehavioralAssessment.continuationContext_value]
  let continuation := (assessment.belief who site).bind fun history =>
    setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) assessment.strategy who
        ((assessment.strategy who).commit site.1 choice)) history.1
  change expect continuation _ = excludedPayoff who
  calc
    _ = expect continuation (fun _ => excludedPayoff who) := by
      apply expect_congr_on_support
      intro final supported
      change final ∈ ((assessment.belief who site).bind _).support at supported
      rw [PMF.support_bind] at supported
      obtain ⟨history, _supported, child⟩ := Set.mem_iUnion₂.mp supported
      exact setup.commitRecovery_voluntaryFailure_payoff assessment.strategy who site choice
        fails history utility excludedPayoff final child
    _ = _ := expect_constant _ _

omit [Fintype Player] in
theorem commitRecovery_terminal_payoff_lower
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (below : ∀ terminal who, excludedPayoff who ≤ utility terminal who)
    (who : Player) (final : setup.commitRecoveryProtocol.History)
    (terminal : setup.commitRecoveryProtocol.terminal final.state) :
    excludedPayoff who ≤ setup.commitRecoveryPayoff utility excludedPayoff who final := by
  cases state : final.state with
  | none => rw [state] at terminal; exact terminal.elim
  | some current =>
      rw [state] at terminal
      obtain ⟨value, read⟩ := ProtocolState.exists_readout_of_terminal setup.program current.point
        terminal
      unfold commitRecoveryPayoff
      split
      · exact le_rfl
      · simpa only [state, commitRecoverySourceState, Option.map_some, protocolReadout,
          Option.bind_some, read, Option.elim_some] using below value who

end Vegas.SourceProgram.Setup
