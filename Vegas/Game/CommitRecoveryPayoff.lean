/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryRestriction
import Vegas.Game.CommitRecoveryReference

/-! # Exact intended readout and permanent-exclusion payoff laws in source recovery -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- Permanent runtime exclusion determines the floor. An accepted unusable
binding alone is latent and does not replace utility before an actual failure. -/
def commitRecoveryPayoff
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.commitRecoveryProtocol.History) : ℝ :=
  if who ∈ (setup.commitRecoveryPublic history.state).1 then excludedPayoff who else
    (setup.protocolReadout (setup.commitRecoverySourceState history.state)).elim 0
      (fun terminal => utility terminal who)

theorem commitRecoveryPayoff_of_excluded
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.commitRecoveryProtocol.History)
    (excluded : who ∈ (setup.commitRecoveryPublic history.state).1) :
    setup.commitRecoveryPayoff utility excludedPayoff who history = excludedPayoff who := by
  simp only [commitRecoveryPayoff, ite_eq_left excluded]

theorem commitRecoveryPayoff_of_clear
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.commitRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state) :
    setup.commitRecoveryPayoff utility excludedPayoff who history =
      (setup.protocolReadout (setup.commitRecoverySourceState history.state)).elim 0
        (fun terminal => utility terminal who) := by
  have empty : (setup.commitRecoveryPublic history.state).1 = ∅ := by
    cases current : history.state with
    | none => rfl
    | some current =>
        simpa only [current, CommitRecoveryClear, commitRecoveryPublic, Option.elim_some]
          using clear
  simp only [commitRecoveryPayoff, empty, Finset.notMem_empty, ↓reduceIte]

theorem commitRecoveryPayoff_lift (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (who : Player) (history : setup.intendedProtocol.History) :
    setup.commitRecoveryPayoff utility excludedPayoff who
        (setup.commitRecoveryLiftHistory wellFormed history) =
      (setup.protocolReadout history.state).elim 0 (fun terminal => utility terminal who) := by
  rw [setup.commitRecoveryPayoff_of_clear utility excludedPayoff who _
    (setup.commitRecoveryLiftHistory_clear wellFormed history),
    setup.commitRecoveryLiftHistory_source]

theorem commitRecoveryPayoff_mem_Icc
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (lower upper : Player → ℝ)
    (bounds : ∀ terminal who, utility terminal who ∈ Set.Icc (lower who) (upper who))
    (who : Player) (history : setup.commitRecoveryProtocol.History) :
    setup.commitRecoveryPayoff utility excludedPayoff who history ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) := by
  unfold commitRecoveryPayoff
  split
  · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩
  · cases setup.protocolReadout (setup.commitRecoverySourceState history.state) with
    | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
    | some terminal =>
        exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (bounds terminal who).1),
          (bounds terminal who).2.trans ((le_max_right _ _).trans (le_max_right _ _))⟩

/-- Every profile extending intended play has the exact joint typed-readout
and realized payoff-vector law. The original private initialization remains in
the readout, so arbitrary exogenous parameters can be read jointly afterwards. -/
theorem commitRecovery_initialized_joint [Fintype Player] (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (agrees : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (fuel : Nat) :
    (setup.intendedModel.runBehavioral source fuel).map
        (fun history => (setup.protocolReadout history.state,
          fun who => (setup.protocolReadout history.state).elim 0
            (fun terminal => utility terminal who))) =
      (setup.commitRecoveryModel.runBehavioral target fuel).map
        (fun history => (setup.protocolReadout (setup.commitRecoverySourceState history.state),
          fun who => setup.commitRecoveryPayoff utility excludedPayoff who history)) := by
  have law := (setup.commitRecoveryRestriction wellFormed).initialized_law source target agrees fuel
  have projected := congrArg (PMF.map (fun history : setup.commitRecoveryProtocol.History =>
    (setup.protocolReadout (setup.commitRecoverySourceState history.state),
      fun who => setup.commitRecoveryPayoff utility excludedPayoff who history))) law
  simpa only [PMF.map_comp, commitRecoveryRestriction, Function.comp_def,
    Function.Embedding.coeFn_mk, commitRecoveryLiftHistory_source, commitRecoveryPayoff_lift]
    using projected

/-- Intended copied play never has a public exclusion, at any supported
intermediate history or terminal history. -/
theorem commitRecovery_run_clear [Fintype Player] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (agrees : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (fuel : Nat) (history : setup.commitRecoveryProtocol.History)
    (supported : history ∈ (setup.commitRecoveryModel.runBehavioral target fuel).support) :
    setup.CommitRecoveryClear history.state := by
  rw [← (setup.commitRecoveryRestriction wellFormed).initialized_law source target agrees fuel,
    PMF.support_map] at supported
  obtain ⟨original, _member, rfl⟩ := supported
  exact setup.commitRecoveryLiftHistory_clear wellFormed original

end Vegas.SourceProgram.Setup
