/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryExtraChoice
import Vegas.Game.CommitRecoveryDebtPayoff

/-! # Extra source recovery choices have the actual exclusion-floor payoff -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem intendedHistory_transport (history : setup.intendedProtocol.History)
    {point : setup.intendedProtocol.State} (same : history.state = point) :
    (⟨point, Eq.mp (congrArg setup.intendedProtocol.Trace same) history.trace⟩ :
      setup.intendedProtocol.History) = history := by
  rcases history with ⟨state, trace⟩
  dsimp only at same
  cases same
  rfl

omit [Fintype Player] in
theorem extra_commitRecovery_choice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who)
    (choice : setup.commitRecoveryModel.Choice who
      ((setup.commitRecoveryRestriction wellFormed).information who view))
    (extra : choice ∉ Set.range ((setup.commitRecoveryRestriction wellFormed).choice who view))
    (move : CommitRecoveryMove Player L) (selected : choice.1 = some move) :
    move.missing = true ∨ some move.action ∉ setup.intendedMenu who view := by
  by_cases missing : move.missing = true
  · exact Or.inl missing
  · right
    intro intended
    apply extra
    refine ⟨⟨some move.action, intended⟩, Subtype.ext ?_⟩
    change CommitRecoveryMove.lift (some move.action) = choice.1
    rw [selected]
    have clear : move.missing = false := Bool.eq_false_iff.mpr missing
    cases move with
    | mk action omission =>
        change omission = false at clear
        subst omission
        rfl

open Classical in
/-- Every terminal continuation after an extra choice at an embedded intended
site pays the author's actual permanent-exclusion floor. Foreign players are
copied only through the first hidden commitment block, then saved debt survives
arbitrary later target behavior and retries. -/
theorem commitRecovery_deviation_payoff (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : setup.commitRecoveryModel.Choice who
      ((setup.commitRecoveryRestriction wellFormed).site who site).1)
    (extra : action ∉ Set.range ((setup.commitRecoveryRestriction wellFormed).choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    ∀ final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
      setup.commitRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) target who
        ((target who).commit ((setup.commitRecoveryRestriction wellFormed).site who site).1 action))
      ((setup.commitRecoveryRestriction wellFormed).history history.1)).support,
      setup.commitRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  classical
  let restriction := setup.commitRecoveryRestriction wellFormed
  let policies := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature) target who
    ((target who).commit (restriction.site who site).1 action)
  have foreignPolicies (observer : Player) (foreign : observer ≠ who) :
      policies observer = target observer := Profile.update_of_ne _ _ foreign
  have sourceActive := InformationModel.InformationSite.active (M := setup.intendedModel)
    site history
  have active : setup.commitRecoveryProtocol.active (restriction.history history.1).state who :=
    (restriction.active history.1 who).mpr sourceActive
  have running : ¬ setup.commitRecoveryProtocol.terminal
      (restriction.history history.1).state := fun stopped =>
    (setup.not_terminal_of_active (CommitmentInterface.values setup.program) sourceActive)
      ((restriction.terminal history.1).mp stopped)
  intro final supported
  change final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom
    setup.commitRecoveryProtocol_bounded.wellFoundedHistories policies
      (restriction.history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨after, realized, child⟩ := continued
  have marginal : draw.1 ∈
      ((setup.commitRecoveryModel.behavioralJoint policies
        (restriction.history history.1).trace running).map Subtype.val).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
  rw [setup.commitRecoveryModel.behavioralJoint_map_val,
    independentProduct_support_iff] at marginal
  have chosen : draw.1 who = action.1 := by
    have own := marginal who
    have info : setup.commitRecoveryModel.infoOf who (restriction.history history.1).trace =
        (restriction.site who site).1 := (restriction.observed who history.1).trans
          (congrArg (restriction.information who) history.2)
    rw [info] at own
    simpa only [policies, Profile.update_same, InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map, PMF.mem_support_pure_iff] using own
  have foreignSupport (observer : Player) (foreign : observer ≠ who) : draw.1 observer ∈
      ((target observer (setup.commitRecoveryModel.infoOf observer
        (restriction.history history.1).trace)).map Subtype.val).support := by
    rw [← foreignPolicies observer foreign]
    exact marginal observer
  have permitted := draw.2.2 who
  rw [chosen] at permitted
  cases selected : action.1 with
  | none =>
      rw [selected] at permitted
      exact (permitted active).elim
  | some move =>
      have extraMove := setup.extra_commitRecovery_choice wellFormed who site.1 action
        extra move selected
      have originalState : setup.commitRecoverySourceState
          (restriction.history history.1).state = history.1.state :=
        setup.commitRecoveryLiftHistory_source wellFormed history.1
      have clear := setup.commitRecoveryLiftHistory_clear wellFormed history.1
      change setup.CommitRecoveryClear (restriction.history history.1).state at clear
      generalize startEquality : restriction.history history.1 = start at *
      rcases start with ⟨state, prior⟩
      cases state with
      | none => exact active.elim
      | some current =>
          change some current.point = history.1.state at originalState
          let originalTrace : setup.intendedProtocol.Trace (some current.point) :=
            Eq.mp (congrArg setup.intendedProtocol.Trace originalState.symm) history.1.trace
          have originalHistory : (⟨some current.point, originalTrace⟩ :
              setup.intendedProtocol.History) = history.1 := by
            exact setup.intendedHistory_transport history.1 originalState.symm
          have observed (observer : Player) (_foreign : observer ≠ who) :
              setup.commitRecoveryModel.infoOf observer prior =
                setup.commitRecoveryModel.infoOf observer
                  (setup.commitRecoveryLiftHistory wellFormed
                    ⟨some current.point, originalTrace⟩).trace := by
            rw [originalHistory]
            change _ = setup.commitRecoveryModel.infoOf observer
              (restriction.history history.1).trace
            rw [startEquality]
          have extraTyped : move.missing = true ∨ move.action ∉
              ProtocolView.intendedAvailable who setup.program
                (ProtocolState.observe who setup.program current.point) := by
            rcases extraMove with missing | forbidden
            · exact Or.inl missing
            · right
              intro offered
              apply forbidden
              have sourceView := history.2.symm.trans (setup.intended_info who history.1.trace)
              rw [← originalState] at sourceView
              rw [sourceView]
              exact ⟨(ProtocolState.actor_observe_eq _ _ _).trans active.1, offered⟩
          change after ∈ ((current.step draw.1).map some).support at realized
          rw [PMF.support_map] at realized
          obtain ⟨next, member, rfl⟩ := realized
          have realized : some next ∈
              (setup.commitRecoveryProtocol.step (some current) draw).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨next, member, rfl⟩
          have initial := setup.commitRecovery_first_extra_debt wellFormed source target copies
            who current prior originalTrace clear observed draw.1 draw.2 foreignSupport move
              (chosen.trans selected) extraTyped next realized
          have finalDebt := setup.hidden_commit_terminal_debt wellFormed
            setup.commitRecoveryProtocol_bounded.wellFoundedHistories source target policies
              copies who foreignPolicies _ initial final child
          have stopped := setup.commitRecoveryModel.runBehavioralTerminalFrom_support_terminal
            setup.commitRecoveryProtocol_bounded.wellFoundedHistories policies _ final child
          cases stateEq : final.state with
          | none => rw [stateEq] at finalDebt; exact finalDebt.elim
          | some last =>
              have excluded : who ∈ last.excluded := by
                rw [stateEq] at finalDebt
                rcases finalDebt with excluded | debt
                · exact excluded
                · exact setup.commitRecovery_terminal_excluded_of_owesFailure final.trace
                    last stateEq who debt.2 (by
                      simpa only [stateEq, commitRecoveryProtocol, Option.elim_some] using stopped)
              apply setup.commitRecoveryPayoff_of_excluded
              simpa only [stateEq, commitRecoveryPublic] using excluded

end Vegas.SourceProgram.Setup
