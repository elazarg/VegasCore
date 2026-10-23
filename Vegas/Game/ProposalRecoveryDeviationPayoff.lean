/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ProposalRecoveryHiddenDebt
import Vegas.Game.ExclusionMoveExtension
import Vegas.Source.ProposalRecoveryFlags
import Vegas.Game.CommitRecoveryPayoff
import Vegas.Game.ProposalRecoveryPayoff
import Vegas.Source.CommitRecoveryFailureCoverage

/-! # First extra intended-site choices secure the actual enriched recovery floor -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
theorem extra_proposalRecovery_choice (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.intendedModel.InfoState who)
    (choice : setup.proposalRecoveryModel.Choice who
      ((setup.proposalRecoveryRestriction wellFormed).information who view))
    (extra : choice ∉ Set.range ((setup.proposalRecoveryRestriction wellFormed).choice who view))
    (move : ProposalRecoveryMove Player L) (selected : choice.1 = some move) :
    move.semantic.missing = true ∨ some move.semantic.action ∉ setup.intendedMenu who view := by
  by_cases missing : move.semantic.missing = true
  · exact Or.inl missing
  · right
    intro intended
    have notFailure := setup.intendedMenu_not_failure who view (some move.semantic.action)
      intended move.semantic.action rfl
    have valid : move.Valid := by
      have legal := ((setup.proposalRecoveryMenu_semantic who _ _).mp choice.property).2
      simpa only [selected, Option.elim_some] using legal
    have absent : move.proposed = false := by
      apply Bool.eq_false_iff.mpr
      intro proposed
      obtain ⟨owner, name, revealing⟩ := valid proposed
      apply notFailure
      rw [revealing]
      trivial
    apply extra
    refine ⟨⟨some move.semantic.action, intended⟩, Subtype.ext ?_⟩
    change ProposalRecoveryMove.lift (some move.semantic.action) = choice.val
    rw [selected]
    have notMissing : move.semantic.missing = false := Bool.eq_false_iff.mpr missing
    cases move with
    | mk semantic proposed =>
        cases semantic with
        | mk action omission => cases absent; cases notMissing; rfl

omit [Fintype Player] in
private theorem intended_history_transport (history : setup.intendedProtocol.History)
    {point : setup.intendedProtocol.State} (same : history.state = point) :
    (⟨point, Eq.mp (congrArg setup.intendedProtocol.Trace same) history.trace⟩ :
      setup.intendedProtocol.History) = history := by
  rcases history with ⟨state, trace⟩
  dsimp only at same
  cases same
  rfl

open Classical in
/-- The current extra proposal action is not made harmless by an arbitrary
free continuation: the first hidden block has copied opponents and its debt
is saved before any later free source behavior or retry can rescue it. -/
theorem proposalRecovery_deviation_payoff
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (excludedPayoff : Player → ℝ)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (copies : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (site : setup.intendedModel.InformationSite who)
    (action : setup.proposalRecoveryModel.Choice who
      ((setup.proposalRecoveryRestriction wellFormed).site who site).1)
    (extra : action ∉ Set.range ((setup.proposalRecoveryRestriction wellFormed).choice who site.1))
    (history : setup.intendedModel.InformationHistory who site.1) :
    ∀ final ∈ (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
      (Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) target who
        ((target who).commit ((setup.proposalRecoveryRestriction wellFormed).site who site).1
          action))
      ((setup.proposalRecoveryRestriction wellFormed).history history.1)).support,
      setup.proposalRecoveryPayoff utility excludedPayoff who final = excludedPayoff who := by
  classical
  let restriction := setup.proposalRecoveryRestriction wellFormed
  let policies := Profile.update (sig := setup.proposalRecoveryModel.behavioralSignature) target who
    ((target who).commit (restriction.site who site).1 action)
  have foreignPolicies (observer : Player) (foreign : observer ≠ who) :
      policies observer = target observer := Profile.update_of_ne _ _ foreign
  have sourceActive := InformationModel.InformationSite.active setup.intendedModel site history
  have active : setup.proposalRecoveryProtocol.active (restriction.history history.1).state who :=
    (restriction.active history.1 who).mpr sourceActive
  have running : ¬ setup.proposalRecoveryProtocol.terminal
      (restriction.history history.1).state := fun stopped =>
    (setup.not_terminal_of_active (CommitmentInterface.values setup.program) sourceActive)
      ((restriction.terminal history.1).mp stopped)
  intro final supported
  change final ∈ (setup.proposalRecoveryModel.runBehavioralTerminalFrom
    setup.proposalRecoveryProtocol_bounded.wellFoundedHistories policies
      (restriction.history history.1)).support at supported
  rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ running,
    PMF.support_bind] at supported
  obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp supported
  rw [PMF.mem_support_bindOnSupport_iff] at continued
  obtain ⟨after, realized, child⟩ := continued
  have marginal : draw.val ∈ ((setup.proposalRecoveryModel.behavioralJoint policies
      (restriction.history history.1).trace running).map Subtype.val).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
  rw [setup.proposalRecoveryModel.behavioralJoint_map_val,
    independentProduct_support_iff] at marginal
  have chosen : draw.val who = action.val := by
    have own := marginal who
    have info := (restriction.observed who history.1).trans
      (congrArg (restriction.information who) history.property)
    rw [info] at own
    simpa only [policies, Profile.update_same, InformationModel.ActionRestriction.site_val,
      InformationModel.BehavioralPolicy.commit_self,
      PMF.pure_map, PMF.mem_support_pure_iff] using own
  have foreignSupport (observer : Player) (outside : observer ≠ who) : draw.val observer ∈
      ((target observer (setup.proposalRecoveryModel.infoOf observer
        (restriction.history history.1).trace)).map Subtype.val).support := by
    rw [← foreignPolicies observer outside]
    exact marginal observer
  have permitted := draw.property.2 who
  rw [chosen] at permitted
  cases selected : action.val with
  | none => rw [selected] at permitted; exact (permitted active).elim
  | some move =>
      have extraMove := setup.extra_proposalRecovery_choice wellFormed who site.1 action
        extra move selected
      have originalState : setup.commitRecoverySourceState
          (restriction.history history.1).state = history.1.state :=
        setup.commitRecoveryLiftHistory_source wellFormed history.1
      have clear := setup.commitRecoveryLiftHistory_clear wellFormed history.1
      change setup.CommitRecoveryClear (restriction.history history.1).state at clear
      have ordinary : setup.proposalRecoveryLiftTrace (fun _ _ => false)
          (setup.proposalRecoveryEraseTrace (restriction.history history.1).trace) =
            (restriction.history history.1).trace := by
        change setup.proposalRecoveryLiftTrace (fun _ _ => false)
          (setup.proposalRecoveryEraseTrace (setup.proposalRecoveryLiftTrace
            (fun _ _ => false) (setup.commitRecoveryLiftHistory wellFormed history.1).trace)) = _
        rw [setup.proposalRecoveryEraseTrace_lift]
        rfl
      have erasedHistory : (⟨(restriction.history history.1).state,
          setup.proposalRecoveryEraseTrace (restriction.history history.1).trace⟩ :
          setup.commitRecoveryProtocol.History) =
        setup.commitRecoveryLiftHistory wellFormed history.1 := by
        change (⟨_, setup.proposalRecoveryEraseTrace
          (setup.proposalRecoveryLiftTrace (fun _ _ => false)
            (setup.commitRecoveryLiftHistory wellFormed history.1).trace)⟩ :
              setup.commitRecoveryProtocol.History) = _
        rw [setup.proposalRecoveryEraseTrace_lift]
      generalize startEq : restriction.history history.1 = start at *
      rcases start with ⟨state, prior⟩
      cases state with
      | none => exact active.elim
      | some current =>
          change some current.point = history.1.state at originalState
          let originalTrace : setup.intendedProtocol.Trace (some current.point) :=
            Eq.mp (congrArg setup.intendedProtocol.Trace originalState.symm) history.1.trace
          have originalHistory : (⟨some current.point, originalTrace⟩ :
              setup.intendedProtocol.History) = history.1 :=
            setup.intended_history_transport history.1 originalState.symm
          have observed (observer : Player) (_outside : observer ≠ who) :
              setup.commitRecoveryModel.infoOf observer (setup.proposalRecoveryEraseTrace prior) =
                setup.commitRecoveryModel.infoOf observer
                  (setup.commitRecoveryLiftHistory wellFormed
                    ⟨some current.point, originalTrace⟩).trace := by
            rw [originalHistory]
            exact congrArg (fun original : setup.commitRecoveryProtocol.History =>
              setup.commitRecoveryModel.infoOf observer original.trace) erasedHistory
          have extraTyped : move.semantic.missing = true ∨ move.semantic.action ∉
              ProtocolView.intendedAvailable who setup.program
                (ProtocolState.observe who setup.program current.point) := by
            rcases extraMove with missing | forbidden
            · exact Or.inl missing
            · right
              intro offered
              apply forbidden
              have view := history.property.symm.trans (setup.intended_info who history.1.trace)
              rw [← originalState] at view
              rw [view]
              exact ⟨(ProtocolState.actor_observe_eq _ _ _).trans active.1, offered⟩
          obtain ⟨next, raw, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp realized
          subst after
          have realized : some next ∈
              (setup.proposalRecoveryProtocol.step (some current) draw).support :=
            (PMF.mem_support_map_iff _ _ _).mpr ⟨next, raw, rfl⟩
          have initial := setup.proposalRecovery_first_extra_debt finite wellFormed source target
            copies who current prior originalTrace clear ordinary observed draw.val draw.property
            foreignSupport move.semantic (by
              simp only [proposalRecoveryJoint, chosen, selected, Option.map_some])
            extraTyped next realized
          have finalDebt := setup.proposalRecovery_hidden_commit_terminal_debt finite wellFormed
            source target policies copies who foreignPolicies _ initial final child
          have stopped := setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
            setup.proposalRecoveryProtocol_bounded.wellFoundedHistories policies _ final child
          cases stateEq : final.state with
          | none => rw [stateEq] at finalDebt; exact finalDebt.elim
          | some last =>
              have excluded : who ∈ last.excluded := by
                rw [stateEq] at finalDebt
                rcases finalDebt with excluded | debt
                · exact excluded
                · exact setup.commitRecovery_terminal_excluded_of_owesFailure
                    (setup.proposalRecoveryEraseTrace final.trace) last stateEq who debt.2
                    (by simpa only [stateEq, proposalRecoveryProtocol,
                      commitRecoveryProtocol, Option.elim_some] using stopped)
              exact setup.commitRecoveryPayoff_of_excluded utility excludedPayoff who
                ⟨final.state, setup.proposalRecoveryEraseTrace final.trace⟩
                  (by simpa only [stateEq, commitRecoveryPublic] using excluded)

end Vegas.SourceProgram.Setup
