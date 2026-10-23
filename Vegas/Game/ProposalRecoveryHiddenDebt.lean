/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryRestriction
import Vegas.Game.CommitRecoveryExtraChoice
import Vegas.Game.CommitRecoveryReference
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # The original hidden-debt argument on actual labeled commitment histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))

/-- The only extra evidence needed by the old hidden-debt invariant is the
literal ordinary action lift while the failed commitment block remains open. -/
def ProposalRecoveryHiddenCommitDebt (wellFormed : setup.WellFormed) (who : Player)
    (history : setup.proposalRecoveryProtocol.History) : Prop :=
  setup.HiddenCommitDebt wellFormed who
      ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩ ∧
    setup.proposalRecoveryLiftTrace (fun _ _ => false)
      (setup.proposalRecoveryEraseTrace history.trace) = history.trace

open Classical in
omit [Fintype Player] in
private theorem copied_semantic_support (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (copies : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (oldTarget : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (oldCopies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source oldTarget)
    (observer : Player) (original : setup.intendedProtocol.History)
    (running : ¬ setup.intendedProtocol.terminal original.state)
    (history : setup.proposalRecoveryProtocol.History)
    (clear : setup.CommitRecoveryClear history.state)
    (ordinary : setup.proposalRecoveryLiftTrace (fun _ _ => false)
      (setup.proposalRecoveryEraseTrace history.trace) = history.trace)
    (observed : setup.commitRecoveryModel.infoOf observer
        (setup.proposalRecoveryEraseTrace history.trace) =
      setup.commitRecoveryModel.infoOf observer
        (setup.commitRecoveryLiftHistory wellFormed original).trace)
    (choice : Option (ProposalRecoveryMove Player L))
    (supported : choice ∈ ((target observer
      (setup.proposalRecoveryModel.infoOf observer history.trace)).map Subtype.val).support) :
    choice.map (·.semantic) ∈ ((oldTarget observer (setup.commitRecoveryModel.infoOf observer
      (setup.proposalRecoveryEraseTrace history.trace))).map Subtype.val).support := by
  have same := setup.proposalRecovery_clear_ordinary_information_eq observer
    (setup.proposalRecoveryEraseTrace history.trace)
    (setup.commitRecoveryLiftHistory wellFormed original).trace clear
    (setup.commitRecoveryLiftHistory_clear wellFormed original) observed
  rw [ordinary] at same
  have law := (setup.proposalRecoveryRestriction wellFormed).extends_at_history
    source target copies original running observer
  change target observer (setup.proposalRecoveryModel.infoOf observer
    (setup.proposalRecoveryIntendedLift wellFormed original).trace) = _ at law
  dsimp only [proposalRecoveryIntendedLift] at law
  rw [same, law, PMF.map_comp] at supported
  obtain ⟨actual, supplied, selected⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have oldLaw := (setup.commitRecoveryRestriction wellFormed).extends_at_history
    source oldTarget oldCopies original running observer
  change oldTarget observer (setup.commitRecoveryModel.infoOf observer
    (setup.commitRecoveryLiftHistory wellFormed original).trace) = _ at oldLaw
  rw [observed, oldLaw, PMF.map_comp]
  refine (PMF.mem_support_map_iff _ _ _).mpr ⟨actual, supplied, ?_⟩
  dsimp only [Function.comp_def] at selected ⊢
  rw [setup.commitRecovery_choiceAt_val]
  rw [setup.proposalRecovery_choiceAt_val] at selected
  have own := congrArg (Option.map (·.semantic)) selected
  simp only [ProposalRecoveryMove.lift, Option.map_map, Function.comp_def,
    ProposalRecoveryMove.ordinary_semantic] at own
  change (CommitRecoveryMove.lift actual.val).map id = choice.map (·.semantic) at own
  simpa only [Option.map_id, id_eq] using own

open Classical in
omit [Fintype Player] in
/-- The original first-extra-debt theorem consumes the SAME actual semantic
step. If its debt is still hidden, the actual commitment labels are ordinary
and retain the required enriched counterpart. -/
theorem proposalRecovery_first_extra_debt [Finite Player]
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (copies : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (current : CommitRecoveryState setup.program)
    (prior : setup.proposalRecoveryProtocol.Trace (some current))
    (original : setup.intendedProtocol.Trace (some current.point))
    (clear : current.excluded = ∅)
    (ordinary : setup.proposalRecoveryLiftTrace (fun _ _ => false)
      (setup.proposalRecoveryEraseTrace prior) = prior)
    (observed : ∀ observer, observer ≠ who →
      setup.commitRecoveryModel.infoOf observer (setup.proposalRecoveryEraseTrace prior) =
        setup.commitRecoveryModel.infoOf observer
          (setup.commitRecoveryLiftHistory wellFormed ⟨some current.point, original⟩).trace)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (foreignSupport : ∀ observer, observer ≠ who → joint observer ∈
      ((target observer (setup.proposalRecoveryModel.infoOf observer prior)).map
        Subtype.val).support)
    (move : CommitRecoveryMove Player L)
    (chosen : proposalRecoveryJoint joint who = some move)
    (extra : move.missing = true ∨ move.action ∉
      ProtocolView.intendedAvailable who setup.program
        (ProtocolState.observe who setup.program current.point))
    (next : CommitRecoveryState setup.program)
    (reached : some next ∈
      (setup.proposalRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    setup.CheckpointedDebt who (some next) ∨
      setup.ProposalRecoveryHiddenCommitDebt wellFormed who
        ⟨some next, prior.extend joint legal reached⟩ := by
  classical
  let _ := Fintype.ofFinite Player
  let oldTarget := (setup.commitRecoveryRestriction wellFormed).extendProfile source
    (setup.commitRecoveryReference finite).strategy
  have oldCopies := (setup.commitRecoveryRestriction wellFormed).extendProfile_extends source
    (setup.commitRecoveryReference finite).strategy
  have oldLegal := setup.proposalRecovery_erase_legal joint legal
  have permitted := oldLegal.2 who
  rw [chosen] at permitted
  have intended := setup.intendedState_trace wellFormed original
  change ProtocolState.Intended setup.program current.point at intended
  have raw : next ∈ (current.step (proposalRecoveryJoint joint)).support := by
    obtain ⟨value, supported, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
    cases Option.some.inj same
    exact supported
  rcases current.deviation who clear intended (proposalRecoveryJoint joint) move chosen
      permitted.1.1 permitted.2 extra next raw with excluded | latent
  · exact Or.inl (Or.inl excluded)
  · have oldSupport (observer : Player) (outside : observer ≠ who) :
        proposalRecoveryJoint joint observer ∈
          ((oldTarget observer (setup.commitRecoveryModel.infoOf observer
            (setup.proposalRecoveryEraseTrace prior))).map Subtype.val).support := by
      exact setup.copied_semantic_support wellFormed source target copies oldTarget oldCopies
        observer ⟨some current.point, original⟩ legal.1 ⟨some current, prior⟩ clear ordinary
        (observed observer outside) (joint observer) (foreignSupport observer outside)
    have debt := setup.commitRecovery_first_extra_debt wellFormed source oldTarget oldCopies
      who current (setup.proposalRecoveryEraseTrace prior) original clear observed
      (proposalRecoveryJoint joint) oldLegal oldSupport move chosen extra next reached
    rcases debt with settled | hidden
    · exact Or.inl settled
    · exact Or.inr ⟨hidden, setup.proposalRecovery_ordinary_extend_of_atCommit current prior
        ordinary latent.2.1 joint legal reached⟩

open Classical in
/-- Replay the SAME supported semantic joint through the already checked
old debt-progress theorem. The focal reference is used only to certify
support of this legal step, not to replace actual continuation probabilities. -/
theorem proposalRecovery_debt_progress (finite : setup.program.FiniteBindingTypes)
    (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target policies : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (copies : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player)
    (foreignPolicies : ∀ observer, observer ≠ who → policies observer = target observer)
    (history : setup.proposalRecoveryProtocol.History)
    (owed : setup.CheckpointedDebt who history.state ∨
      setup.ProposalRecoveryHiddenCommitDebt wellFormed who history)
    (running : ¬ setup.proposalRecoveryProtocol.terminal history.state)
    (draw : {joint // setup.proposalRecoveryProtocol.Legal history.state joint})
    (drawn : draw ∈ (setup.proposalRecoveryModel.behavioralJoint policies history.trace
      running).support)
    (after : setup.proposalRecoveryProtocol.State)
    (reached : after ∈ (setup.proposalRecoveryProtocol.step history.state draw).support) :
    setup.CheckpointedDebt who after ∨
      setup.ProposalRecoveryHiddenCommitDebt wellFormed who (history.extend draw.2 reached) := by
  classical
  rcases owed with settled | unsettled
  · left
    rcases history with ⟨before, prior⟩
    cases before with
    | none => exact settled.elim
    | some current =>
        obtain ⟨next, raw, equality⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
        rw [← equality]
        exact current.step_preserves_excluded_or_owesFailure who
          settled (proposalRecoveryJoint draw.val) next raw
  · obtain ⟨hidden, ordinary⟩ := unsettled
    obtain ⟨current, point, original, state, clear, live, committing, related, observed⟩ := hidden
    have actualState : history.state = some current := state
    let oldHistory : setup.commitRecoveryProtocol.History :=
      ⟨history.state, setup.proposalRecoveryEraseTrace history.trace⟩
    let oldTarget := (setup.commitRecoveryRestriction wellFormed).extendProfile source
      (setup.commitRecoveryReference finite).strategy
    have oldCopies := (setup.commitRecoveryRestriction wellFormed).extendProfile_extends source
      (setup.commitRecoveryReference finite).strategy
    let oldPolicies := Profile.update (sig := setup.commitRecoveryModel.behavioralSignature)
      oldTarget who ((setup.commitRecoveryReference finite).strategy who)
    have oldForeign (observer : Player) (outside : observer ≠ who) :
        oldPolicies observer = oldTarget observer := Profile.update_of_ne _ _ outside
    have originalRunning : ¬ setup.intendedProtocol.terminal (some point) := by
      intro terminal
      apply running
      rw [state]
      exact (related.control who setup.program _ _).2.mpr terminal
    let semantic : {joint // setup.commitRecoveryProtocol.Legal oldHistory.state joint} :=
      ⟨proposalRecoveryJoint draw.val, setup.proposalRecovery_erase_legal draw.val draw.property⟩
    have marginal : draw.val ∈ ((setup.proposalRecoveryModel.behavioralJoint policies
        history.trace running).map Subtype.val).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
    rw [setup.proposalRecoveryModel.behavioralJoint_map_val,
      independentProduct_support_iff] at marginal
    have oldDraw : semantic ∈ (setup.commitRecoveryModel.behavioralJoint oldPolicies
        oldHistory.trace running).support := by
      have rawSupport : semantic.val ∈ ((setup.commitRecoveryModel.behavioralJoint oldPolicies
          oldHistory.trace running).map Subtype.val).support := by
        rw [setup.commitRecoveryModel.behavioralJoint_map_val,
          independentProduct_support_iff]
        intro observer
        by_cases own : observer = who
        · subst observer
          dsimp only [oldPolicies]
          rw [Profile.update_same]
          let choice : setup.commitRecoveryModel.Choice who
              (setup.commitRecoveryModel.infoOf who oldHistory.trace) :=
            ⟨semantic.val who, (setup.commitRecoveryModel.menu_adequate who oldHistory.trace _).mpr
              (by cases selected : semantic.val who <;>
                simpa only [LegalOption, selected] using semantic.property.2 who)⟩
          exact (PMF.mem_support_map_iff _ _ _).mpr
            ⟨choice, setup.commitRecoveryReference_fullSupport finite who _ choice, rfl⟩
        · rw [oldForeign observer own]
          apply setup.copied_semantic_support wellFormed source target copies oldTarget oldCopies
            observer ⟨some point, original⟩ originalRunning history
            (by simpa only [CommitRecoveryClear, actualState, Option.elim_some] using clear)
            ordinary (observed observer own) (draw.val observer)
          rw [← foreignPolicies observer own]
          exact marginal observer
      obtain ⟨actual, offered, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp rawSupport
      have same : actual = semantic := Subtype.ext equal
      rwa [same] at offered
    have result := setup.commitRecovery_debt_progress wellFormed source oldTarget oldPolicies
      oldCopies who oldForeign oldHistory (Or.inr ⟨current, point, original, state, clear,
        live, committing, related, observed⟩) running semantic oldDraw after reached
    rcases result with settled | hiddenNext
    · exact Or.inl settled
    · right
      refine ⟨hiddenNext, ?_⟩
      rcases history with ⟨before, prior⟩
      dsimp only at state
      subst before
      exact setup.proposalRecovery_ordinary_extend_of_atCommit current prior ordinary
        committing draw.val draw.property reached

open Classical in
/-- The existing stopped history-invariant theorem carries the actual debt
to termination. It uses the same supported steps and arbitrary focal policy;
the focal reference in the one-step proof does not enter either run law. -/
theorem proposalRecovery_hidden_commit_terminal_debt
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target policies : ∀ who, setup.proposalRecoveryModel.BehavioralPolicy who)
    (copies : (setup.proposalRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player)
    (foreignPolicies : ∀ observer, observer ≠ who → policies observer = target observer)
    (history : setup.proposalRecoveryProtocol.History)
    (initial : setup.CheckpointedDebt who history.state ∨
      setup.ProposalRecoveryHiddenCommitDebt wellFormed who history)
    (final : setup.proposalRecoveryProtocol.History)
    (supported : final ∈ (setup.proposalRecoveryModel.runBehavioralTerminalFrom
      setup.proposalRecoveryProtocol_bounded.wellFoundedHistories policies history).support) :
    setup.CheckpointedDebt who final.state := by
  classical
  let certificate := setup.proposalRecoveryProtocol_bounded.wellFoundedHistories
  let stopped := fun current : setup.proposalRecoveryProtocol.History =>
    setup.proposalRecoveryProtocol.terminal current.state
  let stopLaw := setup.proposalRecoveryModel.runBehavioralUntil certificate policies stopped history
  have stopTerminal (ending : setup.proposalRecoveryProtocol.History)
      (member : ending ∈ stopLaw.support) : setup.proposalRecoveryProtocol.terminal
        ending.state := by
    exact (setup.proposalRecoveryModel.mem_support_runBehavioralUntil certificate policies
      stopped history ending member).elim id id
  have terminalLaw : setup.proposalRecoveryModel.runBehavioralTerminalFrom certificate policies
      history = stopLaw := by
    rw [setup.proposalRecoveryModel.runBehavioralTerminalFrom_eq_bind_runBehavioralUntil
      certificate policies stopped]
    trans stopLaw.bind PMF.pure
    · apply bind_congr_on_support
      intro ending member
      exact setup.proposalRecoveryProtocol.randomizedBackwardLaw_of_terminal
        (stopTerminal ending member)
    · exact PMF.bind_pure _
  have held := setup.proposalRecoveryModel.runBehavioralUntil_support_history_closed
    certificate policies stopped
    (fun current => setup.CheckpointedDebt who current.state ∨
      setup.ProposalRecoveryHiddenCommitDebt wellFormed who current) (by
        intro current _going running owed next member
        rw [setup.proposalRecoveryModel.runBehavioralFrom_succ_of_not_terminal policies 0 running,
          PMF.mem_support_bind_iff] at member
        obtain ⟨draw, drawn, stepped⟩ := member
        rw [PMF.mem_support_bindOnSupport_iff] at stepped
        obtain ⟨after, reached, child⟩ := stepped
        change next ∈ (PMF.pure (current.extend draw.property reached)).support at child
        rw [PMF.mem_support_pure_iff] at child
        subst next
        exact setup.proposalRecovery_debt_progress finite wellFormed source target policies
          copies who foreignPolicies current owed running draw drawn after reached)
    history initial final (by rwa [terminalLaw] at supported)
  rcases held with settled | hidden
  · exact settled
  · obtain ⟨⟨current, _point, _original, state, _clear, _live, committing, _related,
        _observed⟩, _ordinary⟩ := hidden
    have terminal := setup.proposalRecoveryModel.runBehavioralTerminalFrom_support_terminal
      certificate policies history final supported
    rw [state] at terminal
    have zero := (ProtocolState.remaining_zero_iff_terminal setup.program current.point).mpr
      terminal
    have positive := ProtocolState.commitEnd_lt_remaining setup.program current.point committing
    omega

end Vegas.SourceProgram.Setup
