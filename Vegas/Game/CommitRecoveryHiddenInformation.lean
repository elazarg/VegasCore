/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitBlockRecovery
import Vegas.Game.CommitRecoveryRestriction

/-! # Copied policies during an unfinished hidden commitment block -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

private theorem recoveryChoice_cast_val (who : Player)
    {first second : setup.commitRecoveryModel.InfoState who} (same : first = second)
    (choice : setup.commitRecoveryModel.Choice who first) :
    (Eq.mp (congrArg (setup.commitRecoveryModel.Choice who) same) choice).1 = choice.1 := by
  cases same
  rfl

theorem commitRecovery_choiceAt_val (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History)
    (choice : setup.intendedModel.Choice who (setup.intendedModel.infoOf who original.trace)) :
    ((setup.commitRecoveryRestriction wellFormed).choiceAt who original choice).1 =
      CommitRecoveryMove.lift choice.1 := by
  change (Eq.mp (congrArg (setup.commitRecoveryModel.Choice who)
    (setup.commitRecoveryInformation_observed wellFormed who original).symm)
    (setup.commitRecoveryChoice wellFormed who
      (setup.intendedModel.infoOf who original.trace) choice)).1 = _
  exact setup.recoveryChoice_cast_val who
    (setup.commitRecoveryInformation_observed wellFormed who original).symm _

/-- At a represented foreign information value, every supported copied
choice is an actual intended choice with no physical omission marker. -/
theorem copied_recovery_choice_intended (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (observer : Player) (original : setup.intendedProtocol.History)
    (running : ¬ setup.intendedProtocol.terminal original.state)
    (history : setup.commitRecoveryProtocol.History)
    (observed : setup.commitRecoveryModel.infoOf observer history.trace =
      setup.commitRecoveryModel.infoOf observer
        (setup.commitRecoveryLiftHistory wellFormed original).trace)
    (action : Option (CommitRecoveryMove Player L))
    (supported : action ∈ ((target observer
      (setup.commitRecoveryModel.infoOf observer history.trace)).map Subtype.val).support) :
    ∃ choice : setup.intendedModel.Choice observer
        (setup.intendedModel.infoOf observer original.trace),
      CommitRecoveryMove.lift choice.1 = action := by
  have policy := (setup.commitRecoveryRestriction wellFormed).extends_at_history
    source target copies original running observer
  change target observer (setup.commitRecoveryModel.infoOf observer
      (setup.commitRecoveryLiftHistory wellFormed original).trace) = _ at policy
  rw [observed, policy, PMF.map_comp] at supported
  obtain ⟨choice, _member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact ⟨choice, (setup.commitRecovery_choiceAt_val wellFormed observer original choice).symm.trans
    same⟩

/-- Equal complete foreign information and equal realized foreign choices
remain equal after a pair of clear recovery successors with the same foreign
source views. This retains the whole public transcript and own-play recall. -/
theorem commitRecovery_info_extend_eq (observer : Player)
    (first second : setup.commitRecoveryProtocol.History)
    (left right : Player → Option (CommitRecoveryMove Player L))
    (leftLegal : setup.commitRecoveryProtocol.Legal first.state left)
    (rightLegal : setup.commitRecoveryProtocol.Legal second.state right)
    (firstAfter secondAfter : setup.commitRecoveryProtocol.State)
    (leftReached : firstAfter ∈
      (setup.commitRecoveryProtocol.step first.state ⟨left, leftLegal⟩).support)
    (rightReached : secondAfter ∈
      (setup.commitRecoveryProtocol.step second.state ⟨right, rightLegal⟩).support)
    (before : setup.commitRecoveryModel.infoOf observer first.trace =
      setup.commitRecoveryModel.infoOf observer second.trace)
    (sameChoice : left observer = right observer)
    (privateView : setup.commitRecoveryPrivate observer firstAfter =
      setup.commitRecoveryPrivate observer secondAfter)
    (publicView : setup.commitRecoveryPublic firstAfter =
      setup.commitRecoveryPublic secondAfter) :
    setup.commitRecoveryModel.infoOf observer
        (first.trace.extend left leftLegal leftReached) =
      setup.commitRecoveryModel.infoOf observer
        (second.trace.extend right rightLegal rightReached) := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf observer _ =
    setup.commitRecoverySignals.withOwnPlayRecall.infoOf observer _
  rw [InfoSignals.infoOf_extend, InfoSignals.infoOf_extend]
  change setup.commitRecoverySignals.withOwnPlayRecall.pushInfo observer
      (setup.commitRecoveryModel.infoOf observer first.trace) (left observer)
      (setup.commitRecoveryPrivate observer firstAfter) (setup.commitRecoveryPublic firstAfter) =
    setup.commitRecoverySignals.withOwnPlayRecall.pushInfo observer
      (setup.commitRecoveryModel.infoOf observer second.trace) (right observer)
      (setup.commitRecoveryPrivate observer secondAfter) (setup.commitRecoveryPublic secondAfter)
  rw [before, sameChoice, privateView, publicView]

/-- A physical no-miss step inside the current commitment block has a genuine
intended-history counterpart with every foreign full information value equal.
The intended counterpart may replace arbitrary focal accepted bindings. -/
theorem hidden_commit_recovery_step (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player) (current : CommitRecoveryState setup.program)
    (point : SourceProgram.ProtocolState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some current))
    (original : setup.intendedProtocol.Trace (some point))
    (clear : current.excluded = ∅)
    (related : ProtocolState.HiddenBindings who setup.program current.point point)
    (observed : ∀ observer, observer ≠ who →
      setup.commitRecoveryModel.infoOf observer prior =
        setup.commitRecoveryModel.infoOf observer
          (setup.commitRecoveryLiftHistory wellFormed ⟨some point, original⟩).trace)
    (active : ProtocolState.atCommit setup.program current.point = true)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal (some current) joint)
    (foreignSupport : ∀ observer, observer ≠ who → joint observer ∈
      ((target observer (setup.commitRecoveryModel.infoOf observer prior)).map
        Subtype.val).support)
    (focalNoMiss : CommitRecoveryMove.missed (joint who) = false)
    (next : CommitRecoveryState setup.program)
    (reached : some next ∈
      (setup.commitRecoveryProtocol.step (some current) ⟨joint, legal⟩).support) :
    next.excluded = ∅ ∧ ∃ image : setup.intendedProtocol.History,
      ∃ imagePoint : SourceProgram.ProtocolState setup.program, image.state = some imagePoint ∧
        ProtocolState.HiddenBindings who setup.program next.point imagePoint ∧
        ∀ observer, observer ≠ who →
          setup.commitRecoveryModel.infoOf observer (prior.extend joint legal reached) =
            setup.commitRecoveryModel.infoOf observer
              (setup.commitRecoveryLiftHistory wellFormed image).trace := by
  classical
  let originalHistory : setup.intendedProtocol.History := ⟨some point, original⟩
  let actualHistory : setup.commitRecoveryProtocol.History := ⟨some current, prior⟩
  have originalRunning : ¬ setup.intendedProtocol.terminal originalHistory.state := by
    exact fun terminal => legal.1 ((related.control who setup.program _ _).2.mpr terminal)
  have copied (observer : Player) (foreign : observer ≠ who) :
      ∃ choice : setup.intendedModel.Choice observer
          (setup.intendedModel.infoOf observer original),
        CommitRecoveryMove.lift choice.1 = joint observer :=
    setup.copied_recovery_choice_intended wellFormed source target copies observer
      originalHistory originalRunning actualHistory (observed observer foreign)
      (joint observer) (foreignSupport observer foreign)
  have noMiss (observer : Player) : CommitRecoveryMove.missed (joint observer) = false := by
    by_cases own : observer = who
    · subst observer; exact focalNoMiss
    · obtain ⟨choice, same⟩ := copied observer own
      rw [← same, CommitRecoveryMove.missed_lift]
  have nativeReached : next ∈ (current.step joint).support := by
    exact (PMF.mem_support_map_iff _ _ _).mp reached |>.elim
      (fun value => fun ⟨member, equality⟩ => by
        cases Option.some.inj equality
        exact member)
  obtain ⟨nextClear, ordinary⟩ :=
    current.commit_noMiss_support clear active joint noMiss next nativeReached
  have foreignIntended (observer : Player) (foreign : observer ≠ who) :
      ProtocolView.intendedMenu observer setup.program
        (ProtocolState.observe observer setup.program current.point)
        ((joint observer).map (·.action)) := by
    obtain ⟨choice, same⟩ := copied observer foreign
    have offered : ProtocolView.intendedMenu observer setup.program
        (ProtocolState.observe observer setup.program point) choice.1 := by
      have allowed := (setup.intendedModel.menu_adequate observer original _).mp choice.2
      revert allowed
      cases selected : choice.1 <;> exact id
    rw [← same]
    change ProtocolView.intendedMenu observer setup.program
      (ProtocolState.observe observer setup.program current.point)
      (CommitRecoveryMove.underlying (CommitRecoveryMove.lift choice.1))
    rw [CommitRecoveryMove.underlying_lift]
    rw [related.foreign_observe who observer setup.program _ _ foreign]
    exact offered
  obtain ⟨right, same, rightLegal, imagePoint, imageReached, imageRelated⟩ :=
    related.intended_commit active (fun observer => (joint observer).map (·.action))
      foreignIntended next.point ordinary
  have originalLegal : setup.intendedProtocol.Legal (some point) right := by
    refine ⟨originalRunning, ?_⟩
    intro observer
    have offered := rightLegal observer
    cases choice : right observer <;> rw [choice] at offered <;> exact offered
  have imageRealized : some imagePoint ∈
      (setup.intendedProtocol.step (some point) ⟨right, originalLegal⟩).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨imagePoint, imageReached, rfl⟩
  let image : setup.intendedProtocol.History :=
    ⟨some imagePoint, original.extend right originalLegal imageRealized⟩
  refine ⟨nextClear, image, imagePoint, rfl, imageRelated, ?_⟩
  intro observer foreign
  let lifted := setup.commitRecoveryLiftHistory wellFormed originalHistory
  have liftClear := setup.commitRecoveryLiftHistory_clear wellFormed originalHistory
  have actualClear : setup.CommitRecoveryClear (some current) := clear
  have samePrivate : setup.commitRecoveryPrivate observer (some current) =
      setup.commitRecoveryPrivate observer lifted.state := by
    have before := congrArg (fun info : setup.commitRecoveryModel.InfoState observer => info.1.1.1)
      (observed observer foreign)
    simpa only [commitRecoveryModel, InfoSignals.withOwnPlayRecall_infoOf,
      setup.commitRecoverySignals_current] using before
  have samePublic : setup.commitRecoveryPublic (some current) =
      setup.commitRecoveryPublic lifted.state := by
    have before := congrArg (fun info : setup.commitRecoveryModel.InfoState observer => info.1.1.2)
      (observed observer foreign)
    simpa only [commitRecoveryModel, InfoSignals.withOwnPlayRecall_infoOf,
      setup.commitRecoverySignals_current] using before
  have nextViews : setup.protocolObserve observer (some next.point) =
      setup.protocolObserve observer (some imagePoint) :=
    congrArg some (imageRelated.foreign_observe who observer setup.program _ _ foreign)
  have actualNext : some next = setup.commitRecoveryLiftSuccessor (some current)
      actualClear (some next.point) :=
    setup.commitRecovery_clear_step_reconstruct ⟨joint, legal⟩ reached nextClear
  have nextPublic := setup.commitRecoveryLiftSuccessor_public observer
    (some current) lifted.state actualClear liftClear samePrivate samePublic
      (some next.point) (some imagePoint) nextViews
  have nextPrivate : setup.commitRecoveryPrivate observer (some next) =
      setup.commitRecoveryPrivate observer
        (setup.commitRecoveryLiftSuccessor lifted.state liftClear (some imagePoint)) := by
    rw [setup.commitRecoveryPrivate_source, setup.commitRecoveryPrivate_source,
      setup.commitRecoveryLiftSuccessor_source]
    exact nextViews
  have sameOption : joint observer = CommitRecoveryMove.lift (right observer) := by
    obtain ⟨choice, selected⟩ := copied observer foreign
    rw [← same observer foreign]
    rw [← selected]
    change CommitRecoveryMove.lift choice.1 =
      CommitRecoveryMove.lift (CommitRecoveryMove.underlying (CommitRecoveryMove.lift choice.1))
    rw [CommitRecoveryMove.underlying_lift]
  change setup.commitRecoveryModel.infoOf observer (prior.extend joint legal reached) =
    setup.commitRecoveryModel.infoOf observer
      (setup.commitRecoveryLiftHistory wellFormed image).trace
  apply setup.commitRecovery_info_extend_eq observer actualHistory lifted
    joint (fun observer => CommitRecoveryMove.lift (right observer))
    legal _ (some next) _ reached _ (observed observer foreign) sameOption nextPrivate
  rw [actualNext]
  exact nextPublic

end Vegas.SourceProgram.Setup
