/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryRetraction
import Vegas.Source.SetupObservationRecall

/-! # No additional observed information along intended recovery histories -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- The complete retained observation transcript of an intended recovery
history is determined by the observer's original source view. -/
theorem commitRecoveryLiftTrace_observations (wellFormed : setup.WellFormed) (who : Player) :
    ∀ {first second : setup.intendedProtocol.State}
      (firstTrace : setup.intendedProtocol.Trace first)
      (secondTrace : setup.intendedProtocol.Trace second),
      setup.protocolObserve who first = setup.protocolObserve who second →
        setup.commitRecoverySignals.infoOf who
            (setup.commitRecoveryLiftTrace wellFormed firstTrace).1.trace =
          setup.commitRecoverySignals.infoOf who
            (setup.commitRecoveryLiftTrace wellFormed secondTrace).1.trace
  | _, _, .start, .start, _ => rfl
  | _, _, .start, .extend prior joint legal supported, same => by
      have lengths := setup.intendedTrace_length_eq_of_observe who .start
        (prior.extend joint legal supported) same
      simp only [Trace.length] at lengths
      omega
  | _, _, .extend prior joint legal supported, .start, same => by
      have lengths := setup.intendedTrace_length_eq_of_observe who
        (prior.extend joint legal supported) .start same
      simp only [Trace.length] at lengths
      omega
  | firstAfter, secondAfter, .extend firstPrior firstJoint firstLegal firstSupported,
      .extend secondPrior secondJoint secondLegal secondSupported, same => by
      have before := setup.intended_predecessor_observations_eq who firstPrior secondPrior
        firstJoint secondJoint firstLegal secondLegal firstSupported secondSupported same
      have earlier := commitRecoveryLiftTrace_observations wellFormed who
        firstPrior secondPrior before
      let left := setup.commitRecoveryLiftTrace wellFormed firstPrior
      let right := setup.commitRecoveryLiftTrace wellFormed secondPrior
      have current := congrArg Prod.fst earlier
      rw [setup.commitRecoverySignals_current, setup.commitRecoverySignals_current] at current
      have publicView := setup.commitRecoveryLiftSuccessor_public who left.1.state right.1.state
        left.2.2 right.2.2 (congrArg Prod.fst current) (congrArg Prod.snd current)
        firstAfter secondAfter same
      have privateView : setup.commitRecoveryPrivate who
          (setup.commitRecoveryLiftSuccessor left.1.state left.2.2 firstAfter) =
          setup.commitRecoveryPrivate who
            (setup.commitRecoveryLiftSuccessor right.1.state right.2.2 secondAfter) := by
        rw [setup.commitRecoveryPrivate_source, setup.commitRecoveryPrivate_source,
          setup.commitRecoveryLiftSuccessor_source, setup.commitRecoveryLiftSuccessor_source]
        exact same
      change ((setup.commitRecoveryPrivate who
          (setup.commitRecoveryLiftSuccessor left.1.state left.2.2 firstAfter),
        setup.commitRecoveryPublic
          (setup.commitRecoveryLiftSuccessor left.1.state left.2.2 firstAfter)),
        (setup.commitRecoverySignals.infoOf who left.1.trace).1 ::
          (setup.commitRecoverySignals.infoOf who left.1.trace).2) =
        ((setup.commitRecoveryPrivate who
          (setup.commitRecoveryLiftSuccessor right.1.state right.2.2 secondAfter),
        setup.commitRecoveryPublic
          (setup.commitRecoveryLiftSuccessor right.1.state right.2.2 secondAfter)),
        (setup.commitRecoverySignals.infoOf who right.1.trace).1 ::
          (setup.commitRecoverySignals.infoOf who right.1.trace).2)
      rw [privateView, publicView, earlier]

/-- Extend the retained transcript to all source information values. On an
unrealized information value its current private component still carries that
exact source view, so the extension remains injective. -/
def commitRecoveryRetainedInfo (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) : setup.commitRecoverySignals.InfoState who := by
  classical
  exact if witness : ∃ original : setup.intendedProtocol.History,
      setup.intendedModel.infoOf who original.trace = view then
    setup.commitRecoverySignals.infoOf who
      (setup.commitRecoveryLiftHistory wellFormed witness.choose).trace
  else ((view, (∅, 0, 0)), [])

theorem commitRecoveryRetainedInfo_current (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) :
    (setup.commitRecoveryRetainedInfo wellFormed who view).1.1 = view := by
  classical
  unfold commitRecoveryRetainedInfo
  split
  · next witness =>
      rw [setup.commitRecoverySignals_current,
        setup.commitRecoveryLiftHistory_private wellFormed who witness.choose]
      exact witness.choose_spec
  · rfl

theorem commitRecoveryRetainedInfo_injective (wellFormed : setup.WellFormed) (who : Player) :
    Function.Injective (setup.commitRecoveryRetainedInfo wellFormed who) := by
  intro first second same
  simpa only [commitRecoveryRetainedInfo_current] using
    congrArg (fun info : setup.commitRecoverySignals.InfoState who => info.1.1) same

theorem commitRecoveryRetainedInfo_observed (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History) :
    setup.commitRecoverySignals.infoOf who
        (setup.commitRecoveryLiftHistory wellFormed original).trace =
      setup.commitRecoveryRetainedInfo wellFormed who
        (setup.intendedModel.infoOf who original.trace) := by
  classical
  unfold commitRecoveryRetainedInfo
  split
  · next witness =>
      apply setup.commitRecoveryLiftTrace_observations wellFormed who
      simpa only [setup.intended_info] using witness.choose_spec.symm
  · next absent => exact (absent ⟨original, rfl⟩).elim

theorem commitRecoveryRetainedInfo_excluded (wellFormed : setup.WellFormed) (who : Player)
    (view : setup.ProtocolView who) :
    (setup.commitRecoveryRetainedInfo wellFormed who view).1.2.1 = ∅ := by
  classical
  unfold commitRecoveryRetainedInfo
  split
  · next witness =>
      rw [setup.commitRecoverySignals_current]
      have clear := setup.commitRecoveryLiftHistory_clear wellFormed witness.choose
      cases current : (setup.commitRecoveryLiftHistory wellFormed witness.choose).state with
      | none => rfl
      | some current =>
          rw [current] at clear
          exact clear
  · rfl

private theorem intended_ownPlayView (who : Player) {state : setup.intendedProtocol.State}
    (trace : setup.intendedProtocol.Trace state) :
    setup.intendedModel.ownPlay who trace =
      setup.ownPlayView who (setup.protocolObserve who state) := by
  unfold intendedModel
  rw [InformationModel.restrictMenu_ownPlay]
  exact setup.protocol_ownPlay (CommitmentInterface.values setup.program) who
    (restrictAvailable.trace trace)

/-- The source observer already remembers every effective own action and the
view at which it was taken. Lifting merely annotates those records with the
determined recovery observation transcript and a false physical-omission bit. -/
theorem commitRecoveryLiftTrace_ownPlay (wellFormed : setup.WellFormed) (who : Player) :
    ∀ {state : setup.intendedProtocol.State} (trace : setup.intendedProtocol.Trace state),
      setup.commitRecoverySignals.ownPlay who
          (setup.commitRecoveryLiftTrace wellFormed trace).1.trace =
        (setup.intendedModel.ownPlay who trace).map (fun entry =>
          (setup.commitRecoveryRetainedInfo wellFormed who entry.1,
            (⟨entry.2, false⟩ : CommitRecoveryMove Player L)))
  | _, .start => rfl
  | _, .extend prior joint legal supported => by
      simp only [commitRecoveryLiftTrace, InfoSignals.ownPlay_extend]
      rw [commitRecoveryLiftTrace_ownPlay wellFormed who prior]
      have observed := setup.commitRecoveryRetainedInfo_observed wellFormed who ⟨_, prior⟩
      dsimp only [commitRecoveryLiftHistory] at observed
      cases chosen : joint who with
      | none => rfl
      | some action =>
          simp only [CommitRecoveryMove.lift, Option.map_some, List.map_cons]
          rw [observed]

/-- Embedding of the complete recovery information, including both the entire
observed transcript and own-play recall, at every source information value. -/
def commitRecoveryInformation (wellFormed : setup.WellFormed) (who : Player) :
    setup.intendedModel.InfoState who ↪ setup.commitRecoveryModel.InfoState who where
  toFun view := (setup.commitRecoveryRetainedInfo wellFormed who view,
    (setup.ownPlayView who view).map fun entry =>
      (setup.commitRecoveryRetainedInfo wellFormed who entry.1,
        (⟨entry.2, false⟩ : CommitRecoveryMove Player L)))
  inj' := by
    intro first second same
    apply setup.commitRecoveryRetainedInfo_injective wellFormed who
    exact congrArg Prod.fst same

theorem commitRecoveryInformation_observed (wellFormed : setup.WellFormed) (who : Player)
    (original : setup.intendedProtocol.History) :
    setup.commitRecoveryModel.infoOf who
        (setup.commitRecoveryLiftHistory wellFormed original).trace =
      setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace) := by
  change setup.commitRecoverySignals.withOwnPlayRecall.infoOf who _ = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  apply Prod.ext
  · exact setup.commitRecoveryRetainedInfo_observed wellFormed who original
  · change setup.commitRecoverySignals.ownPlay who
        (setup.commitRecoveryLiftTrace wellFormed original.trace).1.trace = _
    rw [setup.commitRecoveryLiftTrace_ownPlay, setup.intended_ownPlayView, setup.intended_info]
    rfl

end Vegas.SourceProgram.Setup
