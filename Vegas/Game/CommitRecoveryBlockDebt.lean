/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CommitRecoveryHiddenInformation
import Vegas.Source.CommitRecoveryFrontier
import GameTheory.Protocol.BehavioralTerminal

/-! # Checkpointing latent debt before arbitrary later recovery resets -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

def CheckpointedDebt (who : Player) : setup.commitRecoveryProtocol.State → Prop
  | none => False
  | some current => who ∈ current.excluded ∨
      (ProtocolState.OwesFailure who setup.program current.saved ∧
        ProtocolState.OwesFailure who setup.program current.point)

/-- Debt not yet saved belongs to the current hidden commitment block. The
witness is a genuine intended history, retaining every foreign information value. -/
def HiddenCommitDebt (wellFormed : setup.WellFormed) (who : Player)
    (history : setup.commitRecoveryProtocol.History) : Prop :=
  ∃ current : CommitRecoveryState setup.program,
    ∃ point : SourceProgram.ProtocolState setup.program,
      ∃ original : setup.intendedProtocol.Trace (some point),
        history.state = some current ∧ current.excluded = ∅ ∧
          ProtocolState.OwesFailure who setup.program current.point ∧
          ProtocolState.atCommit setup.program current.point = true ∧
          ProtocolState.HiddenBindings who setup.program current.point point ∧
          ∀ observer, observer ≠ who →
            setup.commitRecoveryModel.infoOf observer history.trace =
              setup.commitRecoveryModel.infoOf observer
                (setup.commitRecoveryLiftHistory wellFormed ⟨some point, original⟩).trace

/-- A supported copied-policy step either retains the hidden intended
counterpart, excludes the focal owner, or saves its latent debt at block closure. -/
theorem commitRecovery_debt_progress [Fintype Player] (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target policies : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player)
    (foreignPolicies : ∀ observer, observer ≠ who → policies observer = target observer)
    (history : setup.commitRecoveryProtocol.History)
    (owed : setup.CheckpointedDebt who history.state ∨
      setup.HiddenCommitDebt wellFormed who history)
    (running : ¬ setup.commitRecoveryProtocol.terminal history.state)
    (draw : {joint // setup.commitRecoveryProtocol.Legal history.state joint})
    (drawn : draw ∈ (setup.commitRecoveryModel.behavioralJoint policies history.trace
      running).support)
    (after : setup.commitRecoveryProtocol.State)
    (reached : after ∈ (setup.commitRecoveryProtocol.step history.state draw).support) :
    setup.CheckpointedDebt who after ∨
      setup.HiddenCommitDebt wellFormed who (history.extend draw.2 reached) := by
  classical
  rcases history with ⟨state, prior⟩
  rcases owed with settled | unsettled
  · cases state with
    | none => exact settled.elim
    | some current =>
        change after ∈ ((current.step draw.1).map some).support at reached
        rw [PMF.support_map] at reached
        obtain ⟨next, member, rfl⟩ := reached
        exact Or.inl (current.step_preserves_excluded_or_owesFailure who settled
          draw.1 next member)
  · obtain ⟨current, point, original, stateEq, clear, live, active, related, observed⟩ := unsettled
    dsimp only at stateEq
    subst state
    change after ∈ ((current.step draw.1).map some).support at reached
    rw [PMF.support_map] at reached
    obtain ⟨next, member, rfl⟩ := reached
    have realized : some next ∈
        (setup.commitRecoveryProtocol.step (some current) draw).support :=
      (PMF.mem_support_map_iff _ _ _).mpr ⟨next, member, rfl⟩
    by_cases missing : CommitRecoveryMove.missed (draw.1 who) = true
    · have acting : ProtocolState.actor setup.program current.point = some who := by
        have offered := draw.2.2 who
        cases selected : draw.1 who with
        | none => simp only [selected, CommitRecoveryMove.missed, Option.elim_none] at missing
                  cases missing
        | some move => rw [selected] at offered; exact offered.1.1
      exact Or.inl (Or.inl (current.missed_excludes who draw.1 active acting missing next member))
    · have noMiss : CommitRecoveryMove.missed (draw.1 who) = false :=
        Bool.eq_false_iff.mpr missing
      have jointSupport : draw.1 ∈
          ((setup.commitRecoveryModel.behavioralJoint policies prior running).map
            Subtype.val).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨draw, drawn, rfl⟩
      rw [setup.commitRecoveryModel.behavioralJoint_map_val,
        independentProduct_support_iff] at jointSupport
      have foreignSupport (observer : Player) (foreign : observer ≠ who) : draw.1 observer ∈
          ((target observer (setup.commitRecoveryModel.infoOf observer prior)).map
            Subtype.val).support := by
        rw [← foreignPolicies observer foreign]
        exact jointSupport observer
      obtain ⟨nextClear, image, imagePoint, imageState, imageRelated, nextObserved⟩ :=
        setup.hidden_commit_recovery_step wellFormed source target copies who current point
          prior original clear related observed active draw.1 draw.2 foreignSupport noMiss
          next realized
      have sourceStep := current.clear_step_source clear draw.1 next member nextClear
      have nextOwed := ProtocolState.owesFailure_step who setup.program current.point
        (fun observer => (draw.1 observer).map
          (fun move : CommitRecoveryMove Player L => move.action)) next.point live sourceStep
      by_cases nextCommit : ProtocolState.atCommit setup.program next.point = true
      · right
        rcases image with ⟨imageStateValue, imageTrace⟩
        dsimp only at imageState
        subst imageStateValue
        exact ⟨next, imagePoint, imageTrace, rfl, nextClear, nextOwed, nextCommit,
          imageRelated, nextObserved⟩
      · left
        have notCommit : ProtocolState.atCommit setup.program next.point = false :=
          Bool.eq_false_iff.mpr nextCommit
        have frontier := setup.commitRecovery_blockFrontier (prior.extend draw.1 draw.2 realized)
        have saved : next.saved = next.point :=
          frontier.saved_eq_point_of_not_atCommit notCommit
        exact Or.inr ⟨saved.symm ▸ nextOwed, nextOwed⟩

end Vegas.SourceProgram.Setup
