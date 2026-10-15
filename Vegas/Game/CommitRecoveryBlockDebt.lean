/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryHiddenInformation
import Vegas.Source.CommitRecoveryDebt
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

private theorem terminal_not_atCommit : ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (point : SourceProgram.ProtocolState program),
    ProtocolState.terminal program point → ProtocolState.atCommit program point = false
  | _, _, .ret _, _, _ => rfl
  | _, _, .sample _ _ _ next, point, terminal => by
      cases point with
      | inl _ => exact terminal.elim
      | inr point => exact terminal_not_atCommit next point terminal
  | _, _, .commit _ _ _ _ next, point, terminal => by
      cases point with
      | inl _ => exact terminal.elim
      | inr point => exact terminal_not_atCommit next point terminal
  | _, _, .reveal _ _ _ _ _ _ next, point, terminal => by
      cases point with
      | inl _ => exact terminal.elim
      | inr point => exact terminal_not_atCommit next point terminal

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

/-- Terminal support after a hidden extra binding has either already excluded
its owner or retained the debt in both saved and live semantics. Foreign
policies need stay copied only while the first bad commitment block is open. -/
theorem hidden_commit_terminal_debt [Fintype Player] (wellFormed : setup.WellFormed)
    (certificate : setup.commitRecoveryProtocol.WellFoundedHistories)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target policies : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (who : Player)
    (foreignPolicies : ∀ observer, observer ≠ who → policies observer = target observer)
    (history : setup.commitRecoveryProtocol.History)
    (initial : setup.CheckpointedDebt who history.state ∨
      setup.HiddenCommitDebt wellFormed who history)
    (final : setup.commitRecoveryProtocol.History)
    (supported : final ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate
      policies history).support) : setup.CheckpointedDebt who final.state := by
  have persists : ∀ start : setup.commitRecoveryProtocol.History,
      setup.CheckpointedDebt who start.state ∨ setup.HiddenCommitDebt wellFormed who start →
      ∀ last ∈ (setup.commitRecoveryModel.runBehavioralTerminalFrom certificate policies
        start).support,
        setup.CheckpointedDebt who last.state ∨ setup.HiddenCommitDebt wellFormed who last := by
    intro start
    induction start using certificate.induction with
    | _ start ih =>
        intro initial last member
        by_cases terminal : setup.commitRecoveryProtocol.terminal start.state
        · rw [InformationModel.runBehavioralTerminalFrom,
            setup.commitRecoveryProtocol.randomizedBackwardLaw_of_terminal terminal,
            PMF.mem_support_pure_iff] at member
          subst last
          exact initial
        · rw [InformationModel.runBehavioralTerminalFrom_of_not_terminal _ _ _ terminal,
            PMF.support_bind] at member
          obtain ⟨draw, drawn, continued⟩ := Set.mem_iUnion₂.mp member
          rw [PMF.mem_support_bindOnSupport_iff] at continued
          obtain ⟨after, realized, child⟩ := continued
          exact ih (start.extend draw.2 realized) ⟨draw.1, draw.2, realized⟩
            (setup.commitRecovery_debt_progress wellFormed source target policies copies who
              foreignPolicies start initial terminal draw drawn after realized) last child
  rcases persists history initial final supported with settled | unsettled
  · exact settled
  · obtain ⟨current, _point, _original, state, _clear, _owed, active, _related, _observed⟩ :=
      unsettled
    have terminal := setup.commitRecoveryModel.runBehavioralTerminalFrom_support_terminal
      certificate policies history final supported
    rw [state] at terminal
    have noCommit := terminal_not_atCommit setup.program current.point terminal
    rw [noCommit] at active
    cases active

end Vegas.SourceProgram.Setup
