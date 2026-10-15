/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryClear

/-! # Actual clear source-recovery histories project to source histories -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

theorem clear_before (state : CommitRecoveryState program)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) (clear : next.excluded = ∅) :
    state.excluded = ∅ := by
  apply Finset.subset_empty.mp
  rw [← clear]
  exact state.step_excluded_monotone joint next supported

theorem source_menu_of_clear (state : CommitRecoveryState program) (clear : state.excluded = ∅)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : IsLegalJoint state.Active state.available joint) (who : Player) :
    ProtocolView.menu who program (CommitmentInterface.forfeiture program)
      (ProtocolState.observe who program state.point) ((joint who).map (·.action)) := by
  have offered := legal who
  cases chosen : joint who with
  | none =>
      rw [chosen] at offered
      change ProtocolView.actor who program (ProtocolState.observe who program state.point) ≠
        some who
      intro acts
      apply offered
      refine ⟨(ProtocolState.actor_observe_eq _ _ _).symm.trans acts, ?_⟩
      simp only [clear, Finset.notMem_empty, not_false_eq_true]
  | some move =>
      rw [chosen] at offered
      exact ⟨(ProtocolState.actor_observe_eq _ _ _).trans offered.1.1, offered.2.1⟩

theorem clear_step_source (state : CommitRecoveryState program) (clear : state.excluded = ∅)
    (joint : Player → Option (CommitRecoveryMove Player L)) (next : CommitRecoveryState program)
    (supported : next ∈ (state.step joint).support) (nextClear : next.excluded = ∅) :
    next.point ∈ (ProtocolState.step program state.point
      (fun who => (joint who).map (·.action))).support := by
  obtain ⟨result, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have rawMember : result.1 ∈
      (ProtocolState.recoveryStep program state.point state.excluded joint).support := by
    rw [← map_val_pmfToSubtype
      (ProtocolState.recoveryStep program state.point state.excluded joint)
      (fun result supported => ProtocolState.recoveryStep_excluded_monotone program state.point
        state.excluded joint result supported)]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result, member, rfl⟩
  have resultClear : result.1.2 = ∅ := by
    simpa only [close_excluded, install] using nextClear
  have noFailure : ¬ (state.install result.1 result.2).NewFailure := by
    simp only [NewFailure, install, resultClear, Finset.empty_sdiff,
      Finset.not_nonempty_empty, not_false_eq_true]
  rw [close_point_of_no_new_failure _ noFailure]
  have sourceLaw : (ProtocolState.recoveryStep program state.point state.excluded joint).map
      Prod.fst = ProtocolState.step program state.point
        (fun who => (joint who).map (·.action)) := by
    rw [clear]
    exact ProtocolState.recoveryStep_empty_point program state.point joint
  rw [← sourceLaw]
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨result.1, rawMember, rfl⟩

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

def commitRecoverySourceState (state : setup.commitRecoveryProtocol.State) :
    setup.ProtocolState := state.map (·.point)

def CommitRecoveryClear (state : setup.commitRecoveryProtocol.State) : Prop :=
  state.elim True (fun current => current.excluded = ∅)

theorem commitRecoveryClear_before
    {before after : setup.commitRecoveryProtocol.State}
    (draw : {joint // setup.commitRecoveryProtocol.Legal before joint})
    (supported : after ∈ (setup.commitRecoveryProtocol.step before draw).support)
    (clear : setup.CommitRecoveryClear after) : setup.CommitRecoveryClear before := by
  cases before with
  | none => trivial
  | some previous =>
      obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact previous.clear_before draw.1 next member clear

theorem commitRecovery_source_legal
    {state : setup.commitRecoveryProtocol.State}
    (clear : setup.CommitRecoveryClear state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint) :
    (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).Legal
      (setup.commitRecoverySourceState state) (fun who => (joint who).map (·.action)) := by
  refine ⟨?_, ?_⟩
  · cases state <;> exact legal.1
  · intro who
    cases state with
    | none =>
        have offered := legal.2 who
        cases chosen : joint who with
        | none =>
            simp only [chosen, Option.map_none]
            exact id
        | some move => rw [chosen] at offered; exact offered.1.elim
    | some current =>
        have offered := current.source_menu_of_clear clear joint legal.2 who
        cases chosen : (joint who).map (·.action) <;>
          simpa only [ProtocolView.menu, chosen, executionProtocol, commitRecoverySourceState,
            protocolObserve, Option.map_some, Option.elim_some] using offered

theorem commitRecovery_source_step
    {before after : setup.commitRecoveryProtocol.State}
    (draw : {joint // setup.commitRecoveryProtocol.Legal before joint})
    (supported : after ∈ (setup.commitRecoveryProtocol.step before draw).support)
    (clear : setup.CommitRecoveryClear after) :
    setup.commitRecoverySourceState after ∈
      (setup.protocolStep (setup.commitRecoverySourceState before)
        (fun who => (draw.1 who).map (·.action))).support := by
  cases before with
  | none =>
      obtain ⟨inputs, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨inputs, member, rfl⟩
  | some previous =>
      obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      have beforeClear := previous.clear_before draw.1 next member clear
      exact (PMF.mem_support_map_iff _ _ _).mpr
        ⟨next.point, previous.clear_step_source beforeClear draw.1 next member clear, rfl⟩

/-- Every actual recovery history with no exclusion has an actual source
history with the same typed point and every effective owned source action. -/
def commitRecoveryClearTrace : ∀ {state : setup.commitRecoveryProtocol.State}
    (_trace : setup.commitRecoveryProtocol.Trace state), setup.CommitRecoveryClear state →
      (setup.executionProtocol (CommitmentInterface.forfeiture setup.program)).Trace
        (setup.commitRecoverySourceState state)
  | _, .start, _ => .start
  | _, .extend prior joint legal supported, clear =>
      let earlier := setup.commitRecoveryClear_before ⟨joint, legal⟩ supported clear
      let sourceLegal := setup.commitRecovery_source_legal earlier joint legal
      (commitRecoveryClearTrace prior earlier).extend
        (fun who => CommitRecoveryMove.underlying (joint who)) sourceLegal
        (setup.commitRecovery_source_step ⟨joint, legal⟩ supported clear)

theorem commitRecoveryClearTrace_length : ∀ {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) (clear : setup.CommitRecoveryClear state),
    (setup.commitRecoveryClearTrace trace clear).length = trace.length
  | _, .start, _ => rfl
  | _, .extend prior _ _ _, _ => by
      simp only [commitRecoveryClearTrace, Trace.length, commitRecoveryClearTrace_length prior]

theorem commitRecoveryClearTrace_observe (who : Player)
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (clear : setup.CommitRecoveryClear state) :
    (setup.informationModel (CommitmentInterface.forfeiture setup.program)).infoOf who
      (setup.commitRecoveryClearTrace trace clear) = setup.commitRecoveryPrivate who state := by
  change (setup.protocolSignals (CommitmentInterface.forfeiture setup.program)).infoOf who
    (setup.commitRecoveryClearTrace trace clear) = _
  rw [setup.protocol_info]
  cases state <;> rfl

end Setup
end Vegas.SourceProgram
