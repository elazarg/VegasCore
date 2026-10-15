/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryIntended
import Vegas.Source.CommitRecoveryProjection

/-! # Exact lifting of intended source transitions into recovery -/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryMove

/-- An effective source action with no physical omission. -/
def lift (choice : Option (OwnAction Player L)) : Option (CommitRecoveryMove Player L) :=
  choice.map fun action => ⟨action, false⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem underlying_lift (choice : Option (OwnAction Player L)) :
    underlying (lift choice) = choice := by cases choice <;> rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem missed_lift (choice : Option (OwnAction Player L)) :
    missed (lift choice) = false := by cases choice <;> rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem lift_injective : Function.Injective (lift (Player := Player) (L := L)) := by
  intro first second same
  simpa only [underlying_lift] using congrArg underlying same

end CommitRecoveryMove

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- Install a clear source successor and perform the actual automatic close. -/
def advanceClear (state : CommitRecoveryState program) (clear : state.excluded = ∅)
    (point : ProtocolState program) : CommitRecoveryState program :=
  (state.install (point, ∅) (by simpa only [clear] using (Finset.empty_subset _))).close

@[simp] theorem advanceClear_point (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (point : ProtocolState program) :
    (state.advanceClear clear point).point = point := by
  apply close_point_of_no_new_failure
  simp only [NewFailure, install, Finset.empty_sdiff, Finset.not_nonempty_empty, not_false_eq_true]

@[simp] theorem advanceClear_excluded (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (point : ProtocolState program) :
    (state.advanceClear clear point).excluded = ∅ := by
  rw [advanceClear, close_excluded]
  rfl

@[simp] theorem advanceClear_generation (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (point : ProtocolState program) :
    (state.advanceClear clear point).generation = state.generation := by
  apply close_generation_of_no_new_failure
  simp only [NewFailure, install, Finset.empty_sdiff, Finset.not_nonempty_empty, not_false_eq_true]

/-- This is the full recovery-state law, rather than only its typed marginal. -/
theorem step_lifted_intended (state : CommitRecoveryState program)
    (clear : state.excluded = ∅) (intended : ProtocolState.Intended program state.point)
    (joint : Player → Option (OwnAction Player L))
    (legal : ∀ who, ProtocolView.intendedMenu who program
      (ProtocolState.observe who program state.point) (joint who)) :
    state.step (fun who => CommitRecoveryMove.lift (joint who)) =
      (ProtocolState.step program state.point joint).map (state.advanceClear clear) := by
  let raw := ProtocolState.recoveryStep program state.point state.excluded
    (fun who => CommitRecoveryMove.lift (joint who))
  let keep := fun result (supported : result ∈ raw.support) =>
    ProtocolState.recoveryStep_excluded_monotone program state.point state.excluded
      (fun who => CommitRecoveryMove.lift (joint who)) result supported
  let finish := fun result : ProtocolState program × Finset Player =>
    (state.install result (by simpa only [clear] using (Finset.empty_subset _))).close
  have typed : (fun who => (CommitRecoveryMove.lift (joint who)).map (·.action)) = joint := by
    funext who
    exact CommitRecoveryMove.underlying_lift (joint who)
  have typedWho (who : Player) :
      (CommitRecoveryMove.lift (joint who)).map (·.action) = joint who :=
    CommitRecoveryMove.underlying_lift (joint who)
  have rawLaw : raw = (ProtocolState.step program state.point joint).map
      (fun point => (point, ∅)) := by
    dsimp only [raw]
    rw [clear, ProtocolState.recoveryStep_intended_joint program state.point _ intended
      (fun who => by rw [typedWho]; exact legal who)
      (fun who => CommitRecoveryMove.missed_lift (joint who)),
      typed]
  change (pmfToSubtype raw keep).map (fun result => finish result.1) = _
  rw [map_pmfToSubtype, rawLaw, PMF.map_comp]
  rfl

end CommitRecoveryState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The actual successor checkpoint is determined by a clear recovery state
and its next original source point, including the one private setup draw. -/
def commitRecoveryLiftSuccessor (state : setup.commitRecoveryProtocol.State)
    (clear : setup.CommitRecoveryClear state) (point : setup.ProtocolState) :
    setup.commitRecoveryProtocol.State :=
  match state, point with
  | none, none => none
  | none, some next => some (CommitRecoveryState.atPoint next ∅ 0)
  | some _, none => none
  | some current, some next => some (current.advanceClear clear next)

@[simp] theorem commitRecoveryLiftSuccessor_source
    (state : setup.commitRecoveryProtocol.State) (clear : setup.CommitRecoveryClear state)
    (point : setup.ProtocolState) :
    setup.commitRecoverySourceState
      (setup.commitRecoveryLiftSuccessor state clear point) = point := by
  cases state <;> cases point <;>
    simp only [commitRecoveryLiftSuccessor, commitRecoverySourceState, Option.map_none,
      Option.map_some, CommitRecoveryState.advanceClear_point, CommitRecoveryState.atPoint]

theorem commitRecoveryLiftSuccessor_clear
    (state : setup.commitRecoveryProtocol.State) (clear : setup.CommitRecoveryClear state)
    (point : setup.ProtocolState) :
    setup.CommitRecoveryClear (setup.commitRecoveryLiftSuccessor state clear point) := by
  cases state <;> cases point <;>
    simp only [commitRecoveryLiftSuccessor, CommitRecoveryClear, Option.elim_none,
      Option.elim_some, CommitRecoveryState.advanceClear_excluded, CommitRecoveryState.atPoint]

theorem commitRecovery_lift_legal
    (state : setup.commitRecoveryProtocol.State) (clear : setup.CommitRecoveryClear state)
    (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal (setup.commitRecoverySourceState state) joint) :
    setup.commitRecoveryProtocol.Legal state (fun who => CommitRecoveryMove.lift (joint who)) := by
  refine ⟨?_, ?_⟩
  · cases state <;> exact legal.1
  · intro who
    have offered := legal.2 who
    cases state with
    | none =>
        cases chosen : joint who with
        | none => simp only [CommitRecoveryMove.lift, chosen, Option.map_none]; exact id
        | some action => rw [chosen] at offered; exact offered.1.elim
    | some current =>
        cases chosen : joint who with
        | none =>
            rw [chosen] at offered
            simp only [CommitRecoveryMove.lift, chosen, Option.map_none]
            change ¬ current.Active who
            exact fun acts => offered ((ProtocolState.actor_observe_eq _ _ _).trans acts.1)
        | some action =>
            rw [chosen] at offered
            simp only [CommitRecoveryMove.lift, chosen, Option.map_some]
            refine ⟨⟨(ProtocolState.actor_observe_eq _ _ _).symm.trans offered.1, ?_⟩, ?_⟩
            · simp only [CommitRecoveryClear, Option.elim_some] at clear
              simp only [clear, Finset.notMem_empty, not_false_eq_true]
            · refine ⟨ProtocolView.intendedAvailable_subset who setup.program
                (CommitmentInterface.forfeiture setup.program) _ offered.2, ?_⟩
              dsimp only
              split
              · intro impossible; cases impossible
              · rfl

theorem commitRecovery_lift_step
    (state : setup.commitRecoveryProtocol.State) (clear : setup.CommitRecoveryClear state)
    (intended : (setup.commitRecoverySourceState state).elim True
      (ProtocolState.Intended setup.program))
    (joint : Player → Option (OwnAction Player L))
    (legal : setup.intendedProtocol.Legal (setup.commitRecoverySourceState state) joint) :
    setup.commitRecoveryProtocol.step state
        ⟨(fun who => CommitRecoveryMove.lift (joint who)),
          setup.commitRecovery_lift_legal state clear joint legal⟩ =
      (setup.intendedProtocol.step (setup.commitRecoverySourceState state) ⟨joint, legal⟩).map
        (setup.commitRecoveryLiftSuccessor state clear) := by
  cases state with
  | none =>
      change (setup.initialLaw.map _) = (setup.initialLaw.map _).map _
      rw [PMF.map_comp]
      rfl
  | some current =>
      change ((current.step (fun who => CommitRecoveryMove.lift (joint who))).map some) =
        ((ProtocolState.step setup.program current.point joint).map some).map _
      rw [current.step_lifted_intended clear intended joint (fun who => ?_),
        PMF.map_comp, PMF.map_comp]
      · rfl
      · have offered := legal.2 who
        cases chosen : joint who <;> rw [chosen] at offered <;> exact offered

end Setup
end Vegas.SourceProgram
