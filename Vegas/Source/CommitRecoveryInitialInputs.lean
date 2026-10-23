/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryNoMissRepresentative
import Vegas.Source.PrivateInputsIndependent

/-! # Original private inputs recovered from retained source queries

Actual instruction steps and automatic closes preserve the original entry
cells. The current typed query therefore identifies its owner's original
hidden input tuple even after arbitrary retries and exhausted advances.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace CommitRecoveryState

variable {Γ : SourceCtx Player L} {O : Finset VarId} {program : SourceProgram Player L Γ O}

/-- The real retry and exhausted close preserve the original semantic entry
cells whenever current and saved points retain the same original entry. -/
theorem close_base (state : CommitRecoveryState program)
    (same : ProtocolState.base program state.saved = ProtocolState.base program state.point) :
    ProtocolState.base program state.close.point = ProtocolState.base program state.point ∧
      ProtocolState.base program state.close.saved = ProtocolState.base program state.point := by
  unfold close
  split
  · split
    · split <;>
        simp only [retry, exhausted, atPoint, restored, ProtocolState.base_withHistory,
          ProtocolState.base_automaticCommitBlock, same, and_self]
    · exact ⟨rfl, rfl⟩
  · split
    · exact ⟨rfl, same⟩
    · exact ⟨rfl, rfl⟩

/-- Every actual automatically closed source step retains the same original
entry state in both current and saved points. -/
theorem step_base (state : CommitRecoveryState program) (initial : State L Γ)
    (current : ProtocolState.base program state.point = initial)
    (saved : ProtocolState.base program state.saved = initial)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (next : CommitRecoveryState program) (supported : next ∈ (state.step joint).support) :
    ProtocolState.base program next.point = initial ∧
      ProtocolState.base program next.saved = initial := by
  obtain ⟨raw, rawSupport, rfl⟩ := state.step_raw_result joint next supported
  have rawBase := ProtocolState.base_recoveryStep program state.point state.excluded joint
    raw.1 rawSupport
  have same : ProtocolState.base program (state.install raw.1 raw.2).saved =
      ProtocolState.base program (state.install raw.1 raw.2).point := by
    exact saved.trans (rawBase.trans current).symm
  have closed := (state.install raw.1 raw.2).close_base same
  exact ⟨closed.1.trans (rawBase.trans current), closed.2.trans (rawBase.trans current)⟩

end CommitRecoveryState

namespace ProtocolState

/-- Equal retained typed views identify the owner's observation of all
original entry cells; action-word erasure cannot hide an original input. -/
theorem sourceObserve_base_eq_of_erased_observe_eq (who : Player)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (left right : ProtocolState program)
    (same : ProtocolView.eraseHistory who program (observe who program left) =
      ProtocolView.eraseHistory who program (observe who program right)) :
    sourceObserve who (base program left) = sourceObserve who (base program right) := by
  rw [ProtocolView.eraseHistory_observe, ProtocolView.eraseHistory_observe] at same
  have cells := sourceObserve_base_eq_of_observe_eq who program
    (withHistory program left (fun _ => [])) (withHistory program right (fun _ => [])) same
  simpa only [base_withHistory] using cells

end ProtocolState

omit [IExpr.ResultTypes L] in
/-- The owner's observation includes every original hidden input and initial
commitment of that owner, as one complete tuple. -/
theorem hiddenAgree_of_sourceObserve_eq {Γ : SourceCtx Player L} (who : Player)
    (left right : State L Γ) (same : sourceObserve who left = sourceObserve who right) :
    HiddenAgree who left right := by
  intro name cell member hidden
  cases cell with
  | publicData => cases hidden
  | publication => cases hidden
  | privateInput owner payload =>
      have own : owner = who := Option.some.inj hidden
      subst owner
      have values := congrArg (fun view => view.cells name (.privateInput who payload) member) same
      simp only [sourceObserve_privateInput, ↓reduceIte] at values
      exact Option.some.inj values
  | commitment owner payload =>
      have own : owner = who := Option.some.inj hidden
      subst owner
      have values := congrArg (fun view => view.cells name (.commitment who payload) member) same
      simp only [sourceObserve_commitment, ↓reduceIte] at values
      exact Option.some.inj values

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- An entire genuine source suffix retains its literal original entry
state through every instruction and real automatic close. -/
theorem commitRecovery_base_of_prefix (first : CommitRecoveryState setup.program)
    (prior : setup.commitRecoveryProtocol.Trace (some first))
    (same : ProtocolState.base setup.program first.saved =
      ProtocolState.base setup.program first.point)
    {state : setup.commitRecoveryProtocol.State} (trace : setup.commitRecoveryProtocol.Trace state)
    (retained : TracePrefix prior trace) :
    ∃ current, state = some current ∧
      ProtocolState.base setup.program current.point =
        ProtocolState.base setup.program first.point ∧
      ProtocolState.base setup.program current.saved =
        ProtocolState.base setup.program first.point := by
  induction retained with
  | refl => exact ⟨first, rfl, rfl, same⟩
  | @extend before after earlier kept joint legal supported ih =>
      obtain ⟨current, rfl, currentBase, savedBase⟩ := ih
      obtain ⟨next, nextSupport, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
      obtain ⟨nextBase, nextSaved⟩ := current.step_base _ currentBase savedBase
        joint next nextSupport
      exact ⟨next, rfl, nextBase, nextSaved⟩

private theorem noMissInformation_view (who : Player)
    (information : setup.commitRecoveryModel.InfoState who) :
    (setup.commitRecoveryNoMissInformation who information).1.1.1 = information.1.1.1 := by
  unfold commitRecoveryNoMissInformation
  split
  · exact (setup.commitRecoveryWithAttemptExclusions_controls who _ _ information).1
  · rfl

private theorem current_view (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (setup.commitRecoveryModel.infoOf who trace).1.1.1 = setup.commitRecoveryPrivate who state := by
  change (setup.commitRecoverySignals.withOwnPlayRecall.infoOf who trace).1.1.1 = _
  rw [InfoSignals.withOwnPlayRecall_infoOf]
  exact congrArg Prod.fst (setup.commitRecoverySignals_current who trace)

/-- Equal actual combined source queries retain equal owner observations of
the original entry cells, even when their remembered private words differ. -/
theorem commitRecovery_base_observe_eq_of_query_eq (who : Player)
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.commitRecoveryProtocol.Trace (some left))
    (rightTrace : setup.commitRecoveryProtocol.Trace (some right))
    (same : setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who leftTrace)) =
      setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who rightTrace))) :
    sourceObserve who (ProtocolState.base setup.program left.point) =
      sourceObserve who (ProtocolState.base setup.program right.point) := by
  have views := congrArg (fun info => info.1.1.1) same
  change ((setup.commitRecoveryNoMissInformation who _).1.1.1.map
      (ProtocolView.eraseHistory who setup.program)) =
    ((setup.commitRecoveryNoMissInformation who _).1.1.1.map
      (ProtocolView.eraseHistory who setup.program)) at views
  rw [setup.noMissInformation_view, setup.noMissInformation_view,
    setup.current_view, setup.current_view] at views
  apply ProtocolState.sourceObserve_base_eq_of_erased_observe_eq who setup.program left.point
    right.point
  exact Option.some.inj views

/-- A genuine equal-query fiber has the SAME original hidden owner tuple.
The two literal supported setup prefixes remain part of the original traces;
no independent replacement draw or initial-tuple equality is assumed. -/
theorem commitRecovery_initial_hiddenAgree_of_query_eq (who : Player)
    (leftInputs rightInputs : State L setup.context)
    (leftPrior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig leftInputs)) ∅ 0)))
    (rightPrior : setup.commitRecoveryProtocol.Trace (some (CommitRecoveryState.atPoint
      (ProtocolState.entry setup.program (setup.initialConfig rightInputs)) ∅ 0)))
    (left right : CommitRecoveryState setup.program)
    (leftTrace : setup.commitRecoveryProtocol.Trace (some left))
    (rightTrace : setup.commitRecoveryProtocol.Trace (some right))
    (leftRetained : TracePrefix leftPrior leftTrace)
    (rightRetained : TracePrefix rightPrior rightTrace)
    (same : setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who leftTrace)) =
      setup.commitRecoveryErasedInformation who (setup.commitRecoveryNoMissInformation who
        (setup.commitRecoveryModel.infoOf who rightTrace))) :
    HiddenAgree who leftInputs rightInputs := by
  have leftBase := setup.commitRecovery_base_of_prefix _ leftPrior rfl leftTrace leftRetained
  have rightBase := setup.commitRecovery_base_of_prefix _ rightPrior rfl rightTrace rightRetained
  obtain ⟨leftCurrent, leftEq, leftCells, _⟩ := leftBase
  obtain ⟨rightCurrent, rightEq, rightCells, _⟩ := rightBase
  cases Option.some.inj leftEq
  cases Option.some.inj rightEq
  have equal := setup.commitRecovery_base_observe_eq_of_query_eq who left right
    leftTrace rightTrace same
  rw [leftCells, rightCells] at equal
  simp only [CommitRecoveryState.atPoint, ProtocolState.base_entry] at equal
  exact hiddenAgree_of_sourceObserve_eq who leftInputs rightInputs equal

end Setup
end Vegas.SourceProgram
