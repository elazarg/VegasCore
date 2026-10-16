/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.CommitRecoveryAttemptReset
import Vegas.Source.CommitRecoveryErasure

/-! # Public source chronology is independent of the observer

Public typed fields and source controls are the same observations for every
owner, although their original private source observations remain distinct.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace Config

omit [IExpr.ResultTypes L] in
/-- Equality of the public part of a typed configuration view transfers to
every observer; each original private field is discarded by this projection. -/
theorem public_view_eq_for_observer {Γ : SourceCtx Player L} (focal observer : Player)
    (first second : Config Player L Γ)
    (same : ((first.view focal).1.publicOnly, ([] : List (OwnAction Player L))) =
      ((second.view focal).1.publicOnly, [])) :
    ((first.view observer).1.publicOnly, ([] : List (OwnAction Player L))) =
      ((second.view observer).1.publicOnly, []) := by
  apply Prod.ext
  · apply congrArg SourceObservation.mk
    funext name cell member
    have fields := congrArg (fun view => view.1.cells name cell member) same
    cases cell with
    | publicData => exact fields
    | publication => exact fields
    | privateInput => rfl
    | commitment => rfl
  · rfl

end Config

namespace ProtocolState

/-- Equal actual public source views remain equal at every observer, including
their exact structural source cursor. -/
theorem public_observe_eq_for_observer (focal observer : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (first second : ProtocolState program),
      ProtocolView.publicOnly focal program (observe focal program first) =
        ProtocolView.publicOnly focal program (observe focal program second) →
      ProtocolView.publicOnly observer program (observe observer program first) =
        ProtocolView.publicOnly observer program (observe observer program second)
  | _, _, .ret _, first, second, same =>
      Config.public_view_eq_for_observer focal observer first second same
  | _, _, .sample _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Sum.inl (Config.public_view_eq_for_observer focal observer _ _
          (Sum.inl.inj same))
      · cases same
      · cases same
      · exact congrArg Sum.inr (public_observe_eq_for_observer focal observer next _ _
          (Sum.inr.inj same))
  | _, _, .commit _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Sum.inl (Config.public_view_eq_for_observer focal observer _ _
          (Sum.inl.inj same))
      · cases same
      · cases same
      · exact congrArg Sum.inr (public_observe_eq_for_observer focal observer next _ _
          (Sum.inr.inj same))
  | _, _, .reveal _ _ _ _ _ _ next, first, second, same => by
      cases first <;> cases second
      · exact congrArg Sum.inl (Config.public_view_eq_for_observer focal observer _ _
          (Sum.inl.inj same))
      · cases same
      · cases same
      · exact congrArg Sum.inr (public_observe_eq_for_observer focal observer next _ _
          (Sum.inr.inj same))

end ProtocolState

namespace Setup

variable (setup : Setup (Player := Player) (L := L))

/-- The actual public signal at any source state has the same equality
relation for every observer, without a private-view hypothesis. -/
theorem attemptPublicSignal_eq_for_observer (focal observer : Player)
    (first second : setup.commitRecoveryProtocol.State)
    (same : setup.attemptPublicSignal focal first = setup.attemptPublicSignal focal second) :
    setup.attemptPublicSignal observer first = setup.attemptPublicSignal observer second := by
  apply Prod.ext
  · have views := congrArg Prod.fst same
    cases first <;> cases second
    · rfl
    · cases views
    · cases views
    · exact congrArg some (ProtocolState.public_observe_eq_for_observer focal observer
        setup.program _ _ (Option.some.inj views))
  · have controls := congrArg Prod.snd same
    exact controls

private theorem recall_extend (who : Player) {state target : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal state joint)
    (supported : target ∈ (setup.commitRecoveryProtocol.step state ⟨joint, legal⟩).support) :
    setup.attemptPublicRecall who (trace.extend joint legal supported) =
      setup.attemptPublicSignal who target :: setup.attemptPublicRecall who trace := by
  rw [attemptPublicRecall, InfoSignals.infoOf_extend]
  rfl

private theorem recall_ne_nil (who : Player) {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    setup.attemptPublicRecall who trace ≠ [] := by
  intro impossible
  simp only [attemptPublicRecall, List.map_cons] at impossible
  cases impossible

/-- Equality of the complete genuine public source record for one observer
gives equality for every owner across all phases, retries and exhaustion. -/
theorem attemptPublicRecall_eq_for_observer (focal observer : Player)
    {first second : setup.commitRecoveryProtocol.State}
    (left : setup.commitRecoveryProtocol.Trace first)
    (right : setup.commitRecoveryProtocol.Trace second)
    (same : setup.attemptPublicRecall focal left = setup.attemptPublicRecall focal right) :
    setup.attemptPublicRecall observer left = setup.attemptPublicRecall observer right := by
  induction left generalizing second with
  | start =>
      cases right with
      | start => rfl
      | extend earlier joint legal supported =>
          rw [setup.recall_extend] at same
          have tails := congrArg List.tail same
          exact ((setup.recall_ne_nil focal earlier) tails.symm).elim
  | @extend source target earlier joint legal supported ih =>
      cases right with
      | start =>
          rw [setup.recall_extend] at same
          have tails := congrArg List.tail same
          exact ((setup.recall_ne_nil focal earlier) tails).elim
      | @extend rightSource rightTarget rightEarlier rightJoint rightLegal rightSupport =>
          rw [setup.recall_extend, setup.recall_extend] at same ⊢
          have pair := List.cons.inj same
          exact congrArg₂ List.cons
            (setup.attemptPublicSignal_eq_for_observer focal observer _ _ pair.1)
            (ih rightEarlier pair.2)

end Setup
end Vegas.SourceProgram
